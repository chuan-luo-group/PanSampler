#include <clipp.h>
#include <fmt/core.h>
#include <fmt/format.h>
#include <fmt/ranges.h>
#include <z3++.h>
#include <algorithm>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <list>
#include <magic_enum.hpp>
#include <mutex>
#include <regex>
#include <thread>
#include <unordered_set>
#include <vector>
#include "bitvector.h"

// #include <dbg.h>

template <typename Fn>
void z3_visit(z3::expr e, Fn &&fn) {
    static_assert(sizeof(z3::expr) == 24);
    static_assert(std::is_invocable_v<Fn, z3::expr>);
    if constexpr (std::is_convertible_v<std::invoke_result_t<Fn, z3::expr>, bool>) {
        if (!static_cast<bool>(std::invoke(fn, e))) return;
    } else {
        std::invoke(fn, e);
    }
    for (uint i = 0; i < e.num_args(); i++) {
        z3_visit(e.arg(i), fn);
    }
}

struct expr_wrapper {
    expr_wrapper(z3::expr e) : e_{std::move(e)} {}
    operator z3::expr() const & { return e_; }
    operator z3::expr() && { return std::move(e_); }
    operator z3::expr &() & { return e_; }
    operator z3::expr const &() const & { return e_; }

    z3::expr *operator->() { return &e_; }
    z3::expr const *operator->() const { return &e_; }

    friend bool operator==(expr_wrapper const &e1, expr_wrapper const &e2) noexcept {
        return z3::eq(e1, e2);
    }

    friend bool operator!=(expr_wrapper const &e1, expr_wrapper const &e2) noexcept {
        return !(e1 == e2);
    }

 private:
    z3::expr e_;
};

template <>
struct std::hash<expr_wrapper> {
    auto operator()(expr_wrapper const &e) const noexcept { return e->hash(); }
};

using fmt_string_join_view = decltype(fmt::join(std::vector<std::string>(), "\n"));
template <>
struct fmt::formatter<z3::expr_vector> : fmt::formatter<fmt_string_join_view> {
    template <class Context>
    auto format(const z3::expr_vector &vec, Context &ctx) const -> decltype(ctx.out()) {
        std::vector<std::string> result;
        result.reserve(vec.size());
        std::transform(vec.begin(), vec.end(), std::back_inserter(result),
                       std::bind(&z3::expr::to_string, std::placeholders::_1));
        return fmt::formatter<fmt_string_join_view>::format(fmt::join(result, "\n"), ctx);
    }
};

template <>
struct fmt::formatter<z3::expr> : fmt::formatter<std::string> {
    template <class Context>
    auto format(const z3::expr &e, Context &ctx) const -> decltype(ctx.out()) {
        return fmt::formatter<std::string>::format(e.to_string(), ctx);
    }
};

struct assertion_error : std::runtime_error {
    using std::runtime_error::runtime_error;
};

#define eassert(cond)                                                                       \
    (static_cast<bool>(cond)                                                                \
         ? void(0)                                                                          \
         : throw assertion_error(fmt::format("{}:{}: {}: Assertion `{}` failed.", __FILE__, \
                                             __LINE__, __PRETTY_FUNCTION__, #cond)))

#define eassert_eq(actual, expect)                                                              \
    ((actual) == (expect) ? void(0)                                                             \
                          : throw assertion_error(fmt::format(                                  \
                                "{}:{}: {}: Assertion `{} == {}` failed ({} vs {}).", __FILE__, \
                                __LINE__, __PRETTY_FUNCTION__, #actual, #expect, actual, expect)))

#define eassert_ne(actual, expect)                                                                 \
    ((actual) != (expect) ? void(0)                                                                \
                          : throw assertion_error(fmt::format(                                     \
                                "{}:{}: {}: Assertion `{} != {}` failed (actual = {}).", __FILE__, \
                                __LINE__, __PRETTY_FUNCTION__, #actual, #expect, actual)))

inline std::string parse_define_fun(std::string_view str) {
    while (isspace(str.front())) str = str.substr(1);
    while (isspace(str.back())) str = str.substr(0, str.size() - 1);
    if (str.front() == '(' && str.back() == ')') str = str.substr(1, str.size() - 2);
    std::vector<std::string_view> parts;
    parts.reserve(5);
    while (!str.empty()) {
        if (isspace(str.front())) {
            str = str.substr(1);
            continue;
        }
        if (str.front() == '(') {
            auto end = str.find(')');
            eassert(end != std::string_view::npos);
            parts.push_back(str.substr(0, end + 1));
            str = str.substr(end + 1);
        } else {
            auto end = str.find(' ');
            if (end == std::string_view::npos) {
                parts.push_back(str);
                break;
            }
            parts.push_back(str.substr(0, end));
            str = str.substr(end + 1);
        }
    }
    eassert_eq(parts.size(), 5);
    if (parts[1].front() == '|' && parts[1].back() == '|')
        parts[1] = parts[1].substr(1, parts[1].size() - 2);
    if (parts[2] == "()") {
        return fmt::format("(assert (= |{}| {}))", parts[1], parts[4]);
    } else {
        throw std::runtime_error("error: function with arguments are not supported currently!");
    }
}

class Coverage {
    z3::check_result check_sat(z3::model &m) {
        for (auto e : assertions) {
            auto r = m.eval(e);
            assert(r.is_bool());
            if (r.is_false())
                return z3::check_result::unsat;
            else if (r.is_true())
                continue;
            else
                return z3::check_result::unknown;
        }
        return z3::check_result::sat;
    }

    void solve_and_calculate(z3::model &m, size_t id) {
        auto res = check_sat(m);
        output << fmt::format("{}: {}\n", id, magic_enum::enum_name(res));
        if (res != z3::sat) {
            throw std::runtime_error(
                fmt::format("error on {}: {}", id, magic_enum::enum_name(res)));
        }
        for (auto it = terms.begin(); it != terms.end();) {
            // model completion is extremely slow sometimes, but I don't know why.
            auto e = m.eval(std::get<0>(*it));
            auto idx = std::get<1>(*it);
            auto &covered = std::get<2>(*it);
            if (e.get_sort().is_fpa()) {
                if (m.eval(e.mk_is_nan()).bool_value() == Z3_L_TRUE) {
                    auto size_of_e = e.get_sort().fpa_ebits() + e.get_sort().fpa_sbits();
                    if (size_of_e == 32) {
                        e = ctx.bv_val(uint32_t(0x7fc00000), 32);
                    } else if (size_of_e == 64) {
                        e = ctx.bv_val(uint64_t(0x7ff8000000000000), 64);
                    } else {
                        throw std::runtime_error(
                            fmt::format("unsupported fpa size: {}", size_of_e));
                    }
                } else {
                    e = z3::expr(ctx, Z3_mk_fpa_to_ieee_bv(ctx, e));
                    e = m.eval(e);
                }
            }
            if (e.is_bool()) {
                auto bool_value = e.bool_value();
                if (bool_value == Z3_L_TRUE) {
                    if (!result[idx]) covered++;
                    result[idx] = true;
                } else if (bool_value == Z3_L_FALSE) {
                    if (!result[idx + 1]) covered++;
                    result[idx + 1] = true;
                } else {
                    throw std::runtime_error(fmt::format("bool value of `{}` is undef.", e));
                }
                if (covered == 2) {
                    it = terms.erase(it);
                } else {
                    ++it;
                }
            } else if (e.is_bv()) {
                auto bv_size = e.get_sort().bv_size();
                for (uint i = 0; i < bv_size; i++) {
                    auto v = m.eval(e.extract(i, i));
                    if (!v.is_numeral()) {
                        throw std::runtime_error(fmt::format("value of `{}` is not numeral.", e));
                    }
                    if (v.get_numeral_uint()) {
                        if (!result[idx]) covered++;
                        result[idx] = true;
                    } else {
                        if (!result[idx + 1]) covered++;
                        result[idx + 1] = true;
                    }
                    idx += 2;
                }
                if (covered == bv_size * 2) {
                    it = terms.erase(it);
                } else {
                    ++it;
                }
            } else {
                __builtin_unreachable();
            }
        }
        output << fmt::format("covered: {}\n", result.count_ones());
    }

    void parse_method_sample_file() {
        std::ifstream fsamples(samples_file);
        std::string input;
        z3::model m(ctx);
        size_t sample_id = 0;
        bool getline_mod = false, disable_solve_last = false;
        while (getline_mod ? std::getline(fsamples, input) : fsamples >> input) {
            if (input.empty()) continue;
            if (input == "(") {
                ++sample_id;
                getline_mod = true;
            } else if (input == ")") {
                solve_and_calculate(m, sample_id);
                m = z3::model(ctx);
                disable_solve_last = true;
                getline_mod = false;
                if (sample_id == max_samples) break;
            } else if (input == "Sample" || input.back() == ':') {
                if (input == "Sample") fsamples >> input;
                if (sample_id != 0) {
                    solve_and_calculate(m, sample_id);
                    m = z3::model(ctx);
                    if (sample_id == max_samples) {
                        disable_solve_last = true;
                        break;
                    }
                }
                sample_id++;
            } else if (getline_mod) {
                auto assertion = parse_define_fun(input);
                try {
                    auto es = pc.parse_string(assertion.c_str());
                    eassert(es.size() == 1);
                    model_add(m, es[0]);
                } catch (z3::exception const &e) {
                    output << fmt::format("? error while parsing {} (parsed from {}): {}\n",
                                          assertion, input, e.msg());
                }
            } else {
                std::string value;
                if (!(fsamples >> value)) break;
                eassert_eq(value, "=");
                std::getline(fsamples, value);
                while (fsamples.peek() == ' ' || fsamples.peek() == '(') {
                    std::string tmp;
                    std::getline(fsamples, tmp);
                    value += std::move(tmp);
                }
                auto index =
                    std::find_if(value.begin(), value.end(), [](char ch) { return !isspace(ch); });
                if (value[0] == '!') throw assertion_error("value starts with `!' is deprecated");
                value.erase(value.begin(), index);
                if (value == "null") continue;
                // work around #1: 0 as false and 1 as true (note: bv0 and bv1 not change)
                if (value == "0")
                    value = "false";
                else if (value == "1")
                    value = "true";
                // work around #2: too many parentheses in Array sort
                const auto pat1 = std::regex(R"(\(\(Array \((.*?)\) \((.*?)\)\)\))");
                value = std::regex_replace(value, pat1, "(Array ($1) ($2))");
                // work around #3: lambda with multiply arguments
                const std::string_view pat2 = ") (lambda (";
                size_t count_pat2 = 0, pos_pat2 = value.npos;
                while ((pos_pat2 = value.rfind(pat2, pos_pat2)) != value.npos) {
                    ++count_pat2;
                    value.replace(pos_pat2, pat2.size(), " ");
                }
                value.resize(value.size() - count_pat2);
                // work around #4: store as const array
                const auto pat3 = std::regex(
                    fmt::format(R"(\b\|?{}\|?\b)",
                                input.front() == '|' ? input.substr(1, input.size() - 2) : input));
                if (std::regex_search(value, pat3)) {
                    auto var =
                        pc.parse_string(fmt::format("(assert (= {0} {0}))", input).c_str())[0].arg(
                            0);
                    auto sort = var.get_sort();
                    auto zero = ctx.bv_val(0, sort.array_range().bv_size());
                    value = std::regex_replace(
                        value, pat3, fmt::format("((as const {}) {})", sort.to_string(), zero));
                }
                // work around #5: add `||` to disambigours
                if (input[0] != '|') input = '|' + input + '|';

                auto assertion = fmt::format("(assert (= {} {}))", input, value);
                try {
                    auto es = pc.parse_string(assertion.c_str());
                    eassert(es.size() == 1);
                    model_add(m, es[0]);
                } catch (z3::exception const &e) {
                    output << fmt::format("? while paring ({} = {}): {}", input, value, e.msg());
                }
            }
        }
        if (sample_id != 0 && !disable_solve_last) solve_and_calculate(m, sample_id);
        output << fmt::format("number of samples parsed: {}\n", sample_id);
    }

    /// for jfs
    void parse_method_sample_dir() {
        if (max_samples == 0) {
            auto begin = std::filesystem::directory_iterator(samples_file);
            auto end = std::filesystem::directory_iterator();
            max_samples = std::distance(begin, end);
        }
        for (size_t sample_id = 1; sample_id <= max_samples; ++sample_id) {
            auto filename =
                std::filesystem::path(samples_file).append(fmt::format("model-{}.smt2", sample_id));
            std::ifstream fsamples(filename);
            if (!fsamples) continue;
            z3::model m(ctx);
            try {
                auto es = ctx.parse_file(filename.c_str());
                for (auto e : es) model_add(m, e);
            } catch (z3::exception const &e) {
                output << fmt::format("? error while parsing {}\n", filename.c_str());
                throw;
            }
            solve_and_calculate(m, sample_id);
        }
    }

    void parse_method() {
        if (!std::filesystem::exists(samples_file)) {
            throw std::runtime_error(fmt::format("samples file {} not found!", samples_file));
        }
        if (std::filesystem::is_directory(samples_file)) {
            parse_method_sample_dir();
        } else {
            parse_method_sample_file();
        }
    }

    void model_add_func(z3::model &m, z3::func_decl x, z3::expr y) {
        std::vector<std::pair<z3::expr_vector, z3::expr>> entries;
        while (y.decl().decl_kind() == Z3_OP_ITE) {
            auto cond = y.arg(0);
            z3::expr_vector ev{ctx};
            ev.resize(x.arity());
            const auto dfs_cond = [&](auto &&self, z3::expr e) -> void {
                if (e.is_and()) {
                    for (auto arg : e.args()) self(self, arg);
                    return;
                }
                assert(e.is_eq());
                auto arg = e.arg(0);
                auto value = e.arg(1);
                /// var index is in reverse order.
                auto idx = x.arity() - Z3_get_index_value(ctx, arg) - 1;
                assert(x.domain(idx).sort_kind() == value.get_sort().sort_kind());
                ev.set(idx, value);
            };
            dfs_cond(dfs_cond, cond);
            entries.emplace_back(ev, y.arg(1));
            y = y.arg(2);
        }
        z3::expr else_value = y;
        auto interp = m.add_func_interp(x, else_value);
        for (auto &[k, v] : entries) interp.add_entry(k, v);
    }

    void model_add(z3::model &m, z3::expr e) {
        if (e.is_and()) {
            for (auto child : e.args()) model_add(m, child);
            return;
        }
        eassert(e.is_eq());
        auto arg0 = e.arg(0).decl();
        auto arg1 = e.arg(1);
        // dbg(e, arg0, arg1);
        if (arg0.decl_kind() == Z3_OP_AS_ARRAY) {
            z3::func_decl true_decl{ctx, Z3_get_decl_func_decl_parameter(ctx, arg0, 0)};
            ctx.check_error();
            assert(true_decl);
            assert(arg1.is_lambda());
            model_add_func(m, true_decl, arg1.body());
        } else {
            m.add_const_interp(arg0, arg1);
        }
    }

    void init_terms() {
        // fmt::println("{}", assertions);
        std::unordered_set<expr_wrapper> unique_nodes;
        size_t idx = 0;
        for (auto e : assertions) {
            z3_visit(e, [&idx, &unique_nodes, this](z3::expr e) {
                if (e.num_args() == 0) {
                    // Do NOT calculate leaf nodes.
                    return false;
                }
                if (!unique_nodes.insert(e).second) return false;
                if (e.is_bool()) {
                    terms.emplace_back(e, idx, 0);
                    idx += 2;
                } else if (e.is_bv()) {
                    terms.emplace_back(e, idx, 0);
                    idx += e.get_sort().bv_size() * 2;
                } else if (e.is_fpa()) {
                    auto size_of_e = e.get_sort().fpa_ebits() + e.get_sort().fpa_sbits();
                    terms.emplace_back(e, idx, 0);
                    idx += size_of_e * 2;
                }
                return true;
            });
        }
        result.resize(idx);
    }

    Coverage(const char *smt_file, const char *samples_file, size_t max_samples,
             std::ostream &output)
        : ctx(),
          pc(ctx),
          assertions(ctx),
          max_samples{max_samples},
          samples_file{samples_file},
          output(output) {
        std::ifstream fin(smt_file);
        std::string str, buf;
        while (std::getline(fin, buf)) str += buf, str.push_back('\n');
        assertions = pc.parse_string(str.c_str());
        init_terms();
        // std::cerr << "total ast bits: " << result.size() << std::endl;
    }

 public:
    static void run(std::ostream &out, const char *smt_file, const char *samples_file,
                    int max_samples) noexcept;

 private:
    z3::context ctx;
    z3::parser_context pc;
    z3::expr_vector assertions;

    size_t max_samples;
    const char *samples_file;
    std::list<std::tuple<const z3::expr, const size_t, size_t>> terms;

    bitvector result;
    std::ostream &output;
};

/// mutex
std::mutex mutex;
/// bits covered by at least one method
bitvector allcovered;

void Coverage::run(std::ostream &out, const char *smt_file, const char *samples_file,
                   int max_samples) noexcept {
    std::ostringstream buffer;
    buffer << fmt::format("@{}\n", samples_file);
    try {
        Coverage coverage(smt_file, samples_file, max_samples, buffer);
        struct Defer {
            ~Defer() {
                std::unique_lock lock{mutex};
                assert(allcovered.empty() || allcovered.size() == coverage.result.size());
                allcovered.resize(coverage.result.size());
                allcovered |= coverage.result;
            }
            Coverage &coverage;
        } defer{coverage};
        coverage.parse_method();
    } catch (z3::exception &e) {
        buffer << fmt::format("#{}: {}\n", samples_file, e.msg());
    } catch (std::exception &e) {
        buffer << fmt::format("#{}: {}\n", samples_file, e.what());
    } catch (...) {
        buffer << fmt::format("#{}: unknown error\n", samples_file);
    }
    buffer << fmt::format("end {}.\n", samples_file);
    std::unique_lock lock{mutex};
    out << std::move(buffer).str() << std::endl;
}

struct Argument {
    bool human_readable = false;
    bool cov_append = true;
    bool allow_unknown = false;
    bool overwrite = false;
    size_t max_samples = 0;
    std::string smt_file, dump_file, result_file;
    std::vector<std::string> sample_files;
};

auto read_result_file(std::string const &result_file) {
    std::ifstream is(result_file);
    std::vector<std::pair<std::string, std::string>> result;
    for (std::string line; std::getline(is, line);) {
        if (line.empty()) continue;
        if (line == "done.") break;
        if (line[0] != '@') throw std::runtime_error("expect `@`, but got: " + line);
        auto name = line.substr(1), raw = line + '\n';
        auto end_symbol = fmt::format("end {}.", name);
        while (line != end_symbol) {
            if (!std::getline(is, line)) throw std::runtime_error("broken result file");
            raw += line + '\n';
        }
        result.emplace_back(std::move(name), std::move(raw));
    }
    return result;
}

int main_(Argument &arg) {
    if (arg.max_samples < 0) {
        fmt::print("max_samples must be positive!\n");
        exit(-1);
    }
    if (!arg.dump_file.empty()) {
        std::ifstream dumps{arg.dump_file};
        if (dumps) try {
                if (arg.human_readable) {
                    dumps >> allcovered;
                } else {
                    allcovered.read_bin(dumps);
                }
            } catch (std::exception &e) {
                fmt::print("error while reading {}: {}\n", arg.dump_file, e.what());
                allcovered = bitvector();
                arg.cov_append = false;
            }
    }
    std::ofstream fresult;
    std::unordered_set<std::string> sample_file_set(arg.sample_files.begin(),
                                                    arg.sample_files.end());
    std::unordered_set<std::string> prev_finished;
    if (!arg.result_file.empty()) {
        // fresult.open(arg.result_file, arg.cov_append ? std::ios::app : std::ios::out);
        std::vector<std::pair<std::string, std::string>> prev_result;
        if (arg.cov_append) {
            prev_result = read_result_file(arg.result_file);
        }
        fresult.open(arg.result_file);
        if (fresult.bad()) {
            throw std::runtime_error(fmt::format("open {} failed!", arg.result_file));
        }
        for (auto &[name, raw] : prev_result) {
            if (arg.overwrite && sample_file_set.count(name)) continue;
            if (raw.find("not found!") != raw.npos) continue;
            // if (raw.find("?") != raw.npos) continue;
            if (arg.allow_unknown || raw.find("unknown") == raw.npos) {
                prev_finished.insert(name);
                fresult << raw << std::endl;
            }
        }
    }
    std::ostream &output = fresult.is_open() ? fresult : std::cout;
    std::vector<std::thread> threads;
    for (auto &samples_file : arg.sample_files) {
        if (prev_finished.count(samples_file)) continue;
        threads.emplace_back([&arg, &samples_file, &output] {
            Coverage::run(output, arg.smt_file.c_str(), samples_file.c_str(), arg.max_samples);
        });
    }
    for (auto &th : threads) {
        th.join();
    }
    output << fmt::format("done.\n");
    output << fmt::format("all-bits: {}\n", allcovered.count_ones());
    output.flush();
    if (!arg.dump_file.empty()) {
        std::ofstream dumps{arg.dump_file};
        if (arg.human_readable) {
            dumps << allcovered;
        } else {
            allcovered.print_bin(dumps);
        }
    }
    return 0;
}

int main(int argc, char *argv[]) {
    using namespace clipp;
    Argument argument;
    auto cli = (  //
        value("smt2", argument.smt_file) % "The SMT2 file to analyze",
        option("-o") & value("output", argument.result_file) % "The coverage result file",
        option("--no-append").set(argument.cov_append, false) %
            "Overwrite the result file *entirely*",
        option("--allow-unknown").set(argument.allow_unknown, true) %
            "Allow unknown results to be kept in original result file",
        option("--overwrite").set(argument.overwrite, true) %
            "Overwrite results for sample files in this new run",
        option("-n") & value("count", argument.max_samples) %
                           "Maximum number of samples to process (0 means all samples)",
        option("-S").set(argument.human_readable) % "Dump human readable bits",
        option("-dump") & value("dumpfile", argument.dump_file) %
                              "The file to dump all-covered bits (for incremental coverage use)",
        values("samples", argument.sample_files) % "Sample files to analyze (run parallelly)"  //
    );
    if (!parse(argc, argv, cli)) {
        doc_formatting fmt;
        fmt.first_column(4).doc_column(25);
        std::cout << make_man_page(cli, argv[0], fmt);
        return -1;
    }
    if (!argument.cov_append && argument.overwrite) {
        std::cout << "warning: --overwrite has no effect when --no-append is set.\n";
    }
    if (!argument.cov_append && argument.allow_unknown) {
        std::cout << "warning: --allow-unknown has no effect when --no-append is set.\n";
    }
    if (argument.overwrite && argument.allow_unknown) {
        std::cout << "warning: --allow-unknown has no effect when --overwrite is set.\n";
    }

    try {
        return main_(argument);
    } catch (z3::exception &e) {
        std::cerr << "in " << argument.smt_file << ":" << std::endl;
        std::cerr << "z3 error: " << e.msg() << std::endl;
        std::terminate();
    } catch (std::exception &e) {
        std::cerr << "in " << argument.smt_file << ":" << std::endl;
        std::cerr << "std error: " << e.what() << std::endl;
        std::terminate();
    }
    __builtin_unreachable();
}
