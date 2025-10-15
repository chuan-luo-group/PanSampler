#include <algorithm>
#include <atomic>
#include <cstring>
#include <fstream>
#include <memory.h>
#include <numeric>
#include <random>
#include <vector>
#include <cassert>
#include <thread>
#include <mutex>

#include <bitwuzla/cpp/bitwuzla.h>
#include <bitwuzla/cpp/parser.h>
#include <clipp.h>

#define DBG_MACRO_NO_WARNING
#define DBG_MACRO_DISABLE
#include <dbg.h>

struct Argument {
    std::string input_file_path;
    std::string output_file_path;

    uint coverage_reach = 800;
    int seed = 1, samples = 100;
    int candidate_set_size = 50, thread_num = 10;
    int gen_type = 3;
    int retry_times = 10;
    int each_round = 1;
    int phase_type = 1;
    int _2wise_tuples_set_size = 10000;
    int post_opt_mode = 1;
    int score_mode = 1;

    bool set_phase = true;
    bool use_addition_constr = false;
    bool inline_save = false;
    bool fill_samples = false;
    bool simplified = true;
};
Argument ParseArgument(int argc, char *argv[]) {
    Argument argument;
    using namespace clipp;
    auto cli = ( //
        option("-i", "-input_file_path").required(true) &
            value("input file", argument.input_file_path),
        option("-o", "-output_file_path").required(true) &
            value("output file", argument.output_file_path),
        (option("-seed") & value("random seed", argument.seed))
            % "change random seed (default 1)",
        (option("-r", "-coverage") & value("target ast coverage", argument.coverage_reach))
            % "set target ast-coverage (r * 0.1%) (default 800)",
        (option("-samples") & value("samples count", argument.samples))
            % "set target samples count (default 100)",
        (option("-lambda", "-candidate_set_size") & value("size", argument.candidate_set_size))
            % "set lambda (default 50)",
        (option("-thread_num") & value("number of threads", argument.thread_num))
            % "set threads count (default 10), recommand to devide lambda",
        option("-gen_type") & value("generation type", argument.gen_type),
        option("-each_round") & value("each round", argument.each_round),
        option("-phase_type") & value("phase type", argument.phase_type),
        option("-not_use_post_opt").set(argument.post_opt_mode, 0)
            % "Disables post-sampling optimization technology" |
            (option("-post_opt_mode") & value("post opt mode", argument.post_opt_mode)),
        (option("-score_mode") & value("score mode", argument.score_mode))
            % "set score mode (default 1), 1 for AST-guided scoring function, 0 for Manhattan distance",
        option("-not_use_diversitysmt").set(argument.set_phase, false)
            % "Disables DiversitySMT" |
            option("-set_phase").set(argument.set_phase, true) |
            option("-unset_phase").set(argument.set_phase, false),
        option("-use_addition_constr").set(argument.use_addition_constr, true) |
            option("-not_use_addition_constr").set(argument.use_addition_constr, false),
        (option("-use_simp_ast").set(argument.simplified, true) |
            option("-not_use_simp_ast").set(argument.simplified, false))
            % "whether or not to use simplified ast",
        option("-inline_save").set(argument.inline_save)
            % "saving samples one by one immediately",
        option("-fill_samples").set(argument.fill_samples)
    );

    if (!parse(argc, argv, cli)) {
        std::cerr << make_man_page(cli, argv[0]);
        exit(1);
    }
    return argument;
}

namespace bitwuzla {
struct PrettyTerm {
    Term tm;
    PrettyTerm(Term tm): tm{std::move(tm)} {}
    operator Term() const { return tm; }

 private:
    std::ostream &print_impl(std::ostream &os, uint indent) const {
        for (uint i = 0; i < indent; ++ i) os << ' ';
        if (tm.num_children() == 0) return os << tm;
        os << '(' << tm.kind() << '\n';
        for (PrettyTerm tm : tm.children()) tm.print_impl(os, indent + 2) << '\n';
        for (uint i = 0; i < indent; ++ i) os << ' ';
        return os << ')';
    }

    friend std::ostream &operator<<(std::ostream &os, const PrettyTerm &tm) {
        return tm.print_impl(os, 0);
    }
};

class NekoSampler {

    struct NodeBit1 {
        uint32_t b;         // 在 terms 里的位置
        uint8_t state;
        friend std::ostream &operator<<(std::ostream &os, NodeBit1 val) noexcept {
            return os << val.b << " 0b" << (val.state >> 1) << (val.state & 1);
        }
    };

    struct NodeBit2 {
        uint32_t b1, b2;
        uint8_t state; // [idx2] [idx1]
        friend std::ostream &operator<<(std::ostream &os, NodeBit2 val) noexcept {
            return os << '(' << val.b1 << ',' << val.b2 << ','
                      << "0b" << (val.state >> 3 & 1)
                      << (val.state >> 2 & 1) << (val.state >> 1 & 1) << (val.state & 1) << ')';
        }
    };

    Term assert_val (TermManager &tm, const Term &term, bool v) { 
        return v ? term : tm.mk_term(Kind::NOT, {term}); 
    };

    auto bitwuzla_init () noexcept {
        try {
            parser.parse(params.input_file_path, true);
        } catch (const Exception &e) {
            std::cerr << "Error: " << e.what() << std::endl;
            exit(-1);
        }
        return parser.bitwuzla();
    }

    void bfs_bitwuzla_ast_thread (int thread_id) {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        auto &terms = terms_array[thread_id];
        terms.clear();

        if (params.simplified) bitwuzla->simplify();
        std::vector<Term> original_assertions = bitwuzla->get_assertions();
        std::queue<Term> q;
        std::unordered_set<Term> term_set;
        for (auto &assertion : original_assertions) {
            q.push(assertion);
            term_set.insert(assertion);
        }
        while (! q.empty()) {
            Term term = q.front(); q.pop();
            size_t ch_num = term.num_children();
            for (size_t i = 0; i < ch_num; i ++)
                if (term_set.find(term[i]) == term_set.end()) {
                    term_set.insert(term[i]);
                    q.push(term[i]);
                }
            if (ch_num == 0) continue;

            if (term.sort().is_bool())
                terms.push_back(term);
            else if (term.sort().is_bv()) {
                uint sz = term.sort().bv_size();
                for (uint i = 0; i < sz; i ++) {
                    auto tmp_term = tm.mk_term(bitwuzla::Kind::BV_EXTRACT, {term}, {i, i});
                    terms.push_back(tm.mk_term(bitwuzla::Kind::EQUAL, {tmp_term, tm.mk_bv_one(tm.mk_bv_sort(1))}));
                }
            }
        }
    }

    void bfs_bitwuzla_ast () {
        if (params.simplified) bitwuzla->simplify();
        std::vector<Term> original_assertions = bitwuzla->get_assertions();
        std::queue<Term> q;
        std::unordered_set<Term> term_set;
        for (auto &assertion : original_assertions) {
            q.push(assertion);
            term_set.insert(assertion);
        }
        while (! q.empty()) {
            Term term = q.front(); q.pop();
            size_t ch_num = term.num_children();
            for (size_t i = 0; i < ch_num; i ++) {
                if (term_set.find(term[i]) == term_set.end()) {
                    term_set.insert(term[i]);
                    q.push(term[i]);
                }
            }
            if (ch_num == 0) continue;
            if (term.sort().is_bv() || term.sort().is_bool())
                nodes.emplace_back(term);
        }
        if (nodes.empty()) params.gen_type = 1;

        terms.clear();
        flaten_map.clear();
        flaten_map.resize(nodes.size());
        int nidx = 0;
        for (const auto &term : nodes) {
            if (term.sort().is_bool()) {
                flaten_map[nidx].push_back(terms.size());
                terms.push_back(term);
                node_idx.push_back(nidx);
            }
            else if (term.sort().is_bv()) {
                uint sz = term.sort().bv_size();
                for (uint i = 0; i < sz; i ++) {
                    flaten_map[nidx].push_back(terms.size());
                    auto tmp_term = tm.mk_term(bitwuzla::Kind::BV_EXTRACT, {term}, {i, i});
                    terms.push_back(tm.mk_term(bitwuzla::Kind::EQUAL, {tmp_term, tm.mk_bv_one(tm.mk_bv_sort(1))}));
                    node_idx.push_back(nidx);
                }
            }
            nidx ++;
        }
    }

    void vars_init () noexcept {
        vars = parser.get_declared_funs();
        vars_num = vars.size(), vars_bit_num = 0;
        var_to_idx.reserve(vars.size());
        for (const auto &var : vars) {
            if ((! var.sort().is_bool()) && (! var.sort().is_bv()))
                continue ;
            var_to_idx.emplace_back(vars_bit_num);
            vars_bit_num += var.sort().is_bv() ? var.sort().bv_size() : 1;
        }
    }

    void sampler_init () noexcept {
        dbg("sampler_init begin");

        // int every = (params.candidate_set_size + params.thread_num - 1) / params.thread_num;
        // params.candidate_set_size = every * params.thread_num;
        candidate_set.resize(params.candidate_set_size);
        candidate_set_score.resize(params.candidate_set_size);
        state_array.resize(params.candidate_set_size);

        uncovered_bits.resize(nodes.size());
        for (uint i = 0; i < nodes.size(); i ++) {
            int sz = nodes[i].sort().is_bv() ? nodes[i].sort().bv_size() : 1;
            total_bits += sz;
            for (int j = 0; j < sz; j ++) {
                uncovered_bits[i].push_back({flaten_map[i][j], 0u});
            }
        }

        dbg("sampler_init end");
    }

    std::pair<int, int> get_score(int thread_id) noexcept {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        const auto &terms = terms_array[thread_id];
        const auto &vars = vars_array[thread_id];
        
        std::pair<int, int> score{0, 0};
        if (params.score_mode >= 1) {
            if (need_score1) {
                for (uint idx : notempty_nodes)
                    for (auto [b, k] : uncovered_bits[idx]) {
                        const Term &node = terms[b];
                        bool v = bitwuzla->get_value(node) == tm.mk_true();
                        if (!((k >> v) & 1))
                            score.first ++;
                    }
            }

            for (auto &[b1, b2, state] : uncovered_2wise_tuples) {
                const Term &term1 = terms[b1], &term2 = terms[b2];
                bool v1 = bitwuzla->get_value(term1) == tm.mk_true();
                bool v2 = bitwuzla->get_value(term2) == tm.mk_true();
                bool v = (v1 << 1 | v2);
                if (!((state >> v) & 1))
                    score.second ++;
            }
        } else {
            for (uint i = 0; i < vars_num; ++ i) {
                auto current = bitwuzla->get_value(vars[i]).str();
                for (auto &old : samples_set) {
                    auto size = std::min(current.size(), old[i].size());
                    for (uint c = 0; c < size; ++ c) {
                        score.first += old[i][c] != current[c];
                    }
                    score.first += current.size() - size;
                    score.first += old[i].size() - size;
                }
            }
        }
        return score;
    }

    bool generate_one_sample (  int thread_id, int uncovered_idx,
                                std::vector<Term> &sample, std::pair<int, int> &score ) noexcept {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        const auto &vars = vars_array[thread_id];
        auto &gen = gen_array[thread_id];
        const auto &terms = terms_array[thread_id];

        if (params.set_phase)
            bitwuzla->rand_phase(gen(), gen() % 10 > 1 ? params.phase_type : 0);

        std::vector<NodeBit1> &uncovered_bits_thisnode = uncovered_bits[uncovered_idx];
        bool ret_flag = false;
        int push_times = 0;
        if (params.gen_type == 1) {
            int constr_num = 0;
            std::vector<int> idx_arr(uncovered_bits_thisnode.size());
            std::iota(idx_arr.begin(), idx_arr.end(), 0);
            std::shuffle(idx_arr.begin(), idx_arr.end(), gen);
            std::pair<int, bool> c = std::make_pair(-1, 0);
            for (int idx : idx_arr) {
                auto [i, v] = uncovered_bits_thisnode[idx];
                bool b = (v == 1) ? true : (v == 2 ? false : (gen() % 2));
                bitwuzla->push(1); push_times ++;
                bitwuzla->assert_formula(assert_val(tm, terms[i], b));
                auto result = bitwuzla->check_sat();
                if (result != Result::SAT) {

                    if (constr_num == 0)
                        c = std::make_pair(idx, b);
                    
                    bitwuzla->pop(1); push_times --;
                    if (v == 1 || v == 2)
                        break ;
                    else {
                        bitwuzla->push(1); push_times ++;
                        bitwuzla->assert_formula(assert_val(tm, terms[i], b ^ 1));
                        if (bitwuzla->check_sat() != Result::SAT) {
                            bitwuzla->pop(1); push_times --;
                            break ;
                        }
                        else {
                            constr_num ++;
                            // bitwuzla_cur->assert_formula(assert_val(tm, terms[i], b ^ 1));
                        }
                    }
                }
                else {
                    constr_num ++;
                    // bitwuzla_cur->assert_formula(assert_val(tm, terms[i], b));
                }
            }
            ret_flag = (constr_num > 1);
            
            if (constr_num == 1 && c.first != -1) {
                std::unique_lock lock{mylock};
                uncovered_bits_thisnode[c.first].state |= (1 << c.second);
                // add_constr.push_back(c);
            }
        }
        else if (params.gen_type == 2) {
            
        }
        // else
        //     __builtin_unreachable();

        assert(bitwuzla->check_sat() == Result::SAT);
        sample.clear();
        for (auto &var : vars)
            sample.push_back(bitwuzla->get_value(var));

        score = get_score(thread_id);
        
        if (push_times > 0)
            bitwuzla->pop(push_times);

        return ret_flag;
    }

    void post_opt_thread(int thread_id, uint start_pos, uint end_pos,
                         const std::vector<std::string> &sample_strings,
                         std::vector<Term> &result, std::pair<int, int> &score) noexcept {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        auto &parser = *parser_array[thread_id];
        const auto &vars = vars_array[thread_id];

        std::vector<Term> sample;
        sample.reserve(sample_strings.size());
        for (auto &str: sample_strings) {
            Term term;
            try {
                term = parser.parse_term(str);
            } catch(Exception const&) {
                term = {};
            }
            sample.push_back(std::move(term));
        }

        result.reserve(vars_num);
        for (uint var_idx = start_pos; var_idx < end_pos; var_idx ++) {
            if (sample[var_idx].is_null()) continue;
            if (vars[var_idx].sort().is_array() || vars[var_idx].sort().is_fun()) continue;
            bitwuzla->push(1);
            bitwuzla->assert_formula(tm.mk_term(Kind::NOT, {
                tm.mk_term(Kind::EQUAL, {vars[var_idx], sample[var_idx]})
            }));
            if (bitwuzla->check_sat() == Result::SAT) {
                auto new_score = get_score(thread_id);
                if (new_score > score) {
                    score = new_score;
                    result.clear();
                    for (uint i = 0; i < vars_num; i ++)
                        result.push_back(bitwuzla->get_value(vars[i]));
                }
            }
            bitwuzla->pop(1);
        }
    }

    void post_opt(int &thread_id, std::vector<Term> &sample, std::pair<int, int> &score) noexcept {
        std::vector<std::string> sample_strings;
        sample_strings.reserve(sample.size());
        for (const auto &term : sample)
            sample_strings.push_back(term.str());
        auto old_score = score;
        int div = vars_num / params.thread_num, rem = vars_num % params.thread_num;
        Threads.clear();
        std::vector<std::vector<Term>> results(params.thread_num);
        std::vector<std::pair<int, int>> scores(params.thread_num, score);
        for (int i = 0, st = 0; i < params.thread_num; i ++) {
            int ed = st + div + (i < rem);
            Threads.emplace_back([this, i, st, ed, &sample_strings, &results, &scores] {
                post_opt_thread(i, st, ed, sample_strings, results[i], scores[i]);
            });
            st = ed;
        }
        for (int i = 0; i < params.thread_num; i ++) {
            Threads[i].join();
            if (scores[i] > score) {
                thread_id = i;
                score = scores[i];
                sample.swap(results[i]);
            }
        }
        dbg(old_score, score);
        // if (old_score == score) {
        //     params.post_opt_mode = 0;
        // }
    }

    void simple_post_opt(int thread_id, std::vector<Term> &sample, std::pair<int, int> &score) noexcept {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        const auto &vars = vars_array[thread_id];

        auto old_score = score;
        std::pair<int, Term> result{-1, {}};
        for (uint vi = 0; vi < vars_num; vi ++) {
            bitwuzla->push(1);
            for (uint vj = 0; vj < vars_num; vj ++) {
                if (vars[vj].sort().is_array() || vars[vj].sort().is_fun()) continue;
                auto term = tm.mk_term(Kind::EQUAL, {vars[vj], sample[vj]});
                if (vi == vj) bitwuzla->assert_formula(tm.mk_term(Kind::NOT, {term}));
                else bitwuzla->assert_formula(term);;
            }
            if (bitwuzla->check_sat() == Result::SAT) {
                auto new_score = get_score(thread_id);
                if (new_score > score) {
                    score = new_score;
                    result = {vi, bitwuzla->get_value(vars[vi])};
                }
            }
            bitwuzla->pop(1);
        }
        if (result.first != -1) {
            std::swap(sample[result.first], result.second);
        }
        dbg(old_score, score);
        // if (old_score == score) {
        //     params.post_opt_mode = 0;
        // }
    }

    Term convert_const_array(TermManager &tm, const Term &term, const Term &var) noexcept {
        if (term.kind() == Kind::CONST_ARRAY) {
            return var;
        }
        if (term.num_children() == 0) return term;
        std::vector<Term> terms;
        terms.reserve(term.num_children());
        for (uint i = 0; i < term.num_children(); i ++) {
            terms.push_back(convert_const_array(tm, term[i], var));
        }
        try {
            return tm.mk_term(term.kind(), terms);
        } catch(Exception const&e) {
            dbg(var.sort(), term.kind(), terms);
            std::terminate();
        }
    }

    Term convert_lambda_function(TermManager &tm, const Term &term, const Term &var) noexcept {
        assert (var.sort().is_fun());
        std::vector<Term> params;
        std::unordered_map<std::string, size_t> name2idx;
        params.reserve(var.sort().fun_domain().size());
        Term current = term;
        while (current.kind() == Kind::LAMBDA) {
            assert (current.num_children() == 2);
            auto &&children = current.children();
            name2idx[children[0].str()] = params.size();
            params.push_back(children[0]);
            current = children[1];
        }
        assert (params.size() == var.sort().fun_domain().size());
        std::vector<Term> entries;
        while (current.kind() == Kind::ITE) {
            assert (current.num_children() == 3);
            std::vector<Term> call(params.size() + 1);
            call[0] = var;
            auto &&children = current.children();
            Term cond = children[0];
            auto parse_equal = [&name2idx, &call](Term term) noexcept {
                assert (term.kind() == Kind::EQUAL);
                assert (term.num_children() == 2);
                auto &&children = term.children();
                size_t idx = name2idx.at(children[0].str());
                call[idx + 1] = children[1];
            };
            while (cond.kind() == Kind::AND) {
                assert (cond.num_children() == 2);
                auto &&children = cond.children();
                parse_equal(children[1]);
                cond = children[0];
            }
            parse_equal(cond);
            Term apply = tm.mk_term(Kind::APPLY, call);
            Term assertion = tm.mk_term(Kind::EQUAL, {apply, children[1]});
            current = children[0];
            entries.push_back(assertion);
        }
        assert (!entries.empty());
        return entries.size() == 1 ? entries.front() : tm.mk_term(Kind::AND, entries);
    }

    void update_info_thread_nophase (int thread_id, const std::vector<std::string> &sample) noexcept {
        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &parser = *parser_array[thread_id];
        auto &tm = *tm_array[thread_id];
        const auto &vars = vars_array[thread_id];

        std::vector<Term> result;
        result.reserve(vars.size());
        for (uint i = 0; i < vars_num; ++ i) {
            if (vars[i].sort().is_fun()) continue;
            auto value = parser.parse_term(sample[i]);
            if (vars[i].sort().is_array()) value = convert_const_array(tm, value, vars[i]);
            result.push_back(tm.mk_term(Kind::EQUAL, {vars[i], value}));
        }
        bitwuzla->assert_formula(tm.mk_term(Kind::NOT, {tm.mk_term(Kind::AND, std::move(result))}));
        if (bitwuzla->check_sat() != Result::SAT) {
            has_model = false;
        }
    }

    void update_info (int thread_id, std::vector<Term> &sample, std::pair<int, int> &score) noexcept {
        if (params.post_opt_mode == 1) {
            post_opt(thread_id, sample, score);
        } else if (params.post_opt_mode == 2) {
            simple_post_opt(thread_id, sample, score);
        }

        auto &bitwuzla = bitwuzla_array[thread_id];
        auto &tm = *tm_array[thread_id];
        const auto &vars = vars_array[thread_id];
        const auto &terms = terms_array[thread_id];

        std::vector<std::string> sample_str;
        bitwuzla->push(1);
        for (uint i = 0; i < vars_num; i ++) {
            if (vars[i].sort().is_array()) {
                sample_str.push_back(sample[i].str());
                bitwuzla->assert_formula(tm.mk_term(Kind::EQUAL, {vars[i], convert_const_array(tm, sample[i], vars[i])}));
            } else if (vars[i].sort().is_fun()) {
                auto result = convert_lambda_function(tm, sample[i], vars[i]);
                sample_str.push_back("!" + result.str());
                bitwuzla->assert_formula(result);
            } else {
                sample_str.push_back(sample[i].str());
                bitwuzla->assert_formula(tm.mk_term(Kind::EQUAL, {vars[i], sample[i]}));
            }
        }
        assert(bitwuzla->check_sat() == Result::SAT);

        for (uint idx : notempty_nodes) {
            std::vector<uint> delete_list;
            for (uint i = 0; i < uncovered_bits[idx].size(); i ++) {
                auto &[b, k] = uncovered_bits[idx][i];
                const Term &node = terms[b];
                bool v = bitwuzla->get_value(node) == tm.mk_true();
                if (!((k >> v) & 1))
                    covered_bits ++;
                // k |= (1 << v);
                uncovered_bits[idx][i].state |= (1 << v);
                if (k == 3)
                    delete_list.push_back(i);
            }
            
            auto &current = uncovered_bits[idx];
            auto last = current.size();
            for (int i = delete_list.size() - 1; i >= 0; i --) {
                std::swap(current[delete_list[i]], current[--last]);
            }
            current.resize(last);
        }

        for (auto &[b1, b2, state] : uncovered_2wise_tuples) {
            const Term &term1 = terms[b1], &term2 = terms[b2];
            bool v1 = bitwuzla->get_value(term1) == tm.mk_true();
            bool v2 = bitwuzla->get_value(term2) == tm.mk_true();
            bool v = (v1 << 1 | v2);
            state |= (1 << v);
        }

        bitwuzla->pop(1);

        if (params.set_phase == false)
            for (int i = 0; i < params.thread_num; ++ i)
                update_info_thread_nophase(i, sample_str);
        sample_n ++;
        samples_set.push_back(std::move(sample_str));
        dbg(sample_n, covered_bits);
        std::cout << "sample: " << sample_n << std::endl;
        if (params.inline_save) {
            result_file << "Sample " << sample_n << "\n";
            for (uint i = 0; i < vars_num; i ++) {
                result_file << vars[i] << " = " << samples_set.back()[i] << "\n";
            }
            result_file << "\n";
            result_file.flush();
        }
    }

    void generate_candidate_set_thread (int thread_id, int uncovered_idx, int st, int ed) {
        auto &state = state_array[thread_id];
        state = 0;
        for (int i = st; i < ed; i ++) {
            state += generate_one_sample(thread_id, uncovered_idx, candidate_set[i], candidate_set_score[i].first);
            candidate_set_score[i].second = std::make_pair(thread_id, i);
        }
    }

    void generate_candidate_set (int uncovered_idx) {
        int every = (params.candidate_set_size + params.thread_num - 1) / params.thread_num;
        Threads.clear();
        for (int i = 0, t = 0; i < params.candidate_set_size; i += every, t ++)
            Threads.emplace_back(   
                                    &NekoSampler::generate_candidate_set_thread, this, 
                                    t, uncovered_idx, 
                                    i, std::min(i + every, params.candidate_set_size) 
                                );
        for (auto &thread : Threads)
            thread.join();
    }

    int getdis(const Term &term1, const Term &term2) noexcept {
        std::string s1 = term1.str(), s2 = term2.str();
        assert(s1.length() == s2.length());
        uint sz = s1.length(), dis = 0;
        for (uint i = 0; i < sz; i ++)
            dis += s1[i] != s2[i];
        return dis;
    }

    int getdis(const std::vector<Term> &m1, const std::vector<Term> &m2) {
        int dis = 0;
        for (uint i = 0; i < vars_num; i ++)
            dis += getdis(m1[i], m2[i]);
        return dis;
    }

    std::pair<bool, bool> sample_one (int uncovered_idx) noexcept {
        add_constr.clear();

        update_notempty_nodes();
        generate_candidate_set(uncovered_idx);
        sort(candidate_set_score.begin(), candidate_set_score.end(), std::greater<>());
        dbg(candidate_set_score);
        
        int state = 0;
        for (int s : state_array)
            state += s;
        dbg(state);
        bool flag = state < (params.candidate_set_size + 1) / 2;

        dbg(nodes[uncovered_idx].sort(), add_constr);
        sort(add_constr.begin(), add_constr.end());
        for (uint i = 0; i < add_constr.size(); i ++) {
            if (i > 0 && add_constr[i] == add_constr[i - 1])
                continue ;
            auto &[b, v] = add_constr[i];
            for (int t = 0; t < params.thread_num; t ++)
                bitwuzla_array[t]->assert_formula(assert_val(*tm_array[t], terms_array[t][flaten_map[uncovered_idx][b]], v ^ 1));
        }

        if (candidate_set_score[0].first.first + candidate_set_score[0].first.second <= 0) {
            if (params.score_mode >= 2) {
                need_score1 = false;
                if (uncovered_2wise_tuples.empty())
                    sample_2wise_tuples();
                else
                    params.score_mode = 1;
                return {false, flag};
            } else if (params.score_mode == 1) {
                need_score1 = false;
                params.score_mode = 0;
                return {false, flag};
            }
        }

        int thread_id1 = candidate_set_score[0].second.first;
        int i1 = candidate_set_score[0].second.second;
        dbg(thread_id1, i1);
        update_info(thread_id1, candidate_set[i1], candidate_set_score[0].first);

        if (params.each_round == 1 || sample_n >= params.samples) {
            // if (candidate_set_score.rbegin()->first.first + candidate_set_score.rbegin()->first.second == 0)
            //     sample_2wise_tuples();
            return {true, flag};
        }

        long long mx_dis = 0;
        int p = -1;
        for (int i = 1; i < params.candidate_set_size; i ++) {
            int dis = getdis(candidate_set[i1], candidate_set[candidate_set_score[i].second.second]);
            if (dis > mx_dis)
                mx_dis = dis, p = i;
        }

        if (mx_dis == 0 || p == -1) {
            // if (candidate_set_score.rbegin()->first.first + candidate_set_score.rbegin()->first.second == 0)
            //     sample_2wise_tuples();
            return {true, flag};
        }

        int thread_id2 = candidate_set_score[p].second.first;
        int i2 = candidate_set_score[p].second.second;
        update_info(thread_id2, candidate_set[i2], candidate_set_score[p].first);

        if (params.each_round == 2 || sample_n >= params.samples) {
            // if (candidate_set_score.rbegin()->first.first + candidate_set_score.rbegin()->first.second == 0)
            //     sample_2wise_tuples();
            return {true, flag};
        }

        mx_dis = 0, p = -1;
        for (int i = 1; i < params.candidate_set_size; i ++) {
            if (candidate_set_score[i].second.second == i2)
                continue ;
            int dis1 = getdis(candidate_set[i1], candidate_set[candidate_set_score[i].second.second]);
            int dis2 = getdis(candidate_set[i2], candidate_set[candidate_set_score[i].second.second]);
            if (1ll * dis1 * dis2 > mx_dis)
                mx_dis = 1ll * dis1 * dis2, p = i;
        }
        if (mx_dis == 0 || p == -1) {
            // if (candidate_set_score.rbegin()->first.first + candidate_set_score.rbegin()->first.second == 0)
            //     sample_2wise_tuples();
            return {true, flag};
        }

        int thread_id3 = candidate_set_score[p].second.first;
        int i3 = candidate_set_score[p].second.second;
        update_info(thread_id3, candidate_set[i3], candidate_set_score[p].first);
        
        // if (candidate_set_score.rbegin()->first.first + candidate_set_score.rbegin()->first.second == 0)
        //     sample_2wise_tuples();
        return {true, flag};
    }

    void update_notempty_nodes () {
        notempty_nodes.clear();
        auto size = nodes.size();
        for (uint i = 0; i < size; i ++)
            if (! uncovered_bits[i].empty())
                notempty_nodes.push_back(i);
        dbg(notempty_nodes.size());
        if (! notempty_nodes.empty())
            dbg(notempty_nodes.back());
    }

    void thread_init(int thread_id) {
        gen_array[thread_id].seed(params.seed + thread_id + 3);
        
        auto &parser_cur = *parser_array[thread_id];
        try {
            parser_cur.parse(params.input_file_path, true);
        } catch (const Exception &e) {
            std::cerr << "Error: " << e.what() << std::endl;
            exit(-1);
        }
        
        bitwuzla_array[thread_id] = parser_cur.bitwuzla();
        vars_array[thread_id] = parser_cur.get_declared_funs();
        bfs_bitwuzla_ast_thread(thread_id);
    }

    void sample_2wise_tuples() {
        if (1ll * terms.size() * terms.size() / 100 < (size_t) params._2wise_tuples_set_size)
            params._2wise_tuples_set_size = terms.size() * terms.size() / 100;

        uncovered_2wise_tuples.clear();
        for (int i = 0; i < params._2wise_tuples_set_size; i ++) {
            uint b1 = gen() % terms.size(), b2 = gen() % terms.size();
            while (b1 == b2)
                b1 = gen() % terms.size(), b2 = gen() % terms.size();

            uncovered_2wise_tuples.emplace_back((NodeBit2){b1, b2, 0});
        }
    }
  
  public:
    NekoSampler(const Argument &args, Options opt) noexcept
        : params(args), options(std::move(opt)), tm(), parser(tm, options),
          bitwuzla(bitwuzla_init()) { // bitwuzla 需在 z3_visit 前初始化

        gen.seed(args.seed);
        vars_init();
        bfs_bitwuzla_ast();

        dbg(nodes.size());
        dbg(terms.size());

        dbg(params.thread_num);
        dbg("thread init begin");

        for (int i = 0; i < params.thread_num; i++) {
            auto tm_cur = std::make_unique<TermManager>();
            tm_array.emplace_back(std::move(tm_cur));

            parser_array.push_back(std::make_unique<parser::Parser>(*tm_array[i], options));
        }
        bitwuzla_array.resize(params.thread_num);
        gen_array.resize(params.thread_num);
        vars_array.resize(params.thread_num);
        terms_array.resize(params.thread_num);

        Threads.clear();
        for (int i = 0; i < params.thread_num; i ++)
            Threads.emplace_back(&NekoSampler::thread_init, this, i);
        for (auto &thread : Threads)
            thread.join();
        dbg("thread init end");

        sampler_init();
        dbg(total_bits);
    }

    void sample() noexcept {
        if (params.inline_save) {
            result_file.open(params.output_file_path);
        }

        int retry_times = 0;
        uint idx = 0;
        int node_num = nodes.size();
        dbg(node_num);
        while (sample_n < params.samples &&
               covered_bits * 500 / total_bits < params.coverage_reach &&
               retry_times < params.retry_times &&
               has_model) {
            dbg(idx);

            int times = 0;
            while (uncovered_bits[idx].empty() && times < node_num)
                idx = (idx + 1) % node_num, times ++;
            
            if (times >= node_num)
                retry_times = params.retry_times;
            else {
                auto ret = sample_one(idx);
                dbg(ret);
                if (! ret.first)
                    retry_times ++;
                if ((! ret.first) || ret.second)
                    idx = (idx + 1) % node_num;
            }
            // dbg(sample_n, covered_bits);
        }
        if (params.fill_samples) {
            while (sample_n < params.samples) {
                int idx = gen() % node_num;
                dbg(sample_one(idx));
            }
        }
    }

    void save() noexcept {
        std::cout << "save samples at " << params.output_file_path << std::endl;
        if (params.inline_save) return result_file.close();
        result_file.open(params.output_file_path);
        int samples = samples_set.size();
        for (int i = 0; i < samples; i++) {
            result_file << "Sample " << (i + 1) << "\n";
            const auto &m = samples_set[i];
            for (uint j = 0; j < vars_num; j++)
                result_file << vars[j] << " = " << m[j] << "\n";
            result_file << "\n";
        }
        result_file.close();
    }

  private:
    Argument params;
    Options options;
    std::mt19937 gen;
    std::ofstream result_file;

    TermManager tm;
    parser::Parser parser;
    std::shared_ptr<Bitwuzla> bitwuzla;
    std::vector<Term> terms, nodes;
    std::vector<std::vector<uint32_t>> flaten_map;
    std::vector<uint32_t> node_idx;

    std::vector<Term> vars;
    uint vars_num, vars_bit_num;
    std::vector<uint> var_to_idx;
    std::vector<std::vector<Term>> candidate_set;
    std::vector<std::pair<std::pair<int,int>, std::pair<int,int>>> candidate_set_score;
    std::vector<int> state_array;

    std::vector<std::vector<NodeBit1>> uncovered_bits;
    std::vector<uint> notempty_nodes;

    uint total_bits = 0, covered_bits = 0;
    std::atomic_bool has_model = true;
    std::vector<std::vector<std::string>> samples_set;

    std::vector<std::thread> Threads;
    std::vector<std::unique_ptr<parser::Parser>> parser_array;

    std::vector<std::unique_ptr<TermManager>> tm_array;
    std::vector<std::shared_ptr<Bitwuzla>> bitwuzla_array;
    std::vector<std::mt19937> gen_array;
    std::vector<std::vector<Term>> vars_array;
    std::vector<std::vector<Term>> terms_array;

    int sample_n = 0;
    std::mutex mylock;
    std::vector<std::pair<int, bool>> add_constr;

    std::vector<NodeBit2> uncovered_2wise_tuples;
    bool need_score1 = true;
};

}

int main(int argc, char *argv[]) {
    Argument argument = ParseArgument(argc, argv);

    using namespace bitwuzla;
    Options options;
    options.set(Option::PRODUCE_MODELS, true);
    options.set(Option::PRODUCE_UNSAT_CORES, true);
    options.set(Option::PP_SKELETON_PREPROC, false);

    NekoSampler sampler(argument, std::move(options));
    sampler.sample();
    sampler.save();

    /// save some time...
    std::quick_exit(0);
}
