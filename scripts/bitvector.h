#pragma once

#include <fmt/core.h>
#include <fmt/format.h>
#include <fmt/ranges.h>
#include <algorithm>
#include <cctype>
#include <cstdint>
#include <functional>
#include <iostream>
#include <iterator>
#include <numeric>
#include <string>
#include <vector>

template <class It1, class It2, class Fn>
void for_each(It1 first1, It1 last1, It2 first2, Fn &&fn) {
    for (; first1 != last1; ++first1, ++first2) {
        std::invoke(fn, *first1, *first2);
    }
}

class bitvector {
    friend struct fmt::formatter<bitvector>;
    static constexpr size_t BITS = 64;

    class bool_proxy {
        friend bitvector;
        uint64_t *ptr;
        size_t idx;

        bool_proxy(uint64_t *ptr, size_t idx) : ptr(ptr), idx(63 - idx) {}

     public:
        operator bool() const { return *ptr >> idx & 1; }

        bool_proxy &operator=(const bool_proxy &other) { return *this = bool(other); }
        bool_proxy &operator=(bool_proxy &&other) { return *this = bool(other); }

        bool_proxy &operator=(bool value) {
            if (value)
                *ptr |= uint64_t{1} << idx;
            else
                *ptr &= ~(uint64_t{1} << idx);
            return *this;
        }
        bool_proxy &operator|=(bool value) {
            *ptr |= uint64_t{1} << idx;
            return *this;
        }
        bool_proxy &operator&=(bool value) {
            *ptr &= uint64_t{1} << idx;
            return *this;
        }
        bool_proxy &operator^=(bool value) {
            *ptr ^= uint64_t{1} << idx;
            return *this;
        }
    };

 public:
    bitvector() noexcept = default;
    bitvector(size_t size) : bitvector{} { resize(size); }

    bool empty() const noexcept { return m_size == 0; }

    size_t size() const noexcept { return m_size; }

    size_t capacity() const noexcept { return m_data.capacity() * BITS; }

    void push_back(bool bit) {
        if (m_size % BITS == 0) {
            m_data.push_back(static_cast<uint64_t>(bit) << 63);
        } else {
            m_data.back() |= static_cast<uint64_t>(bit) << (63 - m_size % BITS);
        }
        ++m_size;
    }

    void reserve(size_t n) {
        if (m_size >= n) return;
        m_data.reserve(n / BITS + 1);
    }

    void resize(size_t new_size) {
        if (new_size == m_size) return;
        m_data.resize((new_size + BITS - 1) / BITS, 0);
        m_size = new_size;
    }

    bool operator[](size_t idx) const noexcept {
        return m_data[idx / BITS] >> (63 - idx % BITS) & 1;
    }

    bool_proxy operator[](size_t idx) noexcept {
        return bool_proxy{&m_data[idx / BITS], idx % BITS};
    }

    size_t count_ones() const noexcept {
        return std::transform_reduce(m_data.begin(), m_data.end(), size_t{}, std::plus<>{},
                                     [](auto v) { return __builtin_popcountll(v); });
    }

    size_t count_zeros() const noexcept { return m_size - count_ones(); }

    bitvector &operator|=(const bitvector &other) {
        for_each(m_data.begin(), m_data.end(), other.m_data.begin(),
                 [](auto &x, auto y) { x |= y; });
        return *this;
    }

    bitvector &operator&=(const bitvector &other) {
        for_each(m_data.begin(), m_data.end(), other.m_data.begin(),
                 [](auto &x, auto y) { x &= y; });
        return *this;
    }

    bitvector &operator^=(const bitvector &other) {
        for_each(m_data.begin(), m_data.end(), other.m_data.begin(),
                 [](auto &x, auto y) { x ^= y; });
        return *this;
    }

    bitvector operator|(const bitvector &other) const {
        bitvector result(m_size);
        std::transform(m_data.begin(), m_data.end(), other.m_data.begin(),
                       std::back_inserter(result.m_data), std::bit_or<>{});
        return result;
    }

    bitvector operator&(const bitvector &other) const {
        bitvector result(m_size);
        std::transform(m_data.begin(), m_data.end(), other.m_data.begin(),
                       std::back_inserter(result.m_data), std::bit_and<>{});
        return result;
    }

    bitvector operator^(const bitvector &other) const {
        bitvector result(m_size);
        std::transform(m_data.begin(), m_data.end(), other.m_data.begin(),
                       std::back_inserter(result.m_data), std::bit_xor<>{});
        return result;
    }

    void print_bin(std::ostream &os) const {
        char const *size_bin = reinterpret_cast<char const *>(&m_size);
        for (uint i = 0; i < sizeof(m_size) / sizeof(char); ++i) os << size_bin[i];
        char const *data_bin = reinterpret_cast<char const *>(m_data.data());
        auto length = sizeof(uint64_t) / sizeof(char) * m_data.size();
        for (uint i = 0; i < length; ++i) os << data_bin[i];
    }

    void read_bin(std::istream &is) {
        auto buffer = is.rdbuf();
        const auto non_eof_bumpc = [&buffer] {
            if (auto res = buffer->sbumpc(); res != EOF)
                return (char)res;
            else
                throw std::runtime_error("unexpected EOF");
        };
        char *size_bin = reinterpret_cast<char *>(&m_size);
        for (uint i = 0; i < sizeof(m_size) / sizeof(char); ++i) size_bin[i] = non_eof_bumpc();
        m_data.clear();
        m_data.reserve(m_size / BITS + 1);
        while (buffer->sgetc() != EOF) {
            uint64_t a_data;
            char *data_bin = reinterpret_cast<char *>(&a_data);
            for (uint i = 0; i < sizeof(a_data) / sizeof(char); ++i) data_bin[i] = non_eof_bumpc();
            m_data.push_back(a_data);
        }
    }

    friend std::ostream &operator<<(std::ostream &os, const bitvector &bv) {
        return os << fmt::format("{}", bv);
    }

    friend std::istream &operator>>(std::istream &is, bitvector &bv) {
        std::string buffer;
        is >> buffer;
        size_t idx = 0;
        bv.m_size = std::stoull(buffer, &idx, 16);
        // assert(buffer[idx] == ':');
        buffer = buffer.substr(idx + 1);
        // assert(buffer.size() % 16 == 0);
        bv.m_data.clear();
        bv.m_data.reserve(bv.m_size / BITS + 1);
        while (!buffer.empty()) {
            bv.m_data.push_back(std::stoull(buffer.substr(0, 16), nullptr, 16));
            buffer = buffer.substr(16);
        }
        return is;
    }

 private:
    size_t m_size = 0;
    std::vector<uint64_t> m_data;
};

template <>
struct fmt::formatter<bitvector> : fmt::formatter<std::string> {
    template <class Context>
    auto format(const bitvector &bv, Context &ctx) const -> decltype(ctx.out()) {
        return fmt::formatter<std::string>::format(
            fmt::format("{:x}:{:016x}", bv.m_size, fmt::join(bv.m_data, "")), ctx);
    }
};
