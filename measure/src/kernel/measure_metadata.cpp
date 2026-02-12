/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/measure_metadata.h"
#include <iostream>
#include <stdexcept>
#include <cstring>

namespace lean {

// --- measure_metadata ---

measure_metadata measure_metadata::default_meta() {
    return measure_metadata{};
}

bool measure_metadata::is_default() const {
    return m_theory == 0
        && m_rigor == rigor_level::strict
        && m_epsilon_bound.is_zero()
        && m_theory_deps.empty()
        && m_axiom_deps.empty()
        && m_epsilon_proof_root == 0;
}

// --- Binary I/O helpers ---

static void write_u16(std::ostream & out, uint16_t v) {
    out.write(reinterpret_cast<const char*>(&v), 2);
}

static void write_u32(std::ostream & out, uint32_t v) {
    out.write(reinterpret_cast<const char*>(&v), 4);
}

static void write_u64(std::ostream & out, uint64_t v) {
    out.write(reinterpret_cast<const char*>(&v), 8);
}

static void write_u8(std::ostream & out, uint8_t v) {
    out.write(reinterpret_cast<const char*>(&v), 1);
}

static uint16_t read_u16(std::istream & in) {
    uint16_t v; in.read(reinterpret_cast<char*>(&v), 2); return v;
}

static uint32_t read_u32(std::istream & in) {
    uint32_t v; in.read(reinterpret_cast<char*>(&v), 4); return v;
}

static uint64_t read_u64(std::istream & in) {
    uint64_t v; in.read(reinterpret_cast<char*>(&v), 8); return v;
}

static uint8_t read_u8(std::istream & in) {
    uint8_t v; in.read(reinterpret_cast<char*>(&v), 1); return v;
}

static void write_string(std::ostream & out, std::string const & s) {
    write_u16(out, static_cast<uint16_t>(s.size()));
    out.write(s.data(), s.size());
}

static std::string read_string(std::istream & in) {
    uint16_t len = read_u16(in);
    std::string s(len, '\0');
    in.read(&s[0], len);
    return s;
}

// --- Serialization ---

void serialize_measure_meta(
    std::ostream & out,
    std::unordered_map<std::string, measure_metadata> const & meta)
{
    write_u32(out, MEASURE_MAGIC);
    write_u16(out, MEASURE_VERSION);
    write_u32(out, static_cast<uint32_t>(meta.size()));

    for (auto const & [name, m] : meta) {
        write_string(out, name);
        write_u32(out, m.m_theory);
        write_u8(out, static_cast<uint8_t>(m.m_rigor));
        write_u64(out, m.m_epsilon_bound.m_numerator);
        write_u64(out, m.m_epsilon_bound.m_denominator);

        write_u16(out, static_cast<uint16_t>(m.m_theory_deps.size()));
        for (auto tid : m.m_theory_deps) {
            write_u32(out, tid);
        }

        write_u16(out, static_cast<uint16_t>(m.m_axiom_deps.size()));
        for (auto const & ax : m.m_axiom_deps) {
            write_string(out, ax);
        }

        write_u64(out, m.m_epsilon_proof_root);
    }
}

// --- Deserialization ---

std::unordered_map<std::string, measure_metadata>
deserialize_measure_meta(std::istream & in)
{
    uint32_t magic = read_u32(in);
    if (magic != MEASURE_MAGIC) {
        throw std::runtime_error(
            "Invalid .measure file: bad magic number");
    }
    uint16_t version = read_u16(in);
    if (version != MEASURE_VERSION) {
        throw std::runtime_error(
            "Unsupported .measure file version");
    }

    uint32_t count = read_u32(in);
    std::unordered_map<std::string, measure_metadata> result;
    result.reserve(count);

    for (uint32_t i = 0; i < count; ++i) {
        std::string name = read_string(in);
        measure_metadata m;
        m.m_theory = read_u32(in);
        uint8_t rigor_raw = read_u8(in);
        if (rigor_raw > static_cast<uint8_t>(rigor_level::numerical)) {
            throw std::runtime_error(
                "Invalid rigor_level in .measure file: " + std::to_string(rigor_raw));
        }
        m.m_rigor = static_cast<rigor_level>(rigor_raw);
        m.m_epsilon_bound.m_numerator = read_u64(in);
        m.m_epsilon_bound.m_denominator = read_u64(in);
        if (m.m_epsilon_bound.m_denominator == 0) {
            throw std::runtime_error(
                "Invalid epsilon_val in .measure file: denominator is zero");
        }

        uint16_t td_count = read_u16(in);
        m.m_theory_deps.resize(td_count);
        for (uint16_t j = 0; j < td_count; ++j) {
            m.m_theory_deps[j] = read_u32(in);
        }

        uint16_t ax_count = read_u16(in);
        m.m_axiom_deps.resize(ax_count);
        for (uint16_t j = 0; j < ax_count; ++j) {
            m.m_axiom_deps[j] = read_string(in);
        }

        m.m_epsilon_proof_root = read_u64(in);
        result[name] = m;
    }
    return result;
}

// --- Path derivation ---

std::string measure_path_from_olean(std::string const & olean_path) {
    std::string result = olean_path;
    auto pos = result.rfind(".olean");
    if (pos != std::string::npos) {
        result.replace(pos, 6, ".measure");
    } else {
        result += ".measure";
    }
    return result;
}

// --- Merge ---

std::unordered_map<std::string, measure_metadata>
merge_measure_meta(
    std::vector<std::unordered_map<std::string, measure_metadata>> const & sources)
{
    std::unordered_map<std::string, measure_metadata> merged;
    for (auto const & src : sources) {
        for (auto const & [name, meta] : src) {
            auto it = merged.find(name);
            if (it != merged.end()) {
                if (it->second.m_theory != meta.m_theory) {
                    throw std::runtime_error(
                        "Conflicting measure_metadata for '"
                        + name + "': different theory_id");
                }
            } else {
                merged[name] = meta;
            }
        }
    }
    return merged;
}

} // namespace lean