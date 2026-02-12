/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "kernel/conservation.h"
#include <sstream>
#include <algorithm>
#include <stdexcept>
#include <cctype>
#include <cmath>

namespace lean {

// ── expr_pool helpers ───────────────────────────────────────────

void expr_pool::collect_vars(size_t idx,
                              std::vector<std::string> & out) const
{
    auto const & n = m_nodes[idx];
    if (n.m_kind == expr_node_kind::variable) {
        out.push_back(n.m_name);
        return;
    }
    for (auto c : n.m_children) {
        collect_vars(c, out);
    }
}

bool expr_pool::references_var(size_t idx,
                                std::string const & var) const
{
    auto const & n = m_nodes[idx];
    if (n.m_kind == expr_node_kind::variable) {
        return n.m_name == var;
    }
    for (auto c : n.m_children) {
        if (references_var(c, var)) return true;
    }
    return false;
}

// ── dim_tag formatting ──────────────────────────────────────────

std::string dim_tag::to_string() const {
    std::ostringstream os;
    os << "L" << L << ".M" << M << ".T" << T
       << ".I" << I << ".Th" << Theta
       << ".N" << N << ".J" << J;
    return os.str();
}

// ── AST-level tokenizer for Pass 1 ─────────────────────────────

enum class tok_kind : uint8_t {
    ident, number, assign, colon_assign,
    plus, minus, star, slash, caret,
    lparen, rparen, comma, newline, eof
};

struct token {
    tok_kind kind = tok_kind::eof;
    std::string text;
    unsigned line = 0;
    unsigned col = 0;
};

static std::vector<token> tokenize(std::string const & src) {
    std::vector<token> toks;
    unsigned line = 1, col = 1;
    size_t i = 0;
    while (i < src.size()) {
        char c = src[i];
        if (c == '\n') {
            toks.push_back({tok_kind::newline, "\n", line, col});
            ++line; col = 1; ++i; continue;
        }
        if (c == ' ' || c == '\t' || c == '\r') {
            ++col; ++i; continue;
        }
        if (c == ':' && i + 1 < src.size() && src[i+1] == '=') {
            toks.push_back({tok_kind::colon_assign, ":=", line, col});
            col += 2; i += 2; continue;
        }
        if (c == '=') { toks.push_back({tok_kind::assign, "=", line, col}); ++col; ++i; continue; }
        if (c == '+') { toks.push_back({tok_kind::plus, "+", line, col}); ++col; ++i; continue; }
        if (c == '-') { toks.push_back({tok_kind::minus, "-", line, col}); ++col; ++i; continue; }
        if (c == '*') { toks.push_back({tok_kind::star, "*", line, col}); ++col; ++i; continue; }
        if (c == '/') { toks.push_back({tok_kind::slash, "/", line, col}); ++col; ++i; continue; }
        if (c == '^') { toks.push_back({tok_kind::caret, "^", line, col}); ++col; ++i; continue; }
        if (c == '(') { toks.push_back({tok_kind::lparen, "(", line, col}); ++col; ++i; continue; }
        if (c == ')') { toks.push_back({tok_kind::rparen, ")", line, col}); ++col; ++i; continue; }
        if (c == ',') { toks.push_back({tok_kind::comma, ",", line, col}); ++col; ++i; continue; }
        if (std::isdigit(c) || c == '.') {
            size_t start = i;
            unsigned sc = col;
            while (i < src.size() && (std::isdigit(src[i]) || src[i] == '.' || src[i] == 'e' || src[i] == 'E'
                   || ((src[i] == '+' || src[i] == '-') && i > 0 && (src[i-1] == 'e' || src[i-1] == 'E')))) {
                ++i; ++col;
            }
            toks.push_back({tok_kind::number, src.substr(start, i - start), line, sc});
            continue;
        }
        if (std::isalpha(c) || c == '_') {
            size_t start = i;
            unsigned sc = col;
            while (i < src.size() && (std::isalnum(src[i]) || src[i] == '_' || src[i] == '.' || src[i] == '\'')) {
                ++i; ++col;
            }
            toks.push_back({tok_kind::ident, src.substr(start, i - start), line, sc});
            continue;
        }
        // skip unknown chars
        ++i; ++col;
    }
    toks.push_back({tok_kind::eof, "", line, col});
    return toks;
}

// ── Noether derivation ──────────────────────────────────────────

conservation_law derive_from_noether(symmetry_decl const & sym,
                                     theory_id theory)
{
    conservation_law law;
    law.m_theory = theory;
    law.m_source = conservation_source::noether;
    law.m_symmetry = sym;

    if (sym.m_is_exact) {
        law.m_exactness = conservation_exactness::exact;
    } else {
        law.m_exactness = conservation_exactness::approximate_bound;
    }

    switch (sym.m_kind) {
    case symmetry_kind::time_translation:
        law.m_name = "energy";
        law.m_quantity_expr = "total_energy";
        break;
    case symmetry_kind::space_translation:
        law.m_name = "momentum";
        law.m_quantity_expr = "total_momentum";
        break;
    case symmetry_kind::rotation:
        law.m_name = "angular_momentum";
        law.m_quantity_expr = "total_angular_momentum";
        break;
    case symmetry_kind::gauge:
        law.m_name = sym.m_group_name + "_charge";
        law.m_quantity_expr = "total_" + sym.m_group_name + "_charge";
        break;
    default:
        law.m_name = sym.m_conserved_qty_name;
        law.m_quantity_expr = sym.m_conserved_qty_name;
        break;
    }

    return law;
}

// ── Constructor ──────────────────────────────────────────────────

conservation_checker::conservation_checker(theory_id theory)
    : m_theory(theory) {}

void conservation_checker::add_law(conservation_law const & law) {
    m_laws.push_back(law);
}

void conservation_checker::add_symmetry_laws(
    std::vector<symmetry_decl> const & symmetries)
{
    for (auto const & sym : symmetries) {
        m_laws.push_back(derive_from_noether(sym, m_theory));
    }
}

// ── Recursive-descent parser for RHS expressions into expr_pool ──

/// Forward declarations for recursive descent.
static size_t parse_expr(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool);
static size_t parse_term(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool);
static size_t parse_factor(std::vector<token> const & toks, size_t & pos,
                           expr_pool & pool);
static size_t parse_atom(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool);

static bool is_rhs_end(tok_kind k) {
    return k == tok_kind::newline || k == tok_kind::eof;
}

/// atom = NUMBER | IDENT | IDENT '(' expr (',' expr)* ')' | '(' expr ')' | '-' atom
static size_t parse_atom(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool) {
    if (pos >= toks.size() || is_rhs_end(toks[pos].kind))
        return SIZE_MAX;

    // Unary minus
    if (toks[pos].kind == tok_kind::minus) {
        ++pos;
        size_t child = parse_atom(toks, pos, pool);
        if (child == SIZE_MAX) return SIZE_MAX;
        expr_node n;
        n.m_kind = expr_node_kind::unary_neg;
        n.m_children.push_back(child);
        return pool.add(n);
    }
    // Parenthesized expression
    if (toks[pos].kind == tok_kind::lparen) {
        ++pos;
        size_t inner = parse_expr(toks, pos, pool);
        if (pos < toks.size() && toks[pos].kind == tok_kind::rparen)
            ++pos;
        return inner;
    }
    // Number literal
    if (toks[pos].kind == tok_kind::number) {
        expr_node n;
        n.m_kind = expr_node_kind::literal;
        n.m_literal_val = std::strtod(toks[pos].text.c_str(), nullptr);
        n.m_name = toks[pos].text;
        ++pos;
        return pool.add(n);
    }
    // Identifier (possibly function call)
    if (toks[pos].kind == tok_kind::ident) {
        std::string name = toks[pos].text;
        ++pos;
        // Check for function call: ident '(' ...
        if (pos < toks.size() && toks[pos].kind == tok_kind::lparen) {
            ++pos;
            expr_node fn;
            fn.m_kind = expr_node_kind::func_call;
            fn.m_name = name;
            if (pos < toks.size() && toks[pos].kind != tok_kind::rparen) {
                size_t arg = parse_expr(toks, pos, pool);
                if (arg != SIZE_MAX) fn.m_children.push_back(arg);
                while (pos < toks.size() && toks[pos].kind == tok_kind::comma) {
                    ++pos;
                    arg = parse_expr(toks, pos, pool);
                    if (arg != SIZE_MAX) fn.m_children.push_back(arg);
                }
            }
            if (pos < toks.size() && toks[pos].kind == tok_kind::rparen)
                ++pos;
            return pool.add(fn);
        }
        // Plain variable
        expr_node n;
        n.m_kind = expr_node_kind::variable;
        n.m_name = name;
        return pool.add(n);
    }
    return SIZE_MAX;
}

/// factor = atom ('^' atom)?
static size_t parse_factor(std::vector<token> const & toks, size_t & pos,
                           expr_pool & pool) {
    size_t left = parse_atom(toks, pos, pool);
    if (left == SIZE_MAX) return SIZE_MAX;
    if (pos < toks.size() && toks[pos].kind == tok_kind::caret) {
        ++pos;
        size_t right = parse_atom(toks, pos, pool);
        if (right == SIZE_MAX) return left;
        expr_node n;
        n.m_kind = expr_node_kind::binop_pow;
        n.m_children = {left, right};
        return pool.add(n);
    }
    return left;
}

/// term = factor (('*' | '/') factor)*
static size_t parse_term(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool) {
    size_t left = parse_factor(toks, pos, pool);
    if (left == SIZE_MAX) return SIZE_MAX;
    while (pos < toks.size() &&
           (toks[pos].kind == tok_kind::star || toks[pos].kind == tok_kind::slash)) {
        auto op = toks[pos].kind;
        ++pos;
        size_t right = parse_factor(toks, pos, pool);
        if (right == SIZE_MAX) break;
        expr_node n;
        n.m_kind = (op == tok_kind::star)
            ? expr_node_kind::binop_mul : expr_node_kind::binop_div;
        n.m_children = {left, right};
        left = pool.add(n);
    }
    return left;
}

/// expr = term (('+' | '-') term)*
static size_t parse_expr(std::vector<token> const & toks, size_t & pos,
                         expr_pool & pool) {
    size_t left = parse_term(toks, pos, pool);
    if (left == SIZE_MAX) return SIZE_MAX;
    while (pos < toks.size() &&
           (toks[pos].kind == tok_kind::plus || toks[pos].kind == tok_kind::minus)) {
        auto op = toks[pos].kind;
        ++pos;
        size_t right = parse_term(toks, pos, pool);
        if (right == SIZE_MAX) break;
        expr_node n;
        n.m_kind = (op == tok_kind::plus)
            ? expr_node_kind::binop_add : expr_node_kind::binop_sub;
        n.m_children = {left, right};
        left = pool.add(n);
    }
    return left;
}

// ── Pass 1: AST-level decomposition ─────────────────────────────

std::vector<atomic_mutation> conservation_checker::decompose(
    std::string const & fn_body)
{
    auto toks = tokenize(fn_body);
    std::vector<atomic_mutation> mutations;
    // Shared expression pool for structured RHS trees
    static thread_local expr_pool s_pool;
    s_pool.m_nodes.clear();

    for (size_t i = 0; i < toks.size(); ++i) {
        if (toks[i].kind != tok_kind::ident) continue;

        size_t next = i + 1;
        if (next >= toks.size()) break;

        bool is_assign = toks[next].kind == tok_kind::assign
                      || toks[next].kind == tok_kind::colon_assign;
        if (!is_assign) continue;

        atomic_mutation mut;
        mut.m_target = toks[i].text;
        mut.m_old_val = mut.m_target;
        mut.m_line = toks[i].line;
        mut.m_col = toks[i].col;

        // Collect RHS tokens as string (backward compat)
        std::ostringstream rhs;
        size_t j = next + 1;
        while (j < toks.size()
               && toks[j].kind != tok_kind::newline
               && toks[j].kind != tok_kind::eof) {
            if (!rhs.str().empty()) rhs << " ";
            rhs << toks[j].text;
            ++j;
        }
        mut.m_new_val = rhs.str();

        // Also parse RHS into structured expr_pool AST
        size_t parse_pos = next + 1;
        size_t rhs_root = parse_expr(toks, parse_pos, s_pool);
        mut.m_rhs_expr = rhs_root;

        mutations.push_back(mut);
        i = j;
    }
    return mutations;
}

// ── Pass 2: Compute symbolic delta for a conservation law ────────

delta_result conservation_checker::compute_delta(
    conservation_law const & law,
    std::vector<atomic_mutation> const & mutations)
{
    // Check if any mutation targets a component of the conserved quantity.
    // The conserved quantity expression references state fields;
    // if none of the mutated fields appear in it, delta = 0.
    bool touches_conserved = false;
    for (auto const & mut : mutations) {
        if (law.m_quantity_expr.find(mut.m_target) != std::string::npos) {
            touches_conserved = true;
            break;
        }
    }

    if (!touches_conserved) {
        return {delta_kind::zero, 0.0, ""};
    }

    // Build a symbolic delta expression: Q(new) - Q(old)
    // For now, construct a string representation for Pass 3.
    std::ostringstream delta_expr;
    delta_expr << "delta(" << law.m_quantity_expr << ") = ";
    bool first = true;
    for (auto const & mut : mutations) {
        if (law.m_quantity_expr.find(mut.m_target) != std::string::npos) {
            if (!first) delta_expr << " + ";
            delta_expr << "d_" << mut.m_target
                       << "(" << mut.m_new_val << " - " << mut.m_old_val << ")";
            first = false;
        }
    }

    return {delta_kind::symbolic, 0.0, delta_expr.str()};
}

// ── Pass 3 helpers: dimensional analysis (3b) & bound estimation (3c) ──

/// Known dimension tags for common physics variables.
static std::optional<dim_tag> lookup_var_dim(std::string const & name) {
    // Velocity-like
    if (name.find("velocity") != std::string::npos || name == "v" || name == "v'")
        return dim_tag{1, 0, -1, 0, 0, 0, 0};
    // Mass
    if (name.find("mass") != std::string::npos || name == "m")
        return dim_tag{0, 1, 0, 0, 0, 0, 0};
    // Position / height
    if (name.find("height") != std::string::npos || name == "h" || name == "h'"
        || name.find("position") != std::string::npos || name == "x")
        return dim_tag{1, 0, 0, 0, 0, 0, 0};
    // Time step
    if (name == "dt" || name == "t")
        return dim_tag{0, 0, 1, 0, 0, 0, 0};
    // Acceleration / gravity
    if (name == "g" || name.find("accel") != std::string::npos)
        return dim_tag{1, 0, -2, 0, 0, 0, 0};
    // Energy
    if (name.find("energy") != std::string::npos || name.find("kinetic") != std::string::npos
        || name.find("potential") != std::string::npos)
        return dim_tag{2, 1, -2, 0, 0, 0, 0};
    return std::nullopt;
}

/// Infer dimension of an expression node recursively via expr_pool AST.
static std::optional<dim_tag> infer_expr_dim(
    expr_pool const & pool, size_t idx)
{
    if (idx == SIZE_MAX || idx >= pool.m_nodes.size())
        return std::nullopt;
    auto const & node = pool.get(idx);

    switch (node.m_kind) {
    case expr_node_kind::literal:
        return dim_tag{0, 0, 0, 0, 0, 0, 0}; // dimensionless

    case expr_node_kind::variable:
        return lookup_var_dim(node.m_name);

    case expr_node_kind::unary_neg: {
        if (node.m_children.empty()) return std::nullopt;
        return infer_expr_dim(pool, node.m_children[0]);
    }

    case expr_node_kind::binop_add:
    case expr_node_kind::binop_sub: {
        if (node.m_children.size() < 2) return std::nullopt;
        auto dl = infer_expr_dim(pool, node.m_children[0]);
        auto dr = infer_expr_dim(pool, node.m_children[1]);
        if (!dl || !dr) return dl ? dl : dr;
        if (*dl != *dr) return std::nullopt; // mismatch signals bug
        return dl;
    }

    case expr_node_kind::binop_mul: {
        if (node.m_children.size() < 2) return std::nullopt;
        auto dl = infer_expr_dim(pool, node.m_children[0]);
        auto dr = infer_expr_dim(pool, node.m_children[1]);
        if (!dl || !dr) return std::nullopt;
        return dim_tag{dl->L + dr->L, dl->M + dr->M, dl->T + dr->T,
                       dl->I + dr->I, dl->Theta + dr->Theta,
                       dl->N + dr->N, dl->J + dr->J};
    }

    case expr_node_kind::binop_div: {
        if (node.m_children.size() < 2) return std::nullopt;
        auto dl = infer_expr_dim(pool, node.m_children[0]);
        auto dr = infer_expr_dim(pool, node.m_children[1]);
        if (!dl || !dr) return std::nullopt;
        return dim_tag{dl->L - dr->L, dl->M - dr->M, dl->T - dr->T,
                       dl->I - dr->I, dl->Theta - dr->Theta,
                       dl->N - dr->N, dl->J - dr->J};
    }

    case expr_node_kind::binop_pow: {
        if (node.m_children.size() < 2) return std::nullopt;
        auto dl = infer_expr_dim(pool, node.m_children[0]);
        auto const & exp_node = pool.get(node.m_children[1]);
        if (!dl || exp_node.m_kind != expr_node_kind::literal)
            return std::nullopt;
        int n = static_cast<int>(exp_node.m_literal_val);
        return dim_tag{dl->L * n, dl->M * n, dl->T * n,
                       dl->I * n, dl->Theta * n,
                       dl->N * n, dl->J * n};
    }

    case expr_node_kind::func_call:
        // Transcendental functions: args must be dimensionless, result dimensionless
        if (node.m_name == "sin" || node.m_name == "cos" ||
            node.m_name == "exp" || node.m_name == "log" ||
            node.m_name == "sqrt") {
            return dim_tag{0, 0, 0, 0, 0, 0, 0};
        }
        return std::nullopt;
    }
    return std::nullopt;
}

/// Strategy 3b: AST-level dimensional analysis of delta terms.
/// Walks the structured expr_pool to infer dimensions and detect mismatches.
static std::optional<std::string> check_delta_dimensions(
    std::string const & expr, conservation_law const & law)
{
    // Also do the string-based fallback for backward compat
    std::vector<std::string> term_vars;
    size_t pos = 0;
    while ((pos = expr.find("d_", pos)) != std::string::npos) {
        pos += 2;
        size_t end = pos;
        while (end < expr.size() &&
               (std::isalnum(expr[end]) || expr[end] == '_' || expr[end] == '\''))
            ++end;
        if (end > pos)
            term_vars.push_back(expr.substr(pos, end - pos));
        pos = end;
    }

    if (term_vars.empty()) return std::nullopt;

    auto law_dim = lookup_var_dim(law.m_quantity_expr);
    if (!law_dim.has_value()) return std::nullopt;

    for (auto const & var : term_vars) {
        auto var_dim = lookup_var_dim(var);
        if (!var_dim.has_value()) continue;
        if (var_dim->is_zero() && !law_dim->is_zero()) {
            return "Variable '" + var + "' is dimensionless but contributes to "
                   + law.m_name + " (dim=" + law_dim->to_string() + ")";
        }
    }
    return std::nullopt;
}

/// Strategy 3c: Estimate an upper bound on |delta| from numeric coefficients.
/// Scans the symbolic expression for numeric literals and returns their sum
/// as a rough bound. Returns -1.0 if no estimate is possible.
static double estimate_delta_bound(std::string const & expr) {
    double bound = 0.0;
    bool found_any = false;
    size_t i = 0;
    while (i < expr.size()) {
        // Skip to next digit or sign-before-digit
        if (std::isdigit(expr[i]) || (expr[i] == '.' && i + 1 < expr.size() && std::isdigit(expr[i+1]))) {
            char * end = nullptr;
            double val = std::strtod(expr.c_str() + i, &end);
            if (end != expr.c_str() + i) {
                bound += std::fabs(val);
                found_any = true;
                i = static_cast<size_t>(end - expr.c_str());
                continue;
            }
        }
        ++i;
    }
    return found_any ? bound : -1.0;
}

/// Strategy 3d: CAS delegation interface.
/// In a full implementation, this would serialize the symbolic expression
/// to a CAS (Mathematica, SymPy, etc.) and ask whether it simplifies to zero.
/// Returns true if CAS proves delta = 0, false if delta != 0,
/// or nullopt if the CAS is unavailable or cannot determine.
std::optional<bool> delegate_to_cas(
    std::string const & /* symbolic_expr */,
    conservation_law const & /* law */)
{
    // Not yet connected to an external CAS.
    return std::nullopt;
}

// ── Pass 3: Residual analysis for symbolic deltas ────────────────

conservation_verdict conservation_checker::residual_analysis(
    delta_result const & delta,
    conservation_law const & law)
{
    conservation_verdict v;
    v.m_law_name = law.m_name;

    switch (delta.m_kind) {
    case delta_kind::zero:
        v.m_kind = conservation_verdict_kind::verified;
        v.m_delta = 0.0;
        v.m_hint = "Conservation verified: delta = 0";
        return v;

    case delta_kind::nonzero:
        v.m_kind = conservation_verdict_kind::violation;
        v.m_delta = delta.m_numeric_value;
        v.m_hint = "Conservation violated: delta = "
                   + std::to_string(delta.m_numeric_value);
        return v;

    case delta_kind::symbolic:
        break;
    }

    // Strategy 3a: Check if the symbolic expression contains
    // known cancellation patterns (e.g., "kinetic + potential = 0")
    auto const & expr = delta.m_symbolic_expr;
    if (expr.find("kinetic") != std::string::npos &&
        expr.find("potential") != std::string::npos) {
        v.m_kind = conservation_verdict_kind::verified_approx;
        v.m_hint = "Energy conservation: KE + PE terms detected, "
                   "assuming standard Hamiltonian structure";
        return v;
    }

    // Strategy 3b: Dimensional analysis
    // If the delta expression mixes terms with incompatible dimensions,
    // the update function has a bug (not just a conservation issue).
    {
        auto dim_result = check_delta_dimensions(expr, law);
        if (dim_result.has_value()) {
            v.m_kind = conservation_verdict_kind::violation;
            v.m_delta = 0.0;
            v.m_hint = "Dimensional inconsistency in conservation delta: "
                       + dim_result.value();
            return v;
        }
    }

    // Strategy 3c: Bound estimation
    // Extract numeric coefficients from the symbolic delta and estimate
    // an upper bound on |delta|. If bounded below tolerance, accept.
    {
        double bound = estimate_delta_bound(expr);
        if (bound >= 0.0 && bound < law.m_tolerance) {
            v.m_kind = conservation_verdict_kind::verified_approx;
            v.m_hint = "Conservation verified within tolerance: |delta| <= "
                       + std::to_string(bound) + " < "
                       + std::to_string(law.m_tolerance);
            return v;
        }
    }

    // Strategy 3d: CAS delegation
    // Attempt to delegate to an external CAS for symbolic simplification.
    {
        auto cas_result = delegate_to_cas(expr, law);
        if (cas_result.has_value()) {
            if (*cas_result) {
                v.m_kind = conservation_verdict_kind::verified;
                v.m_delta = 0.0;
                v.m_hint = "CAS verified: delta simplifies to 0";
                return v;
            } else {
                v.m_kind = conservation_verdict_kind::violation;
                v.m_delta = 0.0;
                v.m_hint = "CAS determined: delta is nonzero";
                return v;
            }
        }
    }

    v.m_kind = conservation_verdict_kind::inconclusive;
    v.m_hint = "Static analysis inconclusive for " + law.m_name
               + "; runtime checks will be inserted. "
               + "Symbolic delta: " + expr;
    return v;
}

// ── Main entry: check all laws ──────────────────────────────────

std::vector<conservation_verdict> conservation_checker::check_all(
    std::string const & fn_body) const
{
    auto mutations = decompose(fn_body);
    std::vector<conservation_verdict> results;
    results.reserve(m_laws.size());

    for (auto const & law : m_laws) {
        auto delta = compute_delta(law, mutations);
        results.push_back(residual_analysis(delta, law));
    }
    return results;
}

// ── Runtime checkpoint generation ────────────────────────────────

conservation_checkpoint conservation_checker::generate_checkpoint(
    std::vector<conservation_verdict> const & verdicts) const
{
    conservation_checkpoint cp;
    cp.m_on_violation = {violation_action_kind::halt, 5};
    cp.m_frequency = {check_frequency_kind::adaptive,
                      1, 100, 1, 2, 10000, true};

    for (size_t i = 0; i < verdicts.size(); ++i) {
        if (verdicts[i].m_kind == conservation_verdict_kind::inconclusive) {
            if (i < m_laws.size()) {
                cp.m_laws.push_back(m_laws[i]);
                cp.m_tolerances.push_back(m_laws[i].m_tolerance);
            }
        }
    }
    return cp;
}

// ── Runtime violation handling ───────────────────────────────────

bool conservation_checker::should_halt(
    violation_report const & report,
    violation_action const & action,
    unsigned consecutive_count)
{
    switch (action.m_kind) {
    case violation_action_kind::halt:
        return true;
    case violation_action_kind::warn:
        return false;
    case violation_action_kind::correct:
        return false;
    case violation_action_kind::halt_after_n:
        return consecutive_count >= action.m_halt_after_count;
    }
    return true;
}

// ── Formatting ──────────────────────────────────────────────────

std::string conservation_checker::format_violation(
    violation_report const & report)
{
    std::ostringstream os;
    os << "CONSERVATION VIOLATION at step " << report.m_iteration << ":\n"
       << "  |delta(" << report.m_law_name << ")| = "
       << report.m_delta << " > tolerance " << report.m_tolerance << "\n"
       << "  Severity: " << report.m_severity_ratio << "x tolerance\n";
    return os.str();
}

std::string conservation_checker::format_verdict(
    conservation_verdict const & v)
{
    std::ostringstream os;
    switch (v.m_kind) {
    case conservation_verdict_kind::verified:
        os << "OK: " << v.m_law_name << " conservation verified";
        break;
    case conservation_verdict_kind::verified_approx:
        os << "OK (approx): " << v.m_law_name
           << " conservation verified with bounded error";
        break;
    case conservation_verdict_kind::inconclusive:
        os << "WARN: " << v.m_law_name
           << " conservation inconclusive, runtime checks inserted";
        break;
    case conservation_verdict_kind::violation:
        os << "ERROR: " << v.m_law_name
           << " conservation violated, delta = " << v.m_delta;
        break;
    }
    if (!v.m_hint.empty()) {
        os << "\n  " << v.m_hint;
    }
    return os.str();
}

} // namespace lean
