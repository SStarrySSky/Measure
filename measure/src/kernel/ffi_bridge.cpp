/*
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Lean4 FFI bridge for the Measure kernel extension.
Implements all @[extern] functions declared in Measure.Kernel.FFI.
*/

#if __has_include(<lean/lean.h>)
#include <lean/lean.h>
#else
// Standalone build without Lean runtime — provide minimal FFI stubs
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <cstdlib>

#define LEAN_EXPORT

// Basic Lean object types
typedef void lean_object;
typedef lean_object * b_lean_obj_arg;
typedef lean_object * lean_obj_arg;
typedef lean_object * lean_obj_res;
typedef uint8_t      uint8;
typedef uint32_t     uint32;
typedef size_t       usize;

// External class for opaque types
typedef struct {
    void (*m_finalize)(void *);
    void (*m_foreach)(void *, b_lean_obj_arg);
} lean_external_class;

// String operations
inline lean_object * lean_mk_string(const char *) { return nullptr; }
inline const char * lean_string_cstr(b_lean_obj_arg) { return ""; }
inline size_t lean_string_size(b_lean_obj_arg) { return 1; }
inline lean_object * lean_mk_string_from_bytes(const char *, size_t) { return nullptr; }

// Nat operations
inline lean_object * lean_unsigned_to_nat(unsigned) { return nullptr; }
inline unsigned lean_nat_to_uint32(b_lean_obj_arg) { return 0; }

// External object operations
inline lean_external_class * lean_register_external_class(
    void (*finalize)(void *), void (*foreach_fn)(void *, b_lean_obj_arg)) {
    auto * cls = (lean_external_class *)malloc(sizeof(lean_external_class));
    cls->m_finalize = finalize;
    cls->m_foreach = foreach_fn;
    return cls;
}
inline lean_object * lean_alloc_external(lean_external_class *, void * data) { return (lean_object *)data; }
inline void * lean_get_external_data(b_lean_obj_arg o) { return (void *)o; }

// IO result
inline lean_object * lean_io_result_mk_ok(lean_obj_arg a) { return a; }

// Boxing
inline lean_object * lean_box(size_t n) { return (lean_object *)(uintptr_t)((n << 1) | 1); }
inline size_t lean_unbox(b_lean_obj_arg o) { return ((uintptr_t)o) >> 1; }

// Array operations
inline lean_object * lean_mk_empty_array() { return nullptr; }
inline lean_object * lean_mk_array(lean_obj_arg, lean_obj_arg) { return nullptr; }
inline lean_object * lean_array_push(lean_obj_arg a, lean_obj_arg) { return a; }
inline size_t lean_array_size(b_lean_obj_arg) { return 0; }
inline lean_object * lean_array_get_core(b_lean_obj_arg, size_t) { return nullptr; }

// Unbox uint32
inline uint32_t lean_unbox_uint32(b_lean_obj_arg o) { return (uint32_t)((uintptr_t)o >> 1); }

// Constructor allocation (for tuples/inductive types)
inline lean_object * lean_alloc_ctor(unsigned, unsigned, unsigned) {
    // Allocate enough space for a small object with scalar fields
    return (lean_object *)calloc(1, 64);
}
inline void lean_ctor_set(lean_object * o, unsigned i, lean_object * v) {
    if (o) ((lean_object **)o)[i] = v;
}

// Box/unbox uint64
inline lean_object * lean_box_uint64(uint64_t n) { return (lean_object *)(uintptr_t)n; }
inline uint64_t lean_unbox_uint64(b_lean_obj_arg o) { return (uint64_t)(uintptr_t)o; }

// Reference counting (no-ops in standalone mode)
inline void lean_inc(lean_object *) {}
inline void lean_dec(lean_object *) {}
inline void lean_inc_ref(lean_object *) {}
inline void lean_dec_ref(lean_object *) {}

// Provide empty namespace lean so `using namespace lean;` compiles
namespace lean {}
#endif
#include "kernel/approx_eq.h"
#include "kernel/epsilon_tracker.h"
#include "kernel/measure_metadata.h"
#include "kernel/theory_module.h"
#include "kernel/theory_graph.h"
#include "kernel/conservation.h"
#include "kernel/is_approx_eq.h"
#include "kernel/rigor_propagation.h"
#include <string>
#include <vector>
#include <memory>

using namespace lean;

// ============================================================
// Helper: Lean string <-> std::string
// ============================================================

static std::string lean_string_to_std(b_lean_obj_arg s) {
    return std::string(lean_string_cstr(s), lean_string_size(s) - 1);
}

static lean_obj_res std_string_to_lean(std::string const & s) {
    return lean_mk_string_from_bytes(s.data(), s.size());
}

// ============================================================
// External class: epsilon_val
// ============================================================

static void epsilon_val_finalizer(void * ptr) {
    delete static_cast<epsilon_val *>(ptr);
}
static void epsilon_val_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_epsilon_val_class = nullptr;

static lean_external_class * get_epsilon_val_class() {
    if (!g_epsilon_val_class)
        g_epsilon_val_class = lean_register_external_class(
            epsilon_val_finalizer, epsilon_val_foreach);
    return g_epsilon_val_class;
}

static lean_obj_res mk_epsilon_val_obj(epsilon_val const & ev) {
    return lean_alloc_external(get_epsilon_val_class(), new epsilon_val(ev));
}

static epsilon_val const & to_epsilon_val(b_lean_obj_arg o) {
    return *static_cast<epsilon_val *>(lean_get_external_data(o));
}

// ============================================================
// External class: measure_metadata
// ============================================================

static void metadata_finalizer(void * ptr) {
    delete static_cast<measure_metadata *>(ptr);
}
static void metadata_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_metadata_class = nullptr;

static lean_external_class * get_metadata_class() {
    if (!g_metadata_class)
        g_metadata_class = lean_register_external_class(
            metadata_finalizer, metadata_foreach);
    return g_metadata_class;
}

static lean_obj_res mk_metadata_obj(measure_metadata const & m) {
    return lean_alloc_external(get_metadata_class(), new measure_metadata(m));
}

static measure_metadata const & to_metadata(b_lean_obj_arg o) {
    return *static_cast<measure_metadata *>(lean_get_external_data(o));
}

// ============================================================
// External class: theory_registry
// ============================================================

static void registry_finalizer(void * ptr) {
    delete static_cast<theory_registry *>(ptr);
}
static void registry_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_registry_class = nullptr;

static lean_external_class * get_registry_class() {
    if (!g_registry_class)
        g_registry_class = lean_register_external_class(
            registry_finalizer, registry_foreach);
    return g_registry_class;
}

static lean_obj_res mk_registry_obj(theory_registry * r) {
    return lean_alloc_external(get_registry_class(), r);
}

static theory_registry & to_registry(b_lean_obj_arg o) {
    return *static_cast<theory_registry *>(lean_get_external_data(o));
}

// ============================================================
// External class: theory_graph
// ============================================================

// theory_graph stores a reference to theory_registry, so we wrap
// both together to ensure lifetime safety.
struct theory_graph_wrapper {
    theory_registry * m_registry;  // not owned, must outlive
    theory_graph      m_graph;
    theory_graph_wrapper(theory_registry & reg)
        : m_registry(&reg), m_graph(reg) {}
};

static void graph_finalizer(void * ptr) {
    delete static_cast<theory_graph_wrapper *>(ptr);
}
static void graph_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_graph_class = nullptr;

static lean_external_class * get_graph_class() {
    if (!g_graph_class)
        g_graph_class = lean_register_external_class(
            graph_finalizer, graph_foreach);
    return g_graph_class;
}

static theory_graph & to_graph(b_lean_obj_arg o) {
    return static_cast<theory_graph_wrapper *>(
        lean_get_external_data(o))->m_graph;
}

// ============================================================
// External class: conservation_checker
// ============================================================

static void conservation_finalizer(void * ptr) {
    delete static_cast<conservation_checker *>(ptr);
}
static void conservation_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_conservation_class = nullptr;

static lean_external_class * get_conservation_class() {
    if (!g_conservation_class)
        g_conservation_class = lean_register_external_class(
            conservation_finalizer, conservation_foreach);
    return g_conservation_class;
}

static conservation_checker & to_conservation(b_lean_obj_arg o) {
    return *static_cast<conservation_checker *>(lean_get_external_data(o));
}

// ============================================================
// External class: approx_eq_checker
// ============================================================

static void approx_finalizer(void * ptr) {
    delete static_cast<approx_eq_checker *>(ptr);
}
static void approx_foreach(void *, b_lean_obj_arg) {}
static lean_external_class * g_approx_class = nullptr;

static lean_external_class * get_approx_class() {
    if (!g_approx_class)
        g_approx_class = lean_register_external_class(
            approx_finalizer, approx_foreach);
    return g_approx_class;
}

static approx_eq_checker & to_approx(b_lean_obj_arg o) {
    return *static_cast<approx_eq_checker *>(lean_get_external_data(o));
}

// ============================================================
// extern "C" — epsilon_val functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_zero(lean_obj_arg /* unit */) {
    return mk_epsilon_val_obj(epsilon_val::zero());
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_one(lean_obj_arg /* unit */) {
    return mk_epsilon_val_obj(epsilon_val::one());
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_inf(lean_obj_arg /* unit */) {
    return mk_epsilon_val_obj(epsilon_val::inf());
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_make(uint64_t num, uint64_t den) {
    if (den == 0) return mk_epsilon_val_obj(epsilon_val::inf());
    return mk_epsilon_val_obj(epsilon_val::make(num, den));
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_epsilon_is_zero(b_lean_obj_arg e) {
    return to_epsilon_val(e).is_zero() ? 1 : 0;
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_epsilon_is_inf(b_lean_obj_arg e) {
    return to_epsilon_val(e).is_inf() ? 1 : 0;
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_epsilon_leq(b_lean_obj_arg a, b_lean_obj_arg b) {
    return to_epsilon_val(a).leq(to_epsilon_val(b)) ? 1 : 0;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    return mk_epsilon_val_obj(
        to_epsilon_val(a).add(to_epsilon_val(b)));
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_mul(b_lean_obj_arg a, b_lean_obj_arg b) {
    return mk_epsilon_val_obj(
        to_epsilon_val(a).mul(to_epsilon_val(b)));
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_max(b_lean_obj_arg a, b_lean_obj_arg b) {
    return mk_epsilon_val_obj(
        to_epsilon_val(a).max(to_epsilon_val(b)));
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_epsilon_to_string(b_lean_obj_arg e) {
    return std_string_to_lean(to_epsilon_val(e).to_string());
}

extern "C" LEAN_EXPORT uint64_t
lean_measure_epsilon_numerator(b_lean_obj_arg e) {
    return to_epsilon_val(e).m_numerator;
}

extern "C" LEAN_EXPORT uint64_t
lean_measure_epsilon_denominator(b_lean_obj_arg e) {
    return to_epsilon_val(e).m_denominator;
}

// ============================================================
// extern "C" — measure_metadata functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_metadata_default(lean_obj_arg /* unit */) {
    return mk_metadata_obj(measure_metadata::default_meta());
}

extern "C" LEAN_EXPORT uint32_t
lean_measure_metadata_get_theory(b_lean_obj_arg m) {
    return to_metadata(m).m_theory;
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_metadata_get_rigor(b_lean_obj_arg m) {
    return static_cast<uint8_t>(to_metadata(m).m_rigor);
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_metadata_get_epsilon_bound(b_lean_obj_arg m) {
    return mk_epsilon_val_obj(to_metadata(m).m_epsilon_bound);
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_metadata_is_default(b_lean_obj_arg m) {
    return to_metadata(m).is_default() ? 1 : 0;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_metadata_set_theory(b_lean_obj_arg m, uint32_t t) {
    measure_metadata copy = to_metadata(m);
    copy.m_theory = t;
    return mk_metadata_obj(copy);
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_metadata_set_rigor(b_lean_obj_arg m, uint8_t r) {
    measure_metadata copy = to_metadata(m);
    copy.m_rigor = static_cast<rigor_level>(r);
    return mk_metadata_obj(copy);
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_metadata_set_epsilon_bound(b_lean_obj_arg m, b_lean_obj_arg e) {
    measure_metadata copy = to_metadata(m);
    copy.m_epsilon_bound = to_epsilon_val(e);
    return mk_metadata_obj(copy);
}

// ============================================================
// extern "C" — theory_registry functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_theory_registry_new(lean_obj_arg /* unit */) {
    return mk_registry_obj(new theory_registry());
}

extern "C" LEAN_EXPORT uint32_t
lean_measure_theory_registry_register(
    b_lean_obj_arg reg, b_lean_obj_arg name,
    b_lean_obj_arg parent_ids,
    uint8_t rigor, uint64_t max_eps_num, uint64_t max_eps_den)
{
    auto & r = to_registry(reg);
    std::string n = lean_string_to_std(name);

    // Convert Lean Array TheoryId to std::vector
    std::vector<theory_id> parents;
    size_t len = lean_array_size(parent_ids);
    for (size_t i = 0; i < len; ++i) {
        lean_obj_arg elem = lean_array_get_core(parent_ids, i);
        parents.push_back(lean_unbox_uint32(elem));
    }

    epsilon_val max_eps = (max_eps_den == 0)
        ? epsilon_val::inf()
        : epsilon_val::make(max_eps_num, max_eps_den);

    return r.register_theory(
        n, parents, static_cast<rigor_level>(rigor), max_eps);
}

extern "C" LEAN_EXPORT uint32_t
lean_measure_theory_registry_find_by_name(
    b_lean_obj_arg reg, b_lean_obj_arg name)
{
    return to_registry(reg).find_by_name(lean_string_to_std(name));
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_theory_registry_is_accessible(
    b_lean_obj_arg reg, uint32_t from_, uint32_t target)
{
    return to_registry(reg).is_accessible(from_, target) ? 1 : 0;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_theory_registry_get_name(
    b_lean_obj_arg reg, uint32_t id)
{
    auto const * mod = to_registry(reg).find(id);
    if (!mod) return std_string_to_lean("");
    return std_string_to_lean(mod->m_name);
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_theory_registry_set_relation(
    b_lean_obj_arg reg, uint32_t a, uint32_t b, uint8_t rel)
{
    try {
        to_registry(reg).set_relation(
            a, b, static_cast<theory_relation>(rel));
        return 1;
    } catch (...) {
        return 0;
    }
}

// ============================================================
// extern "C" — theory_graph functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_theory_graph_new(b_lean_obj_arg reg) {
    auto & r = to_registry(reg);
    auto * w = new theory_graph_wrapper(r);
    return lean_alloc_external(get_graph_class(), w);
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_theory_graph_are_conflicting(
    b_lean_obj_arg g, uint32_t a, uint32_t b)
{
    return to_graph(g).are_conflicting(a, b) ? 1 : 0;
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_theory_graph_check_compat(
    b_lean_obj_arg g, uint32_t a, uint32_t b)
{
    auto result = to_graph(g).check_compatibility(a, b);
    return static_cast<uint8_t>(result.m_status);
}

extern "C" LEAN_EXPORT uint64_t
lean_measure_theory_graph_conflict_count(b_lean_obj_arg g) {
    return static_cast<uint64_t>(to_graph(g).conflict_count());
}

extern "C" LEAN_EXPORT uint64_t
lean_measure_theory_graph_bridge_count(b_lean_obj_arg g) {
    return static_cast<uint64_t>(to_graph(g).bridge_count());
}

// ============================================================
// extern "C" — conservation_checker functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_conservation_checker_new(uint32_t theory) {
    auto * c = new conservation_checker(theory);
    return lean_alloc_external(get_conservation_class(), c);
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_conservation_add_law(
    b_lean_obj_arg c, b_lean_obj_arg name, b_lean_obj_arg qty_expr)
{
    conservation_law law;
    law.m_name = lean_string_to_std(name);
    law.m_quantity_expr = lean_string_to_std(qty_expr);
    to_conservation(c).add_law(law);
    return 1;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_conservation_check_all(
    b_lean_obj_arg c, b_lean_obj_arg fn_body)
{
    auto verdicts = to_conservation(c).check_all(
        lean_string_to_std(fn_body));

    lean_obj_res arr = lean_mk_empty_array();
    for (auto const & v : verdicts) {
        std::string s = conservation_checker::format_verdict(v);
        lean_obj_res str = std_string_to_lean(s);
        arr = lean_array_push(arr, str);
    }
    return arr;
}

extern "C" LEAN_EXPORT uint32_t
lean_measure_conservation_law_count(b_lean_obj_arg c) {
    return static_cast<uint32_t>(to_conservation(c).laws().size());
}

// ============================================================
// extern "C" — approx_eq_checker functions
// ============================================================

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_approx_eq_checker_new(lean_obj_arg /* unit */) {
    auto * c = new approx_eq_checker();
    return lean_alloc_external(get_approx_class(), c);
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_approx_eq_try_numeric(
    b_lean_obj_arg c, double val_a, double val_b)
{
    auto result = to_approx(c).try_numeric_approx(val_a, val_b);
    // Return (Bool, UInt64, UInt64) as a tuple
    lean_obj_res tup = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(tup, 0, lean_box(result.m_is_approx_eq ? 1 : 0));
    lean_ctor_set(tup, 1, lean_box_uint64(result.m_epsilon.m_numerator));
    lean_ctor_set(tup, 2, lean_box_uint64(result.m_epsilon.m_denominator));
    return tup;
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_approx_eq_has_overflow(b_lean_obj_arg c) {
    return to_approx(c).tracker().has_overflow() ? 1 : 0;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_approx_eq_reset(b_lean_obj_arg c) {
    to_approx(c).reset();
    return lean_box(0);
}

// ============================================================
// extern "C" — rigor propagation functions
// ============================================================

extern "C" LEAN_EXPORT uint8_t
lean_measure_rigor_propagate(uint8_t a, uint8_t b) {
    return static_cast<uint8_t>(propagate_rigor(
        static_cast<rigor_level>(a),
        static_cast<rigor_level>(b)));
}

extern "C" LEAN_EXPORT uint8_t
lean_measure_rigor_is_compatible(uint8_t declared, uint8_t actual) {
    return is_rigor_compatible(
        static_cast<rigor_level>(declared),
        static_cast<rigor_level>(actual)) ? 1 : 0;
}

extern "C" LEAN_EXPORT lean_obj_res
lean_measure_rigor_to_string(uint8_t r) {
    return std_string_to_lean(
        rigor_to_string(static_cast<rigor_level>(r)));
}
