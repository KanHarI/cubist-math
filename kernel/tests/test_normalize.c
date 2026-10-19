/* Full normalization must follow the shared graph, and a cached result must
 * survive only as long as the exact syntax and referenced state do. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>
#include <time.h>

static cc_term raw(cc_kernel *k, cc_term_kind kind, uint32_t name, cc_term a, cc_term b) {
    cc_term t = cc_kernel_term(k, kind, name, a, b, 0, 0);
    assert(t);
    return t;
}

static cc_judgement_info info(cc_kernel *k, cc_judgement_id id) {
    cc_judgement_info result;
    assert(id && cc_kernel_judgement(k, id, &result));
    return result;
}

static uint64_t steps(cc_kernel *k) {
    cc_work_counters work;
    cc_kernel_work(k, &work);
    return work.query_steps;
}

/* Forty shared sums have 2^40 leaves when expanded, but normalization takes
 * linear work. Check a derived type and Step(Normalize), with syntax interning
 * both on and off: the cache follows handles, not structural hash guesses. */
static void shared_graph(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_judgement_id type = cc_instr_unit(k);
    for (unsigned i = 0; i < 40; ++i)
        type = cc_instr_sum(k, type, type);
    cc_term source = info(k, type).term;
    cc_kernel_set_step_budget(k, 1000);
    uint64_t before = steps(k);
    cc_term result = cc_kernel_normalize(k, source);
    uint64_t cold = steps(k) - before;
    assert(result && ck_alpha_equal(k, result, source));
    assert(cold >= 40 && cold < 300);
    before = steps(k);
    assert(cc_kernel_normalize(k, source) == result);
    assert(steps(k) - before == 1);
    cc_judgement_id equality = cc_instr_step(k, cc_instr_refl(k, type), 1, NULL, 0, CC_STEP_NORMALIZE);
    assert(info(k, equality).other == result);
    /* Returning a cached answer still checks the instruction's own budget. */
    cc_kernel_set_step_budget(k, 1);
    assert(!cc_instr_step(k, cc_instr_refl(k, type), 0, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 1000);
    /* A warm query also observes an expired deadline. */
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { }
    assert(!cc_kernel_normalize(k, source));
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_clear_error(k);
    cc_kernel_set_deadline_ms(k, 0);
    assert(cc_kernel_normalize(k, source) == result);
    printf("shared normalization (interning %s): %llu cold steps, 1 warm step\n",
           optimizations ? "on" : "off", (unsigned long long)cold);
    cc_kernel_free(k);
}

/* Computing children creates a new parent after the checkpoint. Even when
 * the input survives, its cached result may be discarded or relocated. */
static cc_term reducible_sum(cc_kernel *k) {
    cc_judgement_id unit = cc_instr_unit(k), universe = cc_instr_universe(k, ck_level_constant(k, 0, 0));
    cc_entry_id x = cc_instr_extend(k, universe, 100);
    cc_judgement_id identity = cc_instr_lambda(k, x, cc_instr_variable(k, x));
    return info(k, cc_instr_sum(k, cc_instr_apply(k, identity, unit), unit)).term;
}

static void rollback_and_reuse(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term source = reducible_sum(k);
    cc_kernel_checkpoint(k);
    size_t base = k->count;
    cc_term normal = cc_kernel_normalize(k, source);
    assert(normal >= base);
    /* Also cache a key that rollback will discard. */
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), point = raw(k, CC_POINT, 0, 0, 0);
    cc_term identity = raw(k, CC_LAM, 200, unit, raw(k, CC_VAR, 200, 0, 0));
    cc_term dead = raw(k, CC_APP, 0, identity, point);
    assert(cc_kernel_normalize(k, dead) == point);
    cc_kernel_rollback(k);
    cc_term replacement = raw(k, CC_VOID, 0, 0, 0);
    assert(replacement == normal);
    while (k->count <= dead)
        raw(k, CC_VAR, 1000 + (uint32_t)k->count, 0, 0);
    /* The old key's slot now contains a different normal term. */
    assert(cc_kernel_normalize(k, dead) == dead);
    cc_term again = cc_kernel_normalize(k, source);
    assert(again && again != replacement && k->nodes[again].kind == CC_SUM);
    assert(k->nodes[k->nodes[again].child[0]].kind == CC_UNIT);
    cc_kernel_free(k);
}

static void compaction(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term source = reducible_sum(k);
    cc_kernel_checkpoint(k);
    for (unsigned i = 0; i < 300; ++i)
        raw(k, CC_VAR, 1000 + i, 0, 0);
    cc_term normal = cc_kernel_normalize(k, source);
    cc_judgement_id unit = cc_instr_unit(k);
    cc_term reference = info(k, cc_instr_define(k, 300, cc_instr_sum(k, unit, unit))).term;
    assert(cc_kernel_normalize(k, reference) == normal);
    size_t allocated = k->count;
    assert(cc_kernel_commit_checkpoint(k));
    assert(k->count + 250 < allocated);
    reference = cc_kernel_relocated(k, reference);
    cc_term relocated = cc_kernel_relocated(k, normal);
    assert(relocated && relocated != normal);
    /* Refill discarded handles with unrelated, normal syntax as well. */
    while (k->count <= allocated)
        raw(k, CC_VAR, 2000 + (uint32_t)k->count, 0, 0);
    assert(cc_kernel_normalize(k, source) == relocated);
    assert(cc_kernel_normalize(k, reference) == relocated);
    assert(cc_kernel_normalize(k, normal) == normal);
    cc_kernel_free(k);
}

/* A completed child can allocate and cache its result before a later child
 * fails. Clear-error must not turn the failed parent into an answer; rollback
 * must drop the completed child's forward reference too. */
static void failed_parent(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term child = reducible_sum(k);
    cc_term missing = raw(k, CC_DEFREF, 9999, 0, 0);
    cc_term parent = raw(k, CC_SUM, 0, child, missing);
    cc_kernel_checkpoint(k);
    size_t base = k->count;
    assert(!cc_kernel_normalize(k, parent) && k->error[0]);
    assert(k->count > base && k->normal_cache[child] >= base);
    assert(!k->normal_cache[parent] && !k->recursion);
    cc_kernel_clear_error(k);
    assert(!cc_kernel_normalize(k, parent) && k->error[0]);
    cc_kernel_rollback(k);
    cc_term replacement = raw(k, CC_VOID, 0, 0, 0);
    assert(replacement == base);
    assert(cc_kernel_normalize(k, child) != replacement);
    cc_kernel_free(k);
}

/* Names and dimension restrictions remain part of syntax identity: an open
 * result cannot become an answer for a differently substituted/bound term. */
static void scope_and_restriction(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), x = raw(k, CC_VAR, 10, 0, 0), y = raw(k, CC_VAR, 11, 0, 0);
    cc_term identity = raw(k, CC_LAM, 12, unit, raw(k, CC_VAR, 12, 0, 0));
    cc_term applied = raw(k, CC_APP, 0, identity, x);
    assert(cc_kernel_normalize(k, applied) == x);
    cc_term changed = cc_kernel_rename(k, applied, false, 10, 11);
    assert(cc_kernel_normalize(k, changed) == y);
    cc_term sum = raw(k, CC_SUM, 0, unit, unit);
    cc_term bound = raw(k, CC_LAM, 10, unit, raw(k, CC_INL, 0, sum, applied));
    cc_term normal = cc_kernel_normalize(k, bound);
    assert(k->nodes[k->nodes[normal].child[1]].child[1] == x);
    cc_term path = ck_make(k, CC_PATH, 1, unit, x, y, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), raw(k, CC_VAR, 13, 0, 0), path);
    assert(cc_kernel_normalize(k, at) == at);
    assert(cc_kernel_normalize(k, cc_kernel_endpoint_term(k, at, 0, 0)) == x);
    assert(cc_kernel_normalize(k, cc_kernel_endpoint_term(k, at, 0, 1)) == y);
    assert(cc_kernel_normalize(k, at) == at);
    cc_kernel_free(k);
}

/* Path beta substitutes a dimension through a shared graph too. Forty
 * shared sums must not turn that substitution into 2^40 recursive visits. */
static void shared_dimension_substitution(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_judgement_id universe = cc_instr_universe(k, ck_level_constant(k, 0, 0));
    cc_judgement_id unit = cc_instr_unit(k), empty = cc_instr_void(k);
    cc_entry_id i = cc_instr_dimension(k, 0);
    cc_judgement_id path = cc_instr_path(k, i, universe, unit, empty);
    cc_entry_id p = cc_instr_extend(k, path, 100);
    cc_judgement_id type = cc_instr_path_apply(k, cc_instr_variable(k, p), i, 0);
    for (unsigned n = 0; n < 40; ++n)
        type = cc_instr_sum(k, type, type);
    cc_term source = info(k, type).term;
    cc_kernel_set_step_budget(k, 5000);
    uint64_t before = steps(k);
    cc_term left = cc_kernel_endpoint_term(k, source, 0, 0);
    assert(left && steps(k) - before < 1000);
    cc_term right = cc_kernel_endpoint_term(k, source, 0, 1);
    assert(right && left != right);
    cc_term l = cc_kernel_normalize(k, left), r = cc_kernel_normalize(k, right);
    assert(l && r);
    for (unsigned n = 0; n < 40; ++n) {
        assert(k->nodes[l].kind == CC_SUM && k->nodes[r].kind == CC_SUM);
        assert(k->nodes[l].child[0] == k->nodes[l].child[1]);
        assert(k->nodes[r].child[0] == k->nodes[r].child[1]);
        l = k->nodes[l].child[0]; r = k->nodes[r].child[0];
    }
    assert(k->nodes[l].kind == CC_UNIT && k->nodes[r].kind == CC_VOID);
    before = steps(k);
    cc_kernel_set_step_budget(k, 1);
    assert(cc_kernel_endpoint_term(k, source, 0, 0) == left && steps(k) - before == 1);
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { }
    assert(!cc_kernel_endpoint_term(k, source, 0, 0));
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_clear_error(k);
    cc_kernel_set_deadline_ms(k, 0);
    cc_kernel_set_step_budget(k, 5000);
    assert(cc_kernel_endpoint_term(k, source, 0, 0) == left);
    cc_kernel_free(k);
}

static void dimension_cache_scope_and_rollback(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), point = raw(k, CC_POINT, 0, 0, 0);
    cc_term path = ck_make(k, CC_PATH, 2, unit, point, point, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 100), path);
    cc_term line = raw(k, CC_PLAM, 1, unit, at);
    cc_formula j;
    cc_init(&j, CC_INTERVAL);
    assert(cc_generator(&j, 1, true) == CC_OK);
    cc_term renamed = ck_dimension_substitute(k, line, 0, &j);
    assert(renamed && k->nodes[renamed].payload != 1);
    assert(ck_free_dims(k, renamed) & (UINT64_C(1) << 1));
    assert(ck_dimension_substitute(k, line, 0, &j) == renamed);
    cc_clear(&j);

    cc_kernel_checkpoint(k);
    cc_term old = cc_kernel_endpoint_term(k, at, 0, 0);
    assert(old);
    cc_kernel_rollback(k);
    while (k->count <= old)
        raw(k, CC_VAR, 1000 + (uint32_t)k->count, 0, 0);
    cc_term again = cc_kernel_endpoint_term(k, at, 0, 0);
    assert(again && again != old && cc_kernel_normalize(k, again) == point);
    cc_kernel_free(k);
}

/* The replacement formula may itself live in the formula arena. A new
 * formula in the first child can grow that arena before the second child
 * uses the replacement, so recursive substitution must retain its value. */
static void substitution_grows_formula_arena(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), empty = raw(k, CC_VOID, 0, 0, 0);
    cc_term path = ck_make(k, CC_PATH, 3, ck_universe_at(k, 0), unit, empty, 0);
    cc_clause both = {3, 0};
    cc_formula interval = {CC_INTERVAL, &both, 1, 1};
    cc_term p = ck_var(k, 100);
    cc_term first = raw(k, CC_PAPP, ck_formula(k, &interval), p, path);
    cc_term second = raw(k, CC_PAPP, ck_interval_variable(k, 0), p, path);
    cc_term source = raw(k, CC_SUM, 0, first, second);
    cc_formula_id replacement = ck_interval_variable(k, 2);
    for (uint64_t n = 1; k->formula_count < k->formula_capacity; ++n) {
        cc_clause unused = {8 | n << 4, 0};
        cc_formula fill = {CC_INTERVAL, &unused, 1, 1};
        assert(ck_formula(k, &fill));
    }
    size_t capacity = k->formula_capacity;
    cc_term result = ck_dimension_substitute(k, source, 0, cc_kernel_get_formula(k, replacement));
    assert(result && k->formula_capacity > capacity);
    cc_node pair = k->nodes[result];
    const cc_formula *left = cc_kernel_get_formula(k, k->nodes[pair.child[0]].payload);
    assert(left && left->length == 1 && left->clauses[0].positive == 6 && !left->clauses[0].negative);
    assert(k->nodes[pair.child[1]].payload == replacement && !k->error[0]);
    cc_kernel_free(k);
}

static void cached_term_rename(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term x = raw(k, CC_VAR, 100, 0, 0), source = raw(k, CC_SUM, 0, x, x);
    cc_term renamed = cc_kernel_rename(k, source, false, 100, 101);
    assert(renamed && renamed != source);
    uint64_t before = steps(k);
    cc_kernel_set_step_budget(k, 1);
    assert(cc_kernel_rename(k, source, false, 100, 101) == renamed);
    assert(steps(k) - before == 1);
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { }
    assert(!cc_kernel_rename(k, source, false, 100, 101));
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_clear_error(k);
    cc_kernel_set_deadline_ms(k, 0);
    assert(cc_kernel_rename(k, source, false, 100, 101) == renamed);
    cc_kernel_free(k);
}

/* A failed free-name scan is not evidence that substitution does nothing.
 * Public queries must return failure, then recover with enough budget. */
static void interrupted_substitution(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term x = raw(k, CC_VAR, 100, 0, 0), unit = raw(k, CC_UNIT, 0, 0, 0);
    cc_term path = ck_make(k, CC_PATH, 2, ck_universe_at(k, 0), unit, unit, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), x, path);
    cc_term term_graph = x, dimension_graph = at;
    for (unsigned n = 0; n < 40; ++n) {
        term_graph = raw(k, CC_SUM, 0, term_graph, term_graph);
        dimension_graph = raw(k, CC_SUM, 0, dimension_graph, dimension_graph);
    }
    cc_kernel_set_step_budget(k, 1);
    assert(!cc_kernel_rename(k, term_graph, false, 100, 101));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    assert(!cc_kernel_endpoint_term(k, dimension_graph, 0, 0));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 5000);
    cc_term renamed = cc_kernel_rename(k, term_graph, false, 100, 101);
    cc_term restricted = cc_kernel_endpoint_term(k, dimension_graph, 0, 0);
    assert(renamed && restricted && renamed != term_graph && restricted != dimension_graph);
    assert(!ck_term_free(k, renamed, 100) && ck_term_free(k, renamed, 101));
    assert(!ck_free_dims(k, restricted) && !k->error[0]);
    cc_kernel_free(k);
}

/* Reduction-generated walls may still mention the coordinates fixed on
 * their face. Their off-face computation is not part of the partial value.
 * Disjunctive faces must retain their order and only common restrictions. */
static void wall_faces(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), empty = raw(k, CC_VOID, 0, 0, 0);
    cc_term path = ck_make(k, CC_PATH, 3, ck_universe_at(k, 0), unit, empty, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 100), path);
    cc_formula_id i0 = ck_endpoint_face(k, 0, 0);
    cc_term wall = raw(k, CC_TUBE, i0, at, 0);
    cc_term result = cc_kernel_normalize(k, wall);
    assert(result && k->nodes[result].payload == i0 && k->nodes[result].child[0] == unit);

    cc_clause alternatives[] = {{0, 1}, {0, 2}};
    cc_formula either = {CC_FACE, alternatives, 2, 2};
    cc_formula_id disjunction = ck_formula(k, &either);
    wall = raw(k, CC_TUBE, disjunction, at, 0);
    result = cc_kernel_normalize(k, wall);
    assert(result && k->nodes[result].payload == disjunction && k->nodes[result].child[0] == at);

    cc_clause common[] = {{0, 3}, {0, 5}};
    cc_formula shared = {CC_FACE, common, 2, 2};
    cc_formula_id fixed_i = ck_formula(k, &shared);
    wall = raw(k, CC_TUBE, fixed_i, at, 0);
    result = cc_kernel_normalize(k, wall);
    assert(result && k->nodes[result].payload == fixed_i && k->nodes[result].child[0] == unit);
    /* Glue has partial types and equivalences on the same face. Its tail
     * belongs to its own face, so must retain its own endpoint. */
    cc_formula_id i1 = ck_endpoint_face(k, 0, 1);
    cc_term tail = ck_make(k, CC_GLUE_SYSTEM, i1, at, at, 0, 0);
    cc_term glue = ck_make(k, CC_GLUE_SYSTEM, fixed_i, at, at, tail, 0);
    result = cc_kernel_normalize(k, glue);
    assert(result && k->nodes[result].payload == fixed_i);
    assert(k->nodes[result].child[0] == unit && k->nodes[result].child[1] == unit);
    tail = k->nodes[result].child[2];
    assert(k->nodes[tail].payload == i1);
    assert(k->nodes[tail].child[0] == empty && k->nodes[tail].child[1] == empty);
    /* Restrictions cannot escape into an unrestricted use of the term. */
    assert(cc_kernel_normalize(k, at) == at);
    cc_kernel_free(k);
}

/* A face restriction can expose the constructor needed by composition.
 * The new constructor's arguments are compositions, not yet normal forms. */
static void composition_after_restriction(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), point = raw(k, CC_POINT, 0, 0, 0);
    cc_term sum = raw(k, CC_SUM, 0, unit, unit), left = raw(k, CC_INL, 0, sum, point);
    cc_term path = ck_make(k, CC_PATH, 2, sum, left, left, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 100), path);
    cc_term wall = raw(k, CC_TUBE, ck_endpoint_face(k, 0, 0), at, 0);
    cc_term comp = ck_make(k, CC_COMP, 1, sum, wall, left, 0);
    cc_term result = cc_kernel_normalize(k, comp);
    assert(result && ck_alpha_equal(k, result, left));
    assert(ck_alpha_equal(k, cc_kernel_normalize(k, result), result));
    /* Each public query starts with a fresh recursion counter. */
    k->recursion = 1024;
    assert(cc_kernel_normalize(k, comp) == result && !k->recursion);
    cc_kernel_free(k);
}

static void partial_scopes(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term a = ck_var(k, 100), x = ck_var(k, 101), y = ck_var(k, 102);
    cc_term along_type = ck_make(k, CC_PATH, 2, a, x, y, 0);
    cc_term along = raw(k, CC_PAPP, ck_interval_variable(k, 1), ck_var(k, 103), along_type);
    cc_term across_type = ck_make(k, CC_PATH, 2, a, along, along, 0);
    cc_term across = raw(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 104), across_type);
    cc_formula_id j0 = ck_endpoint_face(k, 0, 0);
    cc_term wall = raw(k, CC_TUBE, j0, across, 0);
    cc_term comp = ck_make(k, CC_COMP, 1, a, wall, x, 0);
    cc_term result = cc_kernel_normalize(k, comp);
    assert(result && k->nodes[result].kind == CC_COMP && k->nodes[result].payload == 1);
    cc_term body = k->nodes[k->nodes[result].child[1]].child[0];
    assert(ck_alpha_equal(k, body, along) && ck_free_dims(k, body) == (UINT64_C(1) << 1));
    assert(ck_alpha_equal(k, cc_kernel_normalize(k, result), result));

    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), point = raw(k, CC_POINT, 0, 0, 0);
    cc_term piece = ck_make(k, CC_GLUE_SYSTEM, j0, unit, ck_var(k, 105), 0, 0);
    cc_term glue = raw(k, CC_GLUE, 0, unit, piece);
    cc_term path = ck_make(k, CC_PATH, 2, unit, point, point, 0);
    cc_term at = raw(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 106), path);
    cc_term partial = raw(k, CC_TUBE, j0, at, 0);
    cc_term value = ck_make(k, CC_GLUE_TERM, 0, glue, ck_var(k, 107), partial, 0);
    result = cc_kernel_normalize(k, value);
    assert(result && k->nodes[result].kind == CC_GLUE_TERM);
    partial = k->nodes[result].child[2];
    assert(k->nodes[partial].payload == j0 && ck_alpha_equal(k, k->nodes[partial].child[0], point));
    assert(ck_alpha_equal(k, cc_kernel_normalize(k, result), result) && !k->error[0]);
    cc_kernel_free(k);
}

static void unshared_stuck_composition(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, 0);
    cc_term a = ck_var(k, 100), u = ck_var(k, 101), b = ck_var(k, 102);
    cc_term tube = raw(k, CC_TUBE, ck_endpoint_face(k, 0, 0), u, 0);
    cc_term comp = ck_make(k, CC_HCOMP, 1, a, tube, b, 0);
    cc_kernel_set_step_budget(k, 1000);
    cc_term result = cc_kernel_normalize(k, comp);
    assert(result && ck_alpha_equal(k, result, comp));
    assert(ck_alpha_equal(k, cc_kernel_normalize(k, result), result) && !k->error[0]);
    cc_kernel_free(k);
}

/* References keep each checked definition shallow while its expanded sum
 * type is deep. Full traversal must reach the output syntax guard without
 * exhausting the C call stack first. The guard itself is deliberately kept. */
static void normalization_continuations(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k), type = unit;
    cc_term prefix = 0, middle = 0;
    for (unsigned i = 1; i <= 17000; ++i) {
        type = cc_instr_define(k, 100 + i, cc_instr_sum(k, type, unit));
        cc_term source = info(k, type).term;
        if (i == 400)
            prefix = source;
        if (i == 2200) {
            middle = source;
            cc_kernel_set_step_budget(k, 200);
            assert(!cc_kernel_normalize(k, source));
            assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET && !k->recursion);
            assert(!k->normal_cache[source]);
            cc_kernel_clear_error(k);
            cc_kernel_set_step_budget(k, 1000000);
            assert(!cc_kernel_normalize(k, source));
            assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
            assert(strstr(cc_kernel_error(k), "syntax depth exceeds 512"));
            assert(!k->normal_cache[source] && !k->recursion);
            cc_kernel_clear_error(k);
            cc_term normal = cc_kernel_normalize(k, prefix);
            assert(normal && k->nodes[normal].depth == 401);
            for (unsigned j = 0; j < 400; ++j) {
                cc_node n = k->nodes[normal];
                assert(n.kind == CC_SUM && k->nodes[n.child[1]].kind == CC_UNIT);
                normal = n.child[0];
            }
            assert(k->nodes[normal].kind == CC_UNIT);
        }
    }
    /* The explicit stack has a finite frame/memory bound too. Exhausting it
     * leaves neither a completed parent nor a poisoned subsequent query. */
    cc_term source = info(k, type).term;
    assert(!cc_kernel_normalize(k, source));
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE && !k->recursion);
    assert(strstr(cc_kernel_error(k), "normal-form depth exceeded"));
    assert(!k->normal_cache[source] && !k->normal_cache[middle]);
    cc_kernel_clear_error(k);
    assert(cc_kernel_normalize(k, prefix) && !k->error[0]);
    /* Also traverse a new, uncached deep graph after the resource failure. */
    cc_judgement_id fresh = cc_instr_void(k);
    for (unsigned i = 0; i < 400; ++i)
        fresh = cc_instr_sum(k, unit, fresh);
    cc_term cold = info(k, fresh).term;
    assert(!k->normal_cache[cold]);
    cc_term normal = cc_kernel_normalize(k, cold);
    assert(normal && k->nodes[normal].depth == 401);
    for (unsigned i = 0; i < 400; ++i) {
        cc_node node = k->nodes[normal];
        assert(node.kind == CC_SUM && k->nodes[node.child[0]].kind == CC_UNIT);
        normal = node.child[1];
    }
    assert(k->nodes[normal].kind == CC_VOID && !k->error[0] && !k->recursion);
    cc_kernel_free(k);
}

/* Glue eta must normalize a restricted neutral path at each disjunctive
 * face. Substitution alone leaves PApp(p, 0), so the weak syntactic eta test
 * cannot contract it. A mismatch on a later face must abandon the contraction. */
static void normal_glue_boundaries(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), point = raw(k, CC_POINT, 0, 0, 0);
    cc_term identity = ck_identity_equiv(k, unit);
    cc_term family_piece = ck_make(k, CC_GLUE_SYSTEM, ck_endpoint_face(k, 2, 0), unit, identity, 0, 0);
    cc_term family = raw(k, CC_GLUE, 0, unit, family_piece);
    cc_term path = ck_make(k, CC_PATH, 2, family, point, ck_var(k, 100), 0);
    /* (i /\ j)=0 gives the disjunction i=0 or j=0. Both clauses expose
     * the left endpoint, but the unrestricted path remains neutral. */
    cc_clause product = {3, 0};
    cc_formula coordinate = {CC_INTERVAL, &product, 1, 1};
    cc_formula_id ij = ck_formula(k, &coordinate);
    cc_term glue = ck_dimension_substitute(k, family, 2, &coordinate);
    cc_term value = raw(k, CC_PAPP, ij, ck_var(k, 101), path);
    cc_formula_id either = k->nodes[k->nodes[glue].child[1]].payload;
    assert(cc_kernel_get_formula(k, either)->length == 2);
    cc_term wall = raw(k, CC_TUBE, either, point, 0);
    cc_term projected = raw(k, CC_UNGLUE, 0, glue, value);
    cc_term candidate = ck_make(k, CC_GLUE_TERM, 0, glue, projected, wall, 0);
    assert(k->nodes[cc_kernel_whnf(k, candidate)].kind == CC_GLUE_TERM);
    cc_term normal = cc_kernel_normalize(k, candidate);
    assert(normal && ck_alpha_equal(k, normal, cc_kernel_normalize(k, value)));
    assert(k->nodes[normal].kind == CC_PAPP);
    /* Each negative disjunction agrees on one face and remains neutral on
     * the other. Both coordinates make this insensitive to clause ordering:
     * checking only the first OR only the last clause must fail this test.
     * These deliberately mismatching raw candidates certify no typing. */
    for (unsigned dim = 0; dim < 2; ++dim) {
        cc_term partial = raw(k, CC_PAPP, ck_interval_variable(k, dim), ck_var(k, 101), path);
        cc_term base = raw(k, CC_UNGLUE, 0, glue, partial);
        cc_term bad = ck_make(k, CC_GLUE_TERM, 0, glue, base, wall, 0);
        cc_term stuck = cc_kernel_normalize(k, bad);
        assert(stuck && k->nodes[stuck].kind == CC_GLUE_TERM);
    }
    /* A separate malformed candidate has a bad last piece: a syntax query
     * cannot use the previous successful side condition for this piece. */
    cc_term wrong = raw(k, CC_TUBE, ck_endpoint_face(k, 1, 0), ck_var(k, 102), 0);
    wrong = raw(k, CC_TUBE, ck_endpoint_face(k, 0, 0), point, wrong);
    candidate = ck_make(k, CC_GLUE_TERM, 0, glue, projected, wrong, 0);
    normal = cc_kernel_normalize(k, candidate);
    assert(normal && k->nodes[normal].kind == CC_GLUE_TERM);
    assert(!k->error[0] && !k->recursion);
    cc_kernel_free(k);
}

/* Each alias is separately checked, closed and shallow. Thousands of tail
 * delta steps must reach the point without spending native recursion depth.
 * Cache publication retains completed aliases up to its bound, never a failed prefix. */
static void weak_tail_aliases(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_judgement_id value = cc_instr_point(k);
    cc_term point = info(k, value).term, prefix = 0, middle = 0, visited = 0, omitted = 0;
    for (unsigned i = 1; i <= 21000; ++i) {
        value = cc_instr_define(k, 100 + i, value);
        cc_term source = info(k, value).term;
        if (i == 1000)
            middle = source;
        if (i == 4000)
            visited = source;
        if (i == 4500)
            omitted = source;
        if (i != 4096)
            continue;
        prefix = source;
        cc_kernel_set_step_budget(k, 200);
        assert(!cc_kernel_whnf(k, source));
        assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET && !k->recursion);
        assert(!k->weak_cache[source] && !k->weak_cache[visited]);
        cc_kernel_clear_error(k);
        cc_kernel_set_step_budget(k, 100000);
        uint64_t before = steps(k);
        assert(cc_kernel_whnf(k, source) == point);
        assert(steps(k) - before == 4097 && !k->recursion);
        assert(k->weak_cache[middle] == point);
        before = steps(k);
        assert(cc_kernel_whnf(k, middle) == point && steps(k) - before == 1);
        cc_term normal = cc_kernel_normalize(k, source);
        assert(normal && k->nodes[normal].kind == CC_POINT && !k->error[0]);
    }
    cc_term source = info(k, value).term;
    cc_kernel_set_step_budget(k, 16500);
    assert(!cc_kernel_whnf(k, source));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET && !k->recursion);
    assert(!k->weak_cache[source] && !k->weak_cache[omitted]);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 100000);
    /* More than 16,384 uncached tails still compute. Only memo retention is
     * capped: the outer query is cached, while this later alias is omitted. */
    uint64_t before = steps(k);
    assert(cc_kernel_whnf(k, source) == point && !k->error[0] && !k->recursion);
    assert(steps(k) - before == 21000 - 4096 + 1);
    assert(k->weak_cache[source] == point && !k->weak_cache[omitted]);
    before = steps(k);
    assert(cc_kernel_whnf(k, source) == point && steps(k) - before == 1);
    assert(cc_kernel_whnf(k, omitted) == point && k->weak_cache[omitted] == point);
    assert(cc_kernel_whnf(k, prefix) == point);
    /* A new beta redex succeeds too, rather than relying only on a cache. */
    cc_judgement_id unit = cc_instr_unit(k);
    cc_entry_id x = cc_instr_extend(k, unit, 30000);
    cc_judgement_id identity = cc_instr_lambda(k, x, cc_instr_variable(k, x));
    cc_term application = info(k, cc_instr_apply(k, identity, cc_instr_point(k))).term;
    assert(!k->weak_cache[application]);
    assert(cc_kernel_whnf(k, application) == point && !k->error[0]);
    cc_kernel_free(k);
}

/* A finite checked chain alternating delta and beta fully normalizes. */
static void weak_tail_beta(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k), value = cc_instr_point(k);
    cc_term point = info(k, value).term;
    cc_entry_id x = cc_instr_extend(k, unit, 100);
    cc_judgement_id identity = cc_instr_lambda(k, x, cc_instr_variable(k, x));
    for (unsigned i = 1; i <= 2000; ++i)
        value = cc_instr_define(k, 100 + i, cc_instr_apply(k, identity, value));
    cc_term source = info(k, value).term;
    assert(cc_kernel_normalize(k, source) == point && !k->recursion);
    cc_kernel_free(k);
}

/* Raw syntax queries may receive ill-typed self-application. The tail loop
 * must exhaust its budget, never publish a cyclic "head" or leak recursion. */
static void weak_tail_raw_cycle(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term unit = raw(k, CC_UNIT, 0, 0, 0), x = raw(k, CC_VAR, 42, 0, 0);
    cc_term self = raw(k, CC_LAM, 42, unit, raw(k, CC_APP, 0, x, x));
    cc_term cycle = raw(k, CC_APP, 0, self, self);
    cc_kernel_set_step_budget(k, 100000);
    assert(!cc_kernel_whnf(k, cycle));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET && !k->recursion);
    assert(!k->weak_cache[cycle]);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 1000);
    cc_term point = info(k, cc_instr_point(k)).term;
    assert(cc_kernel_whnf(k, point) == point && !k->error[0]);
    cc_kernel_free(k);
}

int main(void) {
    weak_tail_aliases(CC_SHARE_SYNTAX);
    weak_tail_aliases(0);
    weak_tail_beta();
    weak_tail_raw_cycle();
    normalization_continuations();
    normal_glue_boundaries(CC_SHARE_SYNTAX);
    normal_glue_boundaries(0);
    shared_graph(CC_SHARE_SYNTAX);
    shared_graph(0);
    rollback_and_reuse();
    compaction();
    failed_parent();
    scope_and_restriction();
    shared_dimension_substitution(CC_SHARE_SYNTAX);
    shared_dimension_substitution(0);
    dimension_cache_scope_and_rollback();
    substitution_grows_formula_arena();
    cached_term_rename();
    interrupted_substitution();
    wall_faces();
    composition_after_restriction(CC_SHARE_SYNTAX);
    composition_after_restriction(0);
    partial_scopes(CC_SHARE_SYNTAX);
    partial_scopes(0);
    unshared_stuck_composition();
    puts("full normalization cache: ok");
}
