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

int main(void) {
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
    puts("full normalization cache: ok");
}
