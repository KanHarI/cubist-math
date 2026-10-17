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

int main(void) {
    shared_graph(CC_SHARE_SYNTAX);
    shared_graph(0);
    rollback_and_reuse();
    compaction();
    failed_parent();
    scope_and_restriction();
    puts("full normalization cache: ok");
}
