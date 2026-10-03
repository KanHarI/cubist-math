/* The public API around the instructions: definitions, error kinds, exact
 * sharing, and recovery. A rejected instruction must not prevent a user
 * from constructing a correction. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static cc_term_kind kind(cc_kernel *k, cc_term term) {
    cc_term_kind result;
    assert(cc_kernel_node(k, term, &result, NULL, NULL));
    return result;
}

static cc_judgement_info info(cc_kernel *k, cc_judgement_id id) {
    cc_judgement_info result;
    assert(id && cc_kernel_judgement(k, id, &result));
    return result;
}

static void definitions(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k);
    cc_judgement_id two = cc_instr_sum(k, unit, unit);
    cc_term named_one = info(k, cc_instr_define(k, 101, cc_instr_inject(k, two, cc_instr_point(k), false))).term;
    assert(kind(k, named_one) == CC_DEFREF);
    uint32_t symbol;
    cc_term body, type;
    assert(cc_kernel_definition(k, named_one, &symbol, &body, &type));
    assert(symbol == 101 && kind(k, body) == CC_INL && kind(k, type) == CC_SUM);
    assert(!cc_kernel_definition(k, body, NULL, NULL, NULL));
    assert(kind(k, cc_kernel_whnf(k, named_one)) == CC_INL);
    /* Lookup recalls the definition at its type, and only a definition. */
    assert(info(k, cc_instr_lookup(k, named_one)).type == type);
    assert(!cc_instr_lookup(k, body));
    cc_kernel_clear_error(k);

    /* Publication is closed and atomic: an open judgement, or a name already
     * taken by another body, publishes nothing. */
    cc_entry_id x = cc_instr_extend(k, unit, 17);
    assert(x && !cc_instr_define(k, 102, cc_instr_variable(k, x)));
    assert(strstr(cc_kernel_error(k), "closed judgement"));
    cc_kernel_clear_error(k);
    assert(!cc_instr_define(k, 101, cc_instr_point(k)));
    assert(strstr(cc_kernel_error(k), "already registered"));
    cc_kernel_clear_error(k);

    /* A head query exposes a function without normalizing its body, and
     * free-name analysis visits a shared DAG once rather than walking 2^24
     * branches. */
    cc_term nat = cc_kernel_term(k, CC_U, 0, cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
    cc_term free_var = cc_kernel_term(k, CC_VAR, 17, 0, 0, 0, 0);
    cc_term shared = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    for (unsigned i = 0; i < 24; ++i)
        shared = cc_kernel_term(k, CC_SUM, 0, shared, shared, 0, 0);
    cc_term inner = cc_kernel_term(k, CC_LAM, 18, nat, free_var, 0, 0);
    cc_term outer = cc_kernel_term(k, CC_LAM, 17, nat, inner, 0, 0);
    cc_term inserted = cc_kernel_term(k, CC_APP, 0, outer, shared, 0, 0);
    assert(kind(k, cc_kernel_whnf(k, inserted)) == CC_LAM);
    cc_kernel_free(k);
}

/* Callers classify a rejection by its kind, never by its message. */
static void error_kinds(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k);
    cc_entry_id y = cc_instr_extend(k, unit, 102);
    cc_judgement_id identity = cc_instr_lambda(k, y, cc_instr_variable(k, y));
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    /* Unit, a type, is no argument of λ (y : Unit). y. */
    assert(!cc_instr_apply(k, identity, unit));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH);
    cc_term found = 0, expected = 0;
    assert(cc_kernel_mismatch(k, &found, &expected));
    assert(cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0) == 0); /* no construction while an error is set */
    cc_kernel_clear_error(k);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    assert(!cc_kernel_mismatch(k, &found, &expected));
    /* The recorded pair is the argument's type and the domain it had to match. */
    assert(!cc_instr_apply(k, identity, unit));
    assert(cc_kernel_mismatch(k, &found, &expected));
    assert(found == info(k, unit).type && expected == info(k, unit).term);
    cc_kernel_clear_error(k);
    assert(!cc_instr_variable(k, 999999));
    assert(cc_kernel_error_kind(k) == CC_ERROR_OTHER);
    cc_kernel_clear_error(k);
    /* A type of 64 nested sums, normalized with too small a budget, and
     * then after the deadline has passed. */
    cc_judgement_id large = unit;
    for (unsigned i = 0; i < 64; ++i)
        large = cc_instr_sum(k, unit, large);
    cc_judgement_id reflexive = cc_instr_refl(k, large);
    assert(reflexive);
    cc_kernel_set_step_budget(k, 16);
    assert(!cc_instr_step(k, reflexive, 1, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, UINT64_C(1) << 40);
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { /* let it expire */ }
    assert(!cc_instr_step(k, reflexive, 1, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_clear_error(k);
    cc_kernel_set_deadline_ms(k, 0);
    assert(cc_instr_step(k, reflexive, 1, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(NULL) == CC_ERROR_OTHER);
    cc_kernel_free(k);
}

/* The syntax hash graph is exact: identical syntax has one handle, beyond
 * any cache size, after a rollback reuses handles, and after compaction. */
static void exact_sharing(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    enum { MANY = 100000 };
    cc_term first = cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0);
    for (uint32_t level = 1; level < MANY; ++level)
        assert(cc_kernel_term(k, CC_LCONST, level, 0, 0, 0, 0) == first + level);
    for (uint32_t level = 0; level < MANY; level += 997)
        assert(cc_kernel_term(k, CC_LCONST, level, 0, 0, 0, 0) == first + level);

    cc_kernel_checkpoint(k);
    cc_term discarded = cc_kernel_term(k, CC_LCONST, MANY, 0, 0, 0, 0);
    cc_kernel_rollback(k);
    cc_term nat = cc_kernel_term(k, CC_U, 0, cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
    assert(nat == discarded);
    cc_term again = cc_kernel_term(k, CC_LCONST, MANY, 0, 0, 0, 0);
    assert(again != nat && cc_kernel_term(k, CC_LCONST, MANY, 0, 0, 0, 0) == again);
    assert(cc_kernel_term(k, CC_LCONST, 7, 0, 0, 0, 0) == first + 7);

    cc_kernel_checkpoint(k);
    assert(cc_kernel_term(k, CC_LCONST, MANY + 1, 0, 0, 0, 0));
    cc_judgement_id unit = cc_instr_unit(k);
    cc_term reference = info(k, cc_instr_define(k, 500, cc_instr_sum(k, unit, unit))).term;
    assert(reference && cc_kernel_commit_checkpoint(k));
    cc_term value;
    assert(cc_kernel_definition(k, cc_kernel_relocated(k, reference), NULL, &value, NULL));
    cc_term u = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    assert(cc_kernel_term(k, CC_SUM, 0, u, u, 0, 0) == value);
    cc_kernel_free(k);
}

int main(void) {
    definitions();
    exact_sharing();
    error_kinds();
    cc_kernel *kernel = cc_kernel_new();
    assert(kernel);
    cc_judgement_id unit = cc_instr_unit(kernel), point = cc_instr_point(kernel);
    /* tt is no type: Sum refuses it, and the kernel goes on. */
    assert(unit && point && !cc_instr_sum(kernel, point, unit));
    assert(cc_kernel_error(kernel)[0]);
    cc_kernel_clear_error(kernel);
    assert(!cc_kernel_error(kernel)[0]);
    cc_judgement_info corrected = info(kernel, cc_instr_sum(kernel, unit, unit));
    assert(corrected.term && corrected.type);
    assert(cc_kernel_normalize(kernel, corrected.term));
    cc_kernel_clear_error(NULL);
    cc_kernel_free(kernel);
    puts("Kernel API recovery passed.");
    return 0;
}
