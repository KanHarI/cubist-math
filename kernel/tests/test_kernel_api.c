/* A rejected check must not prevent a user from constructing a correction. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <time.h>

static cc_term_kind kind(cc_kernel *k, cc_term term) {
    cc_term_kind result;
    assert(cc_kernel_node(k, term, &result, NULL, NULL));
    return result;
}

static void checked_definitions(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term one = cc_kernel_term(k, CC_SUCC, 0, zero, 0, 0, 0);
    cc_term named_nat = cc_kernel_define(k, 100, nat, 0);
    cc_term named_one = cc_kernel_define(k, 101, one, named_nat);
    assert(named_nat && named_one);
    assert(kind(k, named_one) == CC_DEFREF);
    uint32_t symbol;
    cc_term body, type;
    assert(cc_kernel_definition(k, named_one, &symbol, &body, &type));
    assert(symbol == 101 && kind(k, body) == CC_SUCC && kind(k, type) == CC_NAT);
    assert(!cc_kernel_definition(k, one, NULL, NULL, NULL));
    cc_checked_result checked;
    assert(cc_kernel_check(k, named_one, named_nat, NULL, 0, &checked));
    assert(checked.expression == named_one && !checked.normal);
    assert(kind(k, cc_kernel_whnf(k, checked.expression)) == CC_SUCC);

    /* Publication is closed and atomic: neither a wrong type, an unknown
     * reference, nor a free variable reserves the requested source name. */
    assert(!cc_kernel_define(k, 102, zero, unit));
    cc_kernel_clear_error(k);
    cc_term free_var = cc_kernel_term(k, CC_VAR, 17, 0, 0, 0, 0);
    assert(!cc_kernel_define(k, 102, free_var, nat));
    cc_kernel_clear_error(k);
    cc_term unknown = cc_kernel_term(k, CC_DEFREF, 999999, 0, 0, 0, 0);
    assert(!cc_kernel_define(k, 102, unknown, nat));
    cc_kernel_clear_error(k);
    cc_term alias = cc_kernel_define(k, 102, named_one, nat);
    assert(alias);
    assert(!cc_kernel_define(k, 102, zero, nat));
    cc_kernel_clear_error(k);
    assert(cc_kernel_check(k, alias, nat, NULL, 0, &checked));

    /* Transparent conversion distinguishes different definitions and only
     * unfolds a body when the folded structures do not already agree. */
    cc_term named_zero = cc_kernel_define(k, 103, zero, nat);
    cc_term constant_path = cc_kernel_term(k, CC_PLAM, 0, nat, alias, 0, 0);
    cc_term same = cc_kernel_term(k, CC_PATH, 0, nat, named_one, named_one, 0);
    cc_term different = cc_kernel_term(k, CC_PATH, 0, nat, named_zero, named_zero, 0);
    assert(cc_kernel_check(k, constant_path, same, NULL, 0, &checked));
    assert(!cc_kernel_check(k, constant_path, different, NULL, 0, &checked));
    cc_kernel_clear_error(k);

    /* A head query exposes the function without normalizing its body. */
    cc_term identity = cc_kernel_term(k, CC_LAM, 17, nat, free_var, 0, 0);
    cc_term named_id = cc_kernel_define(k, 104, identity, 0);
    assert(named_id && kind(k, cc_kernel_whnf(k, named_id)) == CC_LAM);
    cc_term applied = cc_kernel_term(k, CC_APP, 0, named_id, named_one, 0, 0);
    assert(cc_kernel_check(k, applied, nat, NULL, 0, &checked));
    assert(kind(k, cc_kernel_whnf(k, checked.expression)) == CC_SUCC);

    /* Build the compact natural 2^22 by checked applications of doubling.
     * This equality must compare references, not allocate 4,194,304 succs. */
    cc_term n = cc_kernel_term(k, CC_VAR, 18, 0, 0, 0, 0);
    cc_term ih = cc_kernel_term(k, CC_VAR, 19, 0, 0, 0, 0);
    cc_term twice_succ = cc_kernel_term(k, CC_SUCC, 0, ih, 0, 0, 0);
    twice_succ = cc_kernel_term(k, CC_SUCC, 0, twice_succ, 0, 0, 0);
    cc_term step = cc_kernel_term(k, CC_LAM, 19, nat, twice_succ, 0, 0);
    step = cc_kernel_term(k, CC_LAM, 18, nat, step, 0, 0);
    cc_term motive = cc_kernel_term(k, CC_LAM, 18, nat, nat, 0, 0);
    cc_term rec = cc_kernel_term(k, CC_NATREC, 0, motive, zero, step, n);
    cc_term double_fn = cc_kernel_term(k, CC_LAM, 18, nat, rec, 0, 0);
    cc_term named_double = cc_kernel_define(k, 105, double_fn, 0);
    assert(named_double);
    cc_term compact = named_one;
    for (unsigned i = 0; i < 22; ++i) {
        cc_term next = cc_kernel_term(k, CC_APP, 0, named_double, compact, 0, 0);
        compact = cc_kernel_define(k, 200 + i, next, nat);
        assert(compact);
    }
    cc_term compact_path = cc_kernel_term(k, CC_PLAM, 0, nat, compact, 0, 0);
    cc_term compact_type = cc_kernel_term(k, CC_PATH, 1, nat, compact, compact, 0);
    assert(cc_kernel_check(k, compact_path, compact_type, NULL, 0, &checked));
    assert(checked.arena_nodes < 5000);
    printf("Folded 2^22 equality: %zu nodes, %llu checking + %llu reduction steps.\n",
           checked.arena_nodes, (unsigned long long)checked.checking_steps,
           (unsigned long long)checked.reduction_steps);
    /* The inspector also sees shared, not-yet-checked syntax. Free-name
     * analysis must visit this DAG once rather than walking 2^24 branches.
     * Its weak head is a lambda, so no arithmetic evaluation is requested. */
    cc_term shared = one;
    for (unsigned i = 0; i < 24; ++i)
        shared = cc_kernel_term(k, CC_NATREC, 0, motive, shared, step, shared);
    cc_term inner = cc_kernel_term(k, CC_LAM, 18, nat, free_var, 0, 0);
    cc_term outer = cc_kernel_term(k, CC_LAM, 17, nat, inner, 0, 0);
    cc_term inserted = cc_kernel_term(k, CC_APP, 0, outer, shared, 0, 0);
    assert(kind(k, cc_kernel_whnf(k, inserted)) == CC_LAM);
    cc_kernel_free(k);
}

static void open_cube(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term universe = cc_kernel_term(k, CC_U, 0, 0, 0, 0, 0);
    cc_term family_type = cc_kernel_term(k, CC_PATH, 1, universe, nat, unit, 0);
    cc_term family = cc_kernel_term(k, CC_VAR, 100, 0, 0, 0, 0);
    cc_formula i;
    cc_init(&i, CC_INTERVAL);
    assert(cc_generator(&i, 0, true) == CC_OK);
    cc_formula_id direction = cc_kernel_formula(k, &i);
    cc_clear(&i);
    cc_term at_i = cc_kernel_term(k, CC_PAPP, direction, family, 0, 0, 0);
    cc_term x = cc_kernel_term(k, CC_VAR, 101, 0, 0, 0, 0);
    cc_assumption assumptions[] = {{100, family_type}, {101, at_i}};
    cc_checked_result result;
    assert(cc_kernel_check_in_cube(k, x, at_i, assumptions, 2, UINT64_C(1), &result));
    assert(result.expression && result.type);
    assert(!cc_kernel_check(k, x, at_i, assumptions, 2, &result));
    assert(!result.expression && !result.type);
    assert(!cc_kernel_check_in_cube(k, x, at_i, assumptions, 2, UINT64_C(2), &result));
    assert(cc_kernel_check_in_cube(k, x, at_i, assumptions, 2, UINT64_C(1), &result));
    /* An open checking result does not bypass closed definition checking. */
    assert(!cc_kernel_define(k, 102, x, at_i));
    cc_kernel_free(k);
}

/* Callers classify a rejection by its kind, never by its message. */
static void error_kinds(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term free_var = cc_kernel_term(k, CC_VAR, 17, 0, 0, 0, 0);
    cc_term large = zero;
    for (unsigned i = 0; i < 64; ++i) large = cc_kernel_term(k, CC_SUCC, 0, large, 0, 0, 0);
    cc_checked_result result;
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    assert(!cc_kernel_check(k, zero, unit, NULL, 0, &result));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH);
    cc_term found = 0, expected = 0;
    assert(cc_kernel_mismatch(k, &found, &expected));
    assert(cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0) == 0); /* no construction while an error is set */
    cc_kernel_clear_error(k);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    assert(!cc_kernel_mismatch(k, &found, &expected));
    /* The recorded pair is the type of 0 and the type it had to match. */
    cc_checked_result as_nat, as_unit;
    assert(cc_kernel_check(k, zero, nat, NULL, 0, &as_nat));
    assert(cc_kernel_check(k, unit, 0, NULL, 0, &as_unit));
    assert(!cc_kernel_check(k, zero, unit, NULL, 0, &result));
    assert(cc_kernel_mismatch(k, &found, &expected));
    cc_kernel_clear_error(k);
    cc_checked_result found_view, expected_view;
    assert(cc_kernel_check(k, found, 0, NULL, 0, &found_view));
    assert(cc_kernel_check(k, expected, 0, NULL, 0, &expected_view));
    assert(found_view.expression == as_nat.type);
    assert(expected_view.expression == unit);
    assert(!cc_kernel_check(k, free_var, nat, NULL, 0, &result));
    assert(cc_kernel_error_kind(k) == CC_ERROR_OTHER);
    assert(cc_kernel_check(k, zero, nat, NULL, 0, &result));
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    cc_kernel_set_step_budget(k, 16);
    assert(!cc_kernel_check(k, large, nat, NULL, 0, &result));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_set_step_budget(k, UINT64_C(1) << 40);
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { /* let it expire */ }
    assert(!cc_kernel_check(k, large, nat, NULL, 0, &result));
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_set_deadline_ms(k, 0);
    assert(cc_kernel_check(k, large, nat, NULL, 0, &result));
    assert(cc_kernel_error_kind(NULL) == CC_ERROR_OTHER);
    cc_kernel_free(k);
}

/* A trace records the rules as they run, and never changes a judgement. */
static bool traced(const cc_kernel *k, cc_trace_kind kind, uint32_t a, cc_trace_event *found) {
    cc_trace_event event;
    for (size_t i = 0; cc_kernel_trace_event(k, i, &event); ++i)
        if (event.kind == kind && (!a || event.a == a)) { if (found) *found = event; return true; }
    return false;
}

static void trace_events(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term var = cc_kernel_term(k, CC_VAR, 5, 0, 0, 0, 0);
    cc_term identity = cc_kernel_term(k, CC_LAM, 5, nat, var, 0, 0);
    cc_term arrow = cc_kernel_term(k, CC_PI, 5, nat, nat, 0, 0);
    cc_checked_result result;
    assert(cc_kernel_trace_start(k, 256));
    assert(cc_kernel_check(k, identity, arrow, NULL, 0, &result));
    cc_trace_event event;
    /* Entering the binder: the domain is inferred, the context gains 5 : Nat,
     * and the body is inferred one level deeper. */
    assert(traced(k, CC_TRACE_INFER, identity, &event) && event.depth == 0);
    assert(traced(k, CC_TRACE_EXTEND, 5, &event) && event.b);
    assert(traced(k, CC_TRACE_INFER, var, &event) && event.depth == 1);
    assert(traced(k, CC_TRACE_INFERRED, identity, &event) && event.b && event.c);
    assert(traced(k, CC_TRACE_CONVERT, 0, &event) && event.c == 1);
    /* Checking again reuses the cached judgement. */
    assert(cc_kernel_trace_start(k, 256));
    assert(cc_kernel_check(k, identity, arrow, NULL, 0, &result));
    assert(traced(k, CC_TRACE_REUSED, identity, NULL));
    /* A rejection is still a rejection, with the failed conversion recorded. */
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    assert(cc_kernel_trace_start(k, 256));
    assert(!cc_kernel_check(k, zero, unit, NULL, 0, &result));
    assert(traced(k, CC_TRACE_CONVERT, 0, &event) && event.c == 0);
    cc_kernel_clear_error(k);
    /* Events beyond the capacity are counted, not kept. */
    assert(cc_kernel_trace_start(k, 1));
    assert(cc_kernel_check(k, zero, nat, NULL, 0, &result));
    assert(cc_kernel_trace_count(k) > 1);
    assert(cc_kernel_trace_event(k, 0, &event) && !cc_kernel_trace_event(k, 1, &event));
    /* Stopped, nothing is recorded. */
    cc_kernel_trace_stop(k);
    assert(cc_kernel_check(k, identity, arrow, NULL, 0, &result));
    assert(cc_kernel_trace_count(k) == 0 && !cc_kernel_trace_event(k, 0, &event));
    assert(!cc_kernel_trace_start(k, 0));
    cc_kernel_free(k);
}

/* The syntax hash graph is exact: identical syntax has one handle, beyond
 * any cache size, after a rollback reuses handles, and after compaction. */
static void exact_sharing(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    enum { MANY = 100000 };
    cc_term first = cc_kernel_term(k, CC_U, 0, 0, 0, 0, 0);
    for (uint32_t level = 1; level < MANY; ++level)
        assert(cc_kernel_term(k, CC_U, level, 0, 0, 0, 0) == first + level);
    for (uint32_t level = 0; level < MANY; level += 997)
        assert(cc_kernel_term(k, CC_U, level, 0, 0, 0, 0) == first + level);

    cc_kernel_checkpoint(k);
    cc_term discarded = cc_kernel_term(k, CC_U, MANY, 0, 0, 0, 0);
    cc_kernel_rollback(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    assert(nat == discarded);
    cc_term again = cc_kernel_term(k, CC_U, MANY, 0, 0, 0, 0);
    assert(again != nat && cc_kernel_term(k, CC_U, MANY, 0, 0, 0, 0) == again);
    assert(cc_kernel_term(k, CC_U, 7, 0, 0, 0, 0) == first + 7);

    cc_kernel_checkpoint(k);
    assert(cc_kernel_term(k, CC_U, MANY + 1, 0, 0, 0, 0));
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term one = cc_kernel_term(k, CC_SUCC, 0, zero, 0, 0, 0);
    cc_term reference = cc_kernel_define(k, 500, one, nat);
    assert(reference && cc_kernel_commit_checkpoint(k));
    cc_term value;
    assert(cc_kernel_definition(k, cc_kernel_relocated(k, reference), NULL, &value, NULL));
    zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    assert(cc_kernel_term(k, CC_SUCC, 0, zero, 0, 0, 0) == value);
    cc_kernel_free(k);
}

int main(void) {
    trace_events();
    checked_definitions();
    exact_sharing();
    open_cube();
    error_kinds();
    cc_kernel *kernel = cc_kernel_new();
    assert(kernel);
    cc_term nat = cc_kernel_term(kernel, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(kernel, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(kernel, CC_ZERO, 0, 0, 0, 0, 0);
    cc_checked_result result;
    assert(!cc_kernel_check(kernel, zero, unit, NULL, 0, &result));
    assert(result.expression == 0 && result.type == 0);
    assert(cc_kernel_error(kernel)[0]);
    cc_kernel_clear_error(kernel);
    assert(!cc_kernel_error(kernel)[0]);
    cc_term corrected = cc_kernel_term(kernel, CC_SUCC, 0, zero, 0, 0, 0);
    assert(corrected);
    assert(cc_kernel_check(kernel, corrected, nat, NULL, 0, &result));
    assert(result.expression && result.type && !result.normal);
    assert(cc_kernel_normalize(kernel, result.expression));
    cc_kernel_clear_error(NULL);
    cc_kernel_free(kernel);
    puts("Native checked API recovery passed.");
    return 0;
}
