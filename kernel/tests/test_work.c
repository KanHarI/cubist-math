/* Kernel work (cc_kernel_work): the counters measure a search's cost, so
 * they are checked against direct calls. Every instruction and query counts
 * once, its steps are its budget's, failures are charged to it, and nothing
 * but new work changes them: not errors, not rollback. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;

static cc_work_counters now(void) {
    cc_work_counters work;
    cc_kernel_work(k, &work);
    return work;
}

/* The counters' difference, field by field. */
static cc_work_counters since(cc_work_counters before) {
    cc_work_counters after = now();
    return (cc_work_counters){
        after.instructions - before.instructions, after.rejected - before.rejected,
        after.instruction_steps - before.instruction_steps, after.queries - before.queries,
        after.failed_queries - before.failed_queries, after.query_steps - before.query_steps,
        after.exhausted - before.exhausted, after.deadlines - before.deadlines,
    };
}

static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) {
        fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k));
        assert(0);
    }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)

static cc_term raw(cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c, cc_term d) {
    return cc_kernel_term(k, kind, payload, a, b, c, d);
}

static cc_term numeral(unsigned n) {
    cc_term value = raw(CC_UNIT, 0, 0, 0, 0, 0);
    for (unsigned i = 0; i < n; ++i) value = raw(CC_SUM, 0, value, raw(CC_UNIT, 0, 0, 0, 0, 0), 0, 0);
    return value;
}

/* Nested applications of the identity on U0 exercise checking and reduction. */
static cc_term doubled(unsigned n, unsigned base) {
    cc_term u0 = raw(CC_U, 0, raw(CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
    cc_term identity = raw(CC_LAM, 1, u0, raw(CC_VAR, 1, 0, 0, 0, 0), 0, 0);
    cc_term value = numeral(base % 100);
    for (unsigned i = 0; i < 2 * n; ++i) value = raw(CC_APP, 0, identity, value, 0, 0);
    return value;
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    cc_work_counters start = now();
    assert(!memcmp(&start, &(cc_work_counters){0}, sizeof start));

    /* An instruction takes a step on entry. Answered again from the memo, it
     * costs exactly that step and still counts. */
    cc_work_counters before = now();
    cc_judgement_id nat = OK(cc_instr_unit(k));
    cc_work_counters first = since(before);
    assert(first.instructions == 1 && first.instruction_steps >= 1 && !first.rejected);
    assert(!first.queries && !first.query_steps);
    before = now();
    assert(OK(cc_instr_unit(k)) == nat);
    cc_work_counters memo = since(before);
    assert(memo.instructions == 1 && memo.instruction_steps == 1);

    /* A rejected instruction counts, and is charged its error. One issued
     * while that error is recorded does nothing and counts nothing. */
    before = now();
    assert(!cc_instr_apply(k, nat, nat));
    cc_work_counters rejected = since(before);
    assert(rejected.instructions == 1 && rejected.rejected == 1 && !rejected.exhausted);
    before = now();
    assert(!cc_instr_point(k));
    cc_work_counters idle = since(before);
    assert(!memcmp(&idle, &(cc_work_counters){0}, sizeof idle));
    cc_kernel_clear_error(k);

    /* Building syntax is no operation. */
    before = now();
    cc_term big = doubled(40, 0);
    cc_work_counters building = since(before);
    assert(!memcmp(&building, &(cc_work_counters){0}, sizeof building));

    /* A query given a budget of n that runs out counts n steps and one
     * exhaustion; nested work shares the budget. */
    cc_kernel_set_step_budget(k, 7);
    before = now();
    assert(!cc_kernel_normalize(k, big));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_work_counters spent = since(before);
    assert(spent.queries == 1 && spent.failed_queries == 1 && spent.query_steps == 7);
    assert(spent.exhausted == 1 && !spent.instructions && !spent.instruction_steps);
    cc_kernel_clear_error(k);

    /* The term checker's steps are its query's: the same numbers it reports. */
    cc_kernel_set_step_budget(k, 10000000);
    cc_checked_result checked;
    before = now();
    assert(cc_kernel_check(k, big, raw(CC_U, 0, raw(CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0), NULL, 0, &checked));
    cc_work_counters check = since(before);
    assert(check.queries == 1 && check.query_steps == checked.checking_steps + checked.reduction_steps);
    assert(!check.failed_queries && !check.instructions);

    /* A full budget computes the normal form; the steps are the same each
     * time the same computation is made from nothing, and a rollback keeps
     * the counters. */
    cc_kernel_checkpoint(k);
    before = now();
    cc_term normal = cc_kernel_normalize(k, checked.expression);
    assert(normal);
    cc_work_counters computed = since(before);
    assert(computed.queries == 1 && computed.query_steps > 80);
    cc_work_counters kept = now();
    cc_kernel_rollback(k);
    cc_work_counters after_rollback = since(kept);
    assert(!memcmp(&after_rollback, &(cc_work_counters){0}, sizeof after_rollback));

    /* Budgeted instruction work: with a budget of one step, the entry step is
     * taken and the first step of the computation runs out. */
    cc_judgement_id typed = OK(cc_instr_unit(k));
    cc_entry_id x = OK(cc_instr_extend(k, typed, 50));
    cc_judgement_id identity = OK(cc_instr_lambda(k, x, OK(cc_instr_variable(k, x))));
    cc_judgement_id applied = OK(cc_instr_apply(k, identity, OK(cc_instr_point(k))));
    cc_judgement_id redex = OK(cc_instr_refl(k, applied));
    cc_kernel_set_step_budget(k, 1);
    before = now();
    assert(!cc_instr_step(k, redex, 1, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_work_counters short_of = since(before);
    assert(short_of.instructions == 1 && short_of.rejected == 1 && short_of.exhausted == 1);
    assert(short_of.instruction_steps == 1 && !short_of.queries);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 10000000);
    before = now();
    assert(OK(cc_instr_step(k, redex, 1, NULL, 0, CC_STEP_NORMALIZE)));
    cc_work_counters enough = since(before);
    assert(enough.instructions == 1 && !enough.rejected && enough.instruction_steps > 1);

    /* The deadline stops an operation and is counted apart from the budget. */
    before = now();
    cc_kernel_set_deadline_ms(k, 0.000001);
    /* Syntax depth is bounded, so the work is many computations, each new:
     * the deadline is read every 1024 steps. */
    for (unsigned base = 0; base < 4000 && cc_kernel_normalize(k, doubled(100, base)); ++base) continue;
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_set_deadline_ms(k, 0);
    cc_work_counters stopped = since(before);
    assert(stopped.deadlines == 1 && stopped.failed_queries == 1 && !stopped.exhausted);
    cc_kernel_clear_error(k);

    /* A public function that starts no operation charges its error to
     * nothing, however recently an instruction or a query ran. */
    OK(cc_instr_unit(k));
    before = now();
    for (int repeat = 0; repeat < 5; ++repeat) {
        assert(!cc_kernel_set_unfolding_hints(k, NULL, 1));
        assert(cc_kernel_error(k)[0]);
        cc_kernel_clear_error(k);
        assert(!cc_kernel_term(k, CC_SUCC, 0, 0, 0, 0, 0));
        cc_kernel_clear_error(k);
        assert(!cc_kernel_equiv_type(k, 0x7fffffff, 1));
    }
    cc_work_counters standalone = since(before);
    assert(!memcmp(&standalone, &(cc_work_counters){0}, sizeof standalone));
    cc_kernel_normalize(k, numeral(1));
    before = now();
    assert(!cc_kernel_set_unfolding_hints(k, NULL, 1));
    cc_work_counters after_query = since(before);
    assert(!after_query.failed_queries && !after_query.rejected);
    cc_kernel_clear_error(k);
    cc_work_counters total = now();
    assert(total.rejected <= total.instructions && total.failed_queries <= total.queries);

    /* A valid construction by a standalone helper takes steps of the budget
     * the last operation left, and counts none of them, on a fresh kernel
     * and after an instruction ran out of its budget. */
    cc_kernel *fresh = cc_kernel_new();
    cc_term n = cc_kernel_term(fresh, CC_UNIT, 0, 0, 0, 0, 0);
    assert(cc_kernel_equiv_type(fresh, n, n));
    cc_work_counters untouched;
    cc_kernel_work(fresh, &untouched);
    assert(!memcmp(&untouched, &(cc_work_counters){0}, sizeof untouched));
    cc_kernel_free(fresh);
    cc_judgement_id another = OK(cc_instr_refl(k, OK(cc_instr_apply(k, identity, applied))));
    cc_kernel_set_step_budget(k, 1);
    assert(!cc_instr_step(k, another, 1, NULL, 0, CC_STEP_NORMALIZE));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    before = now();
    cc_term nat_syntax = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_kernel_equiv_type(k, nat_syntax, nat_syntax);
    cc_kernel_clear_error(k);
    cc_work_counters spent_nothing = since(before);
    assert(!memcmp(&spent_nothing, &(cc_work_counters){0}, sizeof spent_nothing));
    cc_kernel_set_step_budget(k, 10000000);

    cc_kernel_free(k);
    puts("kernel work counters: ok");
    return 0;
}
