/* Syntactic comparison (ck_alpha_equal) on raw syntax, deliberately: a
 * successful comparison is not a typing certificate. Free and bound
 * variables must remain distinct, and the memo must stay exact. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>
#include <time.h>

static cc_term universe0(cc_kernel *k) {
    return ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
}
static cc_term lambda(cc_kernel *k, cc_term body) {
    return ck_make(k, CC_LAM, 0, universe0(k), body, 0, 0);
}
static cc_term bound(cc_kernel *k, uint32_t index) {
    return ck_make(k, CC_BOUND, index, 0, 0, 0, 0);
}
/* A free variable: a new entry's reference. */
static cc_term free_variable(cc_kernel *k) {
    cc_entry_id entry = cc_instr_extend(k, cc_instr_unit(k));
    assert(entry);
    return ck_make(k, CC_CONTEXT, entry, 0, 0, 0, 0);
}

/* λ (x : Path(d. U0, tt, tt)). x: the identities on two path types that
 * differ only in their dimension binder's name, so that they are two nodes,
 * alpha-equal, as two term binder names made them in ABI 3. */
static cc_term identity_over(cc_kernel *k, unsigned dimension) {
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term domain = ck_make(k, CC_PATH, dimension, universe0(k), unit, unit, 0);
    return ck_make(k, CC_LAM, 0, domain, bound(k, 0), 0, 0);
}

/* A query has three outcomes: equal, different, or no answer. It never
 * reduces, and failed work must neither write an answer nor become cached. */
static void comparison_query(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term x = free_variable(k), y = free_variable(k);
    cc_term a = identity_over(k, 0), b = identity_over(k, 1);
    assert(a != b);
    bool answer = false;
    cc_kernel_set_step_budget(k, 1);
    assert(!cc_kernel_alpha_equal(k, a, b, &answer) && !answer);
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 10000);
    assert(cc_kernel_alpha_equal(k, a, b, &answer) && answer);
    cc_term free = ck_make(k, CC_LAM, 0, k->nodes[a].child[0], x, 0, 0);
    assert(cc_kernel_alpha_equal(k, a, free, &answer) && !answer);
    cc_term redex = ck_make(k, CC_APP, 0, a, y, 0, 0);
    assert(cc_kernel_alpha_equal(k, redex, y, &answer) && !answer);
    assert(cc_kernel_normalize(k, redex) == y);
    assert(cc_kernel_alpha_equal(k, redex, y, &answer) && !answer);
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    cc_kernel_set_step_budget(k, 1);
    assert(cc_kernel_alpha_equal(k, a, b, &answer) && answer);
    cc_kernel_work(k, &after);
    assert(after.queries == before.queries + 1 && after.query_steps == before.query_steps + 1);
    assert(!cc_kernel_alpha_equal(k, 0, b, &answer) && answer);
    assert(!cc_kernel_alpha_equal(k, a, UINT32_MAX, &answer) && answer);
    assert(!cc_kernel_alpha_equal(k, a, b, NULL));
    cc_kernel_set_deadline_ms(k, 0.01);
    for (clock_t start = clock(); clock() - start < CLOCKS_PER_SEC / 100;) { }
    answer = false;
    assert(!cc_kernel_alpha_equal(k, a, b, &answer) && !answer);
    assert(cc_kernel_error_kind(k) == CC_ERROR_DEADLINE);
    cc_kernel_free(k);
}

/* A different term can acquire the same numeric handle after a rollback;
 * a comparison remembered for the old one must not answer for it. Sharing
 * is off, so that the replacement equals the identity at another handle. */
static void memo_survives_no_rollback(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, 0);
    cc_term identity = lambda(k, bound(k, 0));
    cc_kernel_checkpoint(k);
    cc_term old = lambda(k, bound(k, 1));
    assert(!ck_alpha_equal(k, old, identity));
    cc_kernel_rollback(k);
    cc_term replacement = lambda(k, bound(k, 0));
    assert(replacement == old);
    assert(ck_alpha_equal(k, replacement, identity));
    /* Cumulativity raises a universe, and never lowers or identifies one. */
    cc_term u0 = ck_universe_at(k, 0), u1 = ck_universe_at(k, 1);
    assert(ck_syntactic_cumulative(k, u0, u1));
    assert(!ck_alpha_equal(k, u0, u1));
    assert(!ck_syntactic_cumulative(k, u1, u0));
    assert(!k->error[0]);
    cc_kernel_free(k);
}

/* A scan cut short by the budget answers "no" without looking. The syntax
 * memo records nothing while an error is set, so the same question with
 * budget enough gets the true answer: an entry mentioned, an index that
 * occurs, a dimension free. Instantiation then still renames a dimension
 * binder that would capture, and puts a value under a term binder as it
 * is: a locally closed value has no index a binder could capture. */
static void cut_short_scans_are_forgotten(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term deep = free_variable(k), indexed = bound(k, 0);
    cc_entry_id entry = k->nodes[deep].payload;
    cc_term at_three = ck_make(k, CC_PAPP, ck_interval_variable(k, 3), free_variable(k), 0, 0, 0);
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    for (unsigned i = 0; i < 200; ++i) {
        deep = ck_make(k, CC_SUM, 0, unit, deep, 0, 0);
        indexed = ck_make(k, CC_SUM, 0, unit, indexed, 0, 0);
        at_three = ck_make(k, CC_SUM, 0, unit, at_three, 0, 0);
    }
    k->budget = 50;
    assert(!ck_mentions(k, deep, entry) && k->error[0]);
    cc_kernel_clear_error(k);
    k->budget = 50;
    assert(!ck_index_occurs(k, indexed, 0) && k->error[0]);
    cc_kernel_clear_error(k);
    k->budget = 50;
    assert(ck_free_dims(k, at_three) == 0 && k->error[0]);
    cc_kernel_clear_error(k);
    k->budget = UINT64_C(1000000);
    assert(ck_mentions(k, deep, entry) && ck_index_occurs(k, indexed, 0));
    assert(ck_free_dims(k, at_three) == UINT64_C(1) << 3);
    /* Instantiating ⟨3⟩ (index 0) by it renames the path abstraction. */
    cc_term path = ck_make(k, CC_PLAM, 3, unit, bound(k, 0), 0, 0);
    cc_term renamed = ck_instantiate(k, path, at_three);
    assert(renamed && k->nodes[renamed].payload != 3 && !k->error[0]);
    /* Instantiating λ (y : U0). (index 1), a body whose binder a named
     * variable could have been captured by, leaves the binder and puts the
     * value in by handle. */
    cc_term body = lambda(k, bound(k, 1));
    cc_term instance = ck_instantiate(k, body, deep);
    assert(instance && k->nodes[instance].payload == 0 && k->nodes[instance].child[1] == deep);
    assert(k->nodes[instance].child[0] == k->nodes[body].child[0] && !k->error[0]);
    cc_kernel_free(k);
}

/* L(n + 1) = f (⟨a⟩ L(n)) (⟨b⟩ L(n)) at depth n, over dimensions a and b;
 * R the same over c and d. A term or level binder carries no name, so only
 * dimension binders are renamed. R(n) and L(n) are different nodes,
 * alpha-equal, each reached under 2^(40 - n) renamings. The comparison
 * ignores a renaming where neither side has its dimensions free, so 40
 * levels compare in a few thousand steps, not 2^40: #73's normal-form cache
 * met this as a Convert of two such types running out of budget. Where a
 * dimension occurs free, the renaming still decides. */
static cc_term graph(cc_kernel *k, cc_term f, cc_term bottom, unsigned names,
                     cc_term body_of(cc_kernel *, cc_term, unsigned)) {
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), t = bottom;
    for (uint32_t n = 0; n < 40; ++n) {
        cc_term first = ck_make(k, CC_PLAM, names, unit, body_of(k, t, names), 0, 0);
        cc_term second = ck_make(k, CC_PLAM, names + 1, unit, body_of(k, t, names + 1), 0, 0);
        t = ck_make(k, CC_APP, 0, ck_make(k, CC_APP, 0, f, first, 0, 0), second, 0, 0);
    }
    return t;
}
static cc_term unused(cc_kernel *k, cc_term t, unsigned name) { (void)k; (void)name; return t; }
/* t @ a, under the binder of a. */
static cc_term applied(cc_kernel *k, cc_term t, unsigned name) {
    return ck_make(k, CC_PAPP, ck_interval_variable(k, name), t, 0, 0, 0);
}
static bool equal_within(cc_kernel *k, cc_term a, cc_term b, uint64_t steps) {
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    ck_operation(k, CC_WORK_QUERY);
    bool equal = ck_alpha_equal(k, a, b);
    assert(!k->error[0]);
    ck_standalone(k);
    cc_kernel_work(k, &after);
    assert(after.query_steps - before.query_steps < steps);
    return equal;
}
static void renamings_share_work(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term f = free_variable(k), x = free_variable(k), z = free_variable(k);
    cc_term left = graph(k, f, x, 0, unused), right = graph(k, f, x, 2, unused);
    assert(left != right && equal_within(k, left, right, 10000));
    /* A difference at the bottom is found as fast. */
    assert(!equal_within(k, left, graph(k, f, z, 4, unused), 10000));
    /* Bodies that mention their binder, as t @ a: the renaming applies, and
     * a dimension bound on one side is not the same dimension free on the
     * other. */
    cc_term used = graph(k, f, x, 6, applied);
    assert(equal_within(k, used, graph(k, f, x, 8, applied), 1000000));
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term bound_there = ck_make(k, CC_PLAM, 10, unit, applied(k, used, 10), 0, 0);
    cc_term free_there = ck_make(k, CC_PLAM, 11, unit, applied(k, used, 10), 0, 0);
    assert(!equal_within(k, bound_there, free_there, 1000000));
    /* So for a term variable: bound by its λ, an index, it is not the free
     * variable x. */
    cc_term by_index = ck_make(k, CC_LAM, 0, unit, ck_make(k, CC_APP, 0, used, bound(k, 0), 0, 0), 0, 0);
    cc_term by_entry = ck_make(k, CC_LAM, 0, unit, ck_make(k, CC_APP, 0, used, x, 0, 0), 0, 0);
    assert(!equal_within(k, by_index, by_entry, 1000000));
    /* The first review of #77: a formula-bearing node made before its
     * formula exists would keep a mask without the formula's dimensions,
     * and a renaming of them could be dropped. Such a node is refused. */
    uint32_t unregistered = 60000;
    assert(!cc_kernel_get_formula(k, unregistered));
    assert(!cc_kernel_term(k, CC_PAPP, unregistered, x, 0, 0, 0));
    assert(strstr(cc_kernel_error(k), "names no registered formula"));
    cc_kernel_clear_error(k);
    assert(!cc_kernel_term(k, CC_TUBE, unregistered, x, 0, 0, 0));
    cc_kernel_clear_error(k);
    cc_kernel_free(k);
}

int main(void) {
    comparison_query();
    renamings_share_work();
    memo_survives_no_rollback();
    cut_short_scans_are_forgotten();
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term x = free_variable(k), p = free_variable(k);
    k->budget = UINT64_C(1000000);
    cc_term nat = universe0(k);
    cc_term zero = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    /* λ (x : U0). x and λ (y : U0). y are one node: a binder has no name. */
    cc_term identity = lambda(k, bound(k, 0));
    assert(lambda(k, bound(k, 0)) == identity);
    cc_term free_x = lambda(k, x);
    assert(ck_alpha_equal(k, identity, identity));
    assert(!ck_alpha_equal(k, identity, free_x));
    assert(!ck_alpha_equal(k, free_x, identity));
    assert(ck_alpha_equal(k, free_x, free_x));
    /* λ x. λ y. x against λ y. λ x. x: the outer binder's variable is not
     * the inner one's. A loose index is no entry. */
    assert(!ck_alpha_equal(k, lambda(k, lambda(k, bound(k, 1))), lambda(k, lambda(k, bound(k, 0)))));
    assert(!ck_alpha_equal(k, bound(k, 0), x) && !ck_alpha_equal(k, bound(k, 0), bound(k, 1)));

    cc_term p_type = ck_make(k, CC_PATH, 2, nat, zero, zero, 0);
    cc_term pi = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), p, p_type, 0, 0);
    cc_term pj = ck_make(k, CC_PAPP, ck_interval_variable(k, 1), p, p_type, 0, 0);
    cc_term line_i = ck_make(k, CC_PLAM, 0, nat, pi, 0, 0);
    cc_term line_j = ck_make(k, CC_PLAM, 1, nat, pj, 0, 0);
    cc_term free_i = ck_make(k, CC_PLAM, 1, nat, pi, 0, 0);
    assert(ck_alpha_equal(k, line_i, line_j));
    assert(!ck_alpha_equal(k, line_i, free_i));
    assert(!ck_alpha_equal(k, free_i, line_i));
    assert(ck_alpha_equal(k, line_i, line_j));
    assert(ck_alpha_equal(k, free_i, free_i));

    /* Homogeneous composition does not bind its type; transport does not
     * bind its face. A composition direction never binds a tube FACE. */
    cc_term hcomp = ck_make(k, CC_HCOMP, 0, pi, 0, zero, 0);
    assert(ck_free_dims(k, hcomp) & UINT64_C(1));
    cc_term side = ck_make(k, CC_TUBE, ck_endpoint_face(k, 0, 0), zero, 0, 0, 0);
    cc_term comp = ck_make(k, CC_COMP, 0, nat, side, zero, 0);
    cc_term trans = ck_make(k, CC_TRANS, 0, pi, side, zero, 0);
    assert(ck_free_dims(k, comp) & UINT64_C(1));
    assert(ck_free_dims(k, trans) & UINT64_C(1));
    cc_formula one;
    cc_init(&one, CC_INTERVAL);
    assert(cc_one(&one) == CC_OK);
    cc_term specialized = ck_dimension_substitute(k, hcomp, 0, &one);
    assert(!(ck_free_dims(k, specialized) & UINT64_C(1)));
    specialized = ck_dimension_substitute(k, comp, 0, &one);
    cc_node tube = k->nodes[k->nodes[specialized].child[1]];
    assert(cc_kernel_get_formula(k, tube.payload)->length == 0);
    cc_clear(&one);

    /* A closed shared sum DAG has 2^24 unfolded branches. Beneath
     * differently named path abstractions, its nodes are compared once per
     * scope. */
    cc_term shared = zero;
    for (unsigned i = 0; i < 24; ++i)
        shared = ck_make(k, CC_SUM, 0, shared, shared, 0, 0);
    assert(equal_within(k, ck_make(k, CC_PLAM, 0, nat, shared, 0, 0), ck_make(k, CC_PLAM, 1, nat, shared, 0, 0), 1000));
    puts("Scoped comparison of a shared DAG takes fewer than 1,000 steps.");
    cc_kernel_free(k);
    return 0;
}
