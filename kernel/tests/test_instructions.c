/* The instruction kernel derives add, lt and lt_succ forward, as THTH did:
 * every rule application is an instruction, and every reduction is named
 * and placed. The term checker then accepts what the instructions defined. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;

static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) {
        fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k));
        assert(0);
    }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)

static void rejects(uint32_t id, const char *fragment) {
    assert(!id);
    if (!strstr(cc_kernel_error(k), fragment)) {
        fprintf(stderr, "expected \"%s\", got \"%s\"\n", fragment, cc_kernel_error(k));
        assert(0);
    }
    cc_kernel_clear_error(k);
}

static cc_term term_of(cc_judgement_id j) { cc_term t; assert(cc_kernel_fact(k, j, NULL, &t, NULL, NULL)); return t; }
static cc_term other_of(cc_judgement_id j) { cc_term t; assert(cc_kernel_fact(k, j, NULL, NULL, &t, NULL)); return t; }
static cc_term type_of(cc_judgement_id j) { cc_term t; assert(cc_kernel_fact(k, j, NULL, NULL, NULL, &t)); return t; }
static size_t context_size(cc_judgement_id j) { size_t n = 0; while (cc_kernel_fact_context(k, j, n)) ++n; return n; }
static cc_term_kind kind(cc_term t) { cc_term_kind result; assert(cc_kernel_node(k, t, &result, NULL, NULL)); return result; }

/* Contract one redex of side 1 of an equality, at a position. */
#define AT(...) (const uint8_t[]){__VA_ARGS__}, sizeof((uint8_t[]){__VA_ARGS__})
#define STEP(eq, rule, ...) OK(cc_instr_step(k, (eq), 1, __VA_ARGS__, (rule)))
#define ROOT NULL, 0

static unsigned successors(cc_term t) {
    unsigned count = 0;
    cc_term children[4];
    for (cc_term_kind which; (which = kind(t)) == CC_SUCC; ++count) {
        assert(cc_kernel_node(k, t, NULL, NULL, children));
        t = children[0];
    }
    assert(kind(t) == CC_ZERO);
    return count;
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    enum { N = 1, M, K, A, B, X, P, H, W = 9, Q = 20 };

    /* add(a, b) := natrec(λx. Nat, a, λp. λh. succ(h), b). The motive's
     * applications are beta-reduced where the rules need a plain Nat. */
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_entry_id a = OK(cc_instr_extend(k, nat, A)), b = OK(cc_instr_extend(k, nat, B));
    cc_entry_id x = OK(cc_instr_extend(k, nat, X)), p = OK(cc_instr_extend(k, nat, P));
    cc_judgement_id motive = OK(cc_instr_lambda(k, x, nat));
    cc_judgement_id zero = OK(cc_instr_zero(k));
    cc_judgement_id at_zero = OK(cc_instr_apply(k, motive, zero));
    cc_judgement_id base = OK(cc_instr_convert(k, OK(cc_instr_variable(k, a)),
        OK(cc_instr_symmetry(k, STEP(OK(cc_instr_refl(k, at_zero)), CC_STEP_BETA, ROOT)))));
    cc_judgement_id pv = OK(cc_instr_variable(k, p));
    cc_judgement_id at_p = OK(cc_instr_apply(k, motive, pv));
    cc_entry_id h = OK(cc_instr_extend(k, at_p, H));
    cc_judgement_id hv = OK(cc_instr_convert(k, OK(cc_instr_variable(k, h)), STEP(OK(cc_instr_refl(k, at_p)), CC_STEP_BETA, ROOT)));
    assert(context_size(hv) == 2);
    cc_judgement_id at_succ = OK(cc_instr_apply(k, motive, OK(cc_instr_succ(k, pv))));
    cc_judgement_id next = OK(cc_instr_convert(k, OK(cc_instr_succ(k, hv)),
        OK(cc_instr_symmetry(k, STEP(OK(cc_instr_refl(k, at_succ)), CC_STEP_BETA, ROOT)))));
    cc_judgement_id step = OK(cc_instr_lambda(k, p, OK(cc_instr_lambda(k, h, next))));
    assert(context_size(step) == 0);
    cc_judgement_id bv = OK(cc_instr_variable(k, b));
    cc_judgement_id recursion = OK(cc_instr_nat_elim(k, motive, base, step, bv));
    assert(context_size(recursion) == 2);
    cc_judgement_id sum = OK(cc_instr_convert(k, recursion,
        STEP(OK(cc_instr_refl(k, OK(cc_instr_apply(k, motive, bv)))), CC_STEP_BETA, ROOT)));
    cc_judgement_id add = OK(cc_instr_define(k, 100, OK(cc_instr_lambda(k, a, OK(cc_instr_lambda(k, b, sum))))));

    /* The term checker computes with the instructions' definition. */
    cc_term raw_zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term two = cc_kernel_term(k, CC_SUCC, 0, cc_kernel_term(k, CC_SUCC, 0, raw_zero, 0, 0, 0), 0, 0, 0);
    cc_term three = cc_kernel_term(k, CC_SUCC, 0, two, 0, 0, 0);
    cc_term five = cc_kernel_term(k, CC_APP, 0, cc_kernel_term(k, CC_APP, 0, term_of(add), two, 0, 0), three, 0, 0);
    cc_checked_result checked;
    assert(cc_kernel_check(k, five, cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0), NULL, 0, &checked));
    assert(successors(cc_kernel_normalize(k, checked.expression)) == 5);

    /* lt(n, m) := Σ(k : Nat). succ(add(n, k)) = m. */
    cc_entry_id n = OK(cc_instr_extend(k, nat, N)), m = OK(cc_instr_extend(k, nat, M)), kk = OK(cc_instr_extend(k, nat, K));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_judgement_id nv = OK(cc_instr_variable(k, n));
    cc_judgement_id n_plus_k = OK(cc_instr_apply(k, OK(cc_instr_apply(k, add, nv)), OK(cc_instr_variable(k, kk))));
    cc_judgement_id equation = OK(cc_instr_path(k, i, nat, OK(cc_instr_succ(k, n_plus_k)), OK(cc_instr_variable(k, m))));
    assert(context_size(equation) == 3);
    cc_judgement_id lt = OK(cc_instr_define(k, 101,
        OK(cc_instr_lambda(k, n, OK(cc_instr_lambda(k, m, OK(cc_instr_sigma(k, kk, equation))))))));

    /* lt_succ : Π(n : Nat). lt(n, succ(n)) := λn. (0, <i> succ(n)).
     * The goal unfolds by one delta and two betas, highlighted in turn. */
    cc_judgement_id sn = OK(cc_instr_succ(k, nv));
    cc_judgement_id goal = OK(cc_instr_apply(k, OK(cc_instr_apply(k, lt, nv)), sn));
    cc_judgement_id unfolded = OK(cc_instr_refl(k, goal));
    unfolded = STEP(unfolded, CC_STEP_DELTA, AT(0, 0));
    unfolded = STEP(unfolded, CC_STEP_BETA, AT(0));
    unfolded = STEP(unfolded, CC_STEP_BETA, ROOT);
    assert(kind(other_of(unfolded)) == CC_SIGMA);
    cc_judgement_id sigma = OK(cc_instr_side(k, unfolded, 1));
    cc_judgement_id expected = OK(cc_instr_family(k, sigma, zero));
    /* succ(add(n, 0)) computes to succ(n) inside the path type. */
    cc_judgement_id computed = OK(cc_instr_refl(k, expected));
    computed = STEP(computed, CC_STEP_DELTA, AT(1, 0, 0, 0));
    computed = STEP(computed, CC_STEP_BETA, AT(1, 0, 0));
    computed = STEP(computed, CC_STEP_BETA, AT(1, 0));
    computed = STEP(computed, CC_STEP_IOTA, AT(1, 0));
    cc_judgement_id loop = OK(cc_instr_path_lambda(k, i, sn));
    assert(context_size(loop) == 1);
    cc_judgement_id witness = OK(cc_instr_convert(k, loop, OK(cc_instr_symmetry(k, computed))));
    cc_judgement_id proof = OK(cc_instr_pair(k, sigma, zero, witness));
    proof = OK(cc_instr_convert(k, proof, OK(cc_instr_symmetry(k, unfolded))));
    assert(term_of(goal) == type_of(proof));
    cc_judgement_id lt_succ = OK(cc_instr_define(k, 102, OK(cc_instr_lambda(k, n, proof))));
    cc_term value;
    assert(cc_kernel_definition(k, term_of(lt_succ), NULL, &value, NULL));
    assert(cc_kernel_check(k, value, type_of(lt_succ), NULL, 0, &checked));

    /* Replacement under a binder: the goal's entry n is the binder's. */
    cc_judgement_id statement = OK(cc_instr_pi(k, n, goal));
    assert(context_size(statement) == 0);
    cc_judgement_id opened = OK(cc_instr_replace(k, OK(cc_instr_refl(k, statement)), 1, AT(1), unfolded));
    assert(context_size(opened) == 0 && kind(other_of(opened)) == CC_PI);
    cc_term children[4];
    assert(cc_kernel_node(k, other_of(opened), NULL, NULL, children) && kind(children[1]) == CC_SIGMA);
    rejects(cc_instr_replace(k, OK(cc_instr_refl(k, statement)), 1, AT(0), unfolded), "not the equality's left side");

    /* A bound name must correspond to an entry of the binder's type. */
    cc_term raw_nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term identity = cc_kernel_define(k, 103, cc_kernel_term(k, CC_LAM, W, raw_nat, cc_kernel_term(k, CC_VAR, W, 0, 0, 0, 0), 0, 0), 0);
    assert(identity);
    cc_judgement_id identity_value = STEP(OK(cc_instr_refl(k, OK(cc_instr_lookup(k, identity)))), CC_STEP_DELTA, ROOT);
    cc_entry_id w = OK(cc_instr_extend(k, OK(cc_instr_unit(k)), W));
    rejects(cc_instr_replace(k, identity_value, 1, AT(1), OK(cc_instr_refl(k, OK(cc_instr_variable(k, w))))), "different types");

    /* An entry cannot be discharged while another depends on it. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, nat, nv, nv));
    cc_entry_id q = OK(cc_instr_extend(k, loop_type, Q));
    rejects(cc_instr_lambda(k, n, OK(cc_instr_variable(k, q))), "still depends");
    rejects(cc_instr_extend(k, nat, N), "already names");

    /* Paths compute at a path lambda, and at an endpoint of the annotation. */
    cc_judgement_id end = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, loop, 0, 1)))), CC_STEP_PATH, ROOT);
    assert(other_of(end) == term_of(sn));
    cc_judgement_id start = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, OK(cc_instr_variable(k, q)), 0, 0)))), CC_STEP_PATH, ROOT);
    assert(other_of(start) == term_of(nv));

    /* Two dimension entries with one index never meet. */
    cc_entry_id j = OK(cc_instr_dimension(k, 0));
    cc_judgement_id at_i = OK(cc_instr_path_apply(k, loop, i, 0)), at_j = OK(cc_instr_path_apply(k, loop, j, 0));
    rejects(cc_instr_apply(k, OK(cc_instr_apply(k, add, at_i)), at_j), "one index");

    /* Mismatches are reported with both types. */
    cc_term found, wanted;
    assert(!cc_instr_apply(k, add, OK(cc_instr_variable(k, w))));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH && cc_kernel_mismatch(k, &found, &wanted));
    assert(kind(found) == CC_UNIT && kind(wanted) == CC_NAT);
    cc_kernel_clear_error(k);
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, nv)), 0, ROOT, CC_STEP_BETA), "Beta needs");
    rejects(cc_instr_define(k, 104, nv), "closed");

    /* Normalization, eta and cumulativity. */
    cc_judgement_id numeral = OK(cc_instr_succ(k, OK(cc_instr_succ(k, zero))));
    cc_judgement_id four = OK(cc_instr_apply(k, OK(cc_instr_apply(k, add, numeral)), numeral));
    assert(successors(other_of(STEP(OK(cc_instr_refl(k, four)), CC_STEP_NORMALIZE, ROOT))) == 4);
    assert(kind(other_of(OK(cc_instr_eta(k, add)))) == CC_LAM);
    assert(kind(other_of(OK(cc_instr_eta(k, loop)))) == CC_PLAM);
    cc_judgement_id lifted = OK(cc_instr_lift(k, nat, OK(cc_instr_universe(k, 1))));
    assert(kind(type_of(lifted)) == CC_U);
    rejects(cc_instr_lift(k, zero, OK(cc_instr_universe(k, 0))), "not included");

    /* A rollback drops the judgements made since the checkpoint. */
    cc_kernel_checkpoint(k);
    cc_judgement_id scratch = OK(cc_instr_succ(k, numeral));
    cc_kernel_rollback(k);
    assert(!cc_kernel_fact(k, scratch, NULL, NULL, NULL, NULL));
    assert(cc_kernel_fact(k, numeral, NULL, NULL, NULL, NULL));
    assert(OK(cc_instr_lookup(k, term_of(lt_succ))));

    cc_kernel_free(k);
    puts("instruction tests passed");
    return 0;
}
