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

static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info result; assert(cc_kernel_judgement(k, j, &result)); return result; }
static cc_term term_of(cc_judgement_id j) { return info(j).term; }
static cc_term other_of(cc_judgement_id j) { return info(j).other; }
static cc_term type_of(cc_judgement_id j) { return info(j).type; }
static size_t context_size(cc_judgement_id j) { size_t n = 0; while (cc_kernel_judgement_context(k, j, n)) ++n; return n; }
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
    rejects(cc_instr_extend(k, OK(cc_instr_unit(k)), N), "already names");

    /* Paths compute at a path lambda, and at an endpoint of the annotation. */
    cc_judgement_id end = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, loop, 0, 1)))), CC_STEP_PATH, ROOT);
    assert(other_of(end) == term_of(sn));
    cc_judgement_id start = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, OK(cc_instr_variable(k, q)), 0, 0)))), CC_STEP_PATH, ROOT);
    assert(other_of(start) == term_of(nv));

    cc_judgement_id numeral = OK(cc_instr_succ(k, OK(cc_instr_succ(k, zero))));
    cc_judgement_id four = OK(cc_instr_apply(k, OK(cc_instr_apply(k, add, numeral)), numeral));

    /* Rewriting a typing judgement in place: its type by a step, as THTH's
     * HighType with a pointed reduction, and its term by a replacement. */
    cc_judgement_id retyped = OK(cc_instr_step(k, proof, 2, AT(0, 0), CC_STEP_DELTA));
    retyped = OK(cc_instr_step(k, retyped, 2, AT(0), CC_STEP_BETA));
    retyped = OK(cc_instr_step(k, retyped, 2, ROOT, CC_STEP_BETA));
    assert(term_of(retyped) == term_of(proof) && type_of(retyped) == other_of(unfolded));
    cc_judgement_id reduced = OK(cc_instr_step(k, OK(cc_instr_refl(k, four)), 0, ROOT, CC_STEP_NORMALIZE));
    assert(successors(term_of(reduced)) == 4 && successors(term_of(OK(cc_instr_step(k, four, 0, ROOT, CC_STEP_NORMALIZE)))) == 4);
    rejects(cc_instr_step(k, four, 1, ROOT, CC_STEP_NORMALIZE), "sides");
    cc_judgement_id swapped = OK(cc_instr_replace(k, goal, 0, ROOT, unfolded));
    assert(term_of(swapped) == other_of(unfolded) && type_of(swapped) == type_of(goal));

    /* The graph records each derivation once: its rule, premises, entry,
     * operands and highlighted position. Dimension entries are their index. */
    assert(OK(cc_instr_dimension(k, 0)) == i && OK(cc_instr_extend(k, nat, N)) == n);
    assert(OK(cc_instr_apply(k, OK(cc_instr_apply(k, lt, nv)), sn)) == goal && OK(cc_instr_nat(k)) == nat);
    cc_judgement_info derived = info(goal);
    assert(derived.rule == CC_INSTR_APPLY && info(derived.premise[0]).rule == CC_INSTR_APPLY && derived.premise[1] == sn);
    derived = info(computed);
    assert(derived.rule == CC_INSTR_STEP && derived.operand[0] == 1 && derived.operand[1] == CC_STEP_IOTA);
    assert(derived.depth == 2 && derived.position[0] == 1 && derived.position[1] == 0);
    assert(OK(cc_instr_step(k, derived.premise[0], 1, AT(1, 0), CC_STEP_IOTA)) == computed);
    assert(info(opened).rule == CC_INSTR_REPLACE && info(opened).premise[1] == unfolded);
    cc_judgement_id source;
    bool dimension;
    assert(cc_kernel_entry(k, h, NULL, NULL, &dimension, &source) && !dimension && source == at_p);
    assert(cc_kernel_entry(k, i, NULL, NULL, &dimension, &source) && dimension && !source);
    for (cc_judgement_id id = 1; id < cc_kernel_judgement_count(k); ++id)
        for (unsigned slot = 0; slot < 4; ++slot)
            assert(info(id).premise[slot] < id);

    /* An endpoint substitutes into a judgement and discharges the dimension. */
    cc_judgement_id at_one = OK(cc_instr_endpoint(k, OK(cc_instr_path_apply(k, loop, i, 0)), i, 1));
    assert(context_size(at_one) == 1 && kind(term_of(at_one)) == CC_PAPP);
    assert(other_of(STEP(OK(cc_instr_refl(k, at_one)), CC_STEP_PATH, ROOT)) == term_of(sn));

    /* A path at a compound formula, and composition along a second
     * dimension with tubes on the faces i = 0 and i = 1. */
    cc_formula formula;
    cc_init(&formula, CC_INTERVAL);
    assert(cc_generator(&formula, 0, false) == CC_OK);
    cc_formula_id reversed = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id at_reversed = OK(cc_instr_path_at(k, loop, reversed));
    assert(context_size(at_reversed) == 2 && type_of(at_reversed) == type_of(sn));
    cc_formula_id faces[2];
    for (unsigned side = 0; side < 2; ++side) {
        cc_init(&formula, CC_FACE);
        assert(cc_generator(&formula, 0, side == 1) == CC_OK);
        faces[side] = cc_kernel_formula(k, &formula);
        cc_clear(&formula);
    }
    cc_entry_id j2 = OK(cc_instr_dimension(k, 1));
    cc_judgement_id system = OK(cc_instr_system(k, j2, nat, nv));
    cc_judgement_id stay = OK(cc_instr_refl(k, nv));
    for (unsigned side = 0; side < 2; ++side)
        system = OK(cc_instr_system_tube(k, system, faces[side], nv, stay));
    rejects(cc_instr_system_tube(k, system, faces[0], nv, stay), "Overlapping");
    rejects(cc_instr_step(k, system, 0, ROOT, CC_STEP_NORMALIZE), "closed by Comp");
    cc_judgement_id composed = OK(cc_instr_comp(k, system));
    assert(kind(term_of(composed)) == CC_COMP && kind(type_of(composed)) == CC_NAT);
    /* The context is n and the face's dimension; the composition's is bound. */
    assert(context_size(composed) == 2);
    cc_assumption assumptions[] = {{N, type_of(nv)}};
    assert(cc_kernel_check_in_cube(k, term_of(composed), type_of(composed), assumptions, 1, 1, &checked));
    rejects(cc_instr_system(k, i, nat, OK(cc_instr_path_apply(k, loop, i, 0))), "may not use its dimension");

    /* Mismatches are reported with both types. */
    cc_term found, wanted;
    assert(!cc_instr_apply(k, add, OK(cc_instr_variable(k, w))));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH && cc_kernel_mismatch(k, &found, &wanted));
    assert(kind(found) == CC_UNIT && kind(wanted) == CC_NAT);
    cc_kernel_clear_error(k);
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, nv)), 0, ROOT, CC_STEP_BETA), "Beta needs");
    rejects(cc_instr_define(k, 104, nv), "closed");

    /* Normalization, eta and cumulativity. */
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
    cc_judgement_info unused;
    assert(!cc_kernel_judgement(k, scratch, &unused) && cc_kernel_judgement(k, numeral, &unused));
    /* A truncated judgement's id is issued again, and never confused. */
    cc_judgement_id other = OK(cc_instr_succ(k, four));
    assert(other == scratch && info(other).premise[0] == four);
    cc_judgement_id repeated = OK(cc_instr_succ(k, numeral));
    assert(repeated != other && info(repeated).premise[0] == numeral);
    assert(OK(cc_instr_lookup(k, term_of(lt_succ))));

    cc_kernel_free(k);
    puts("instruction tests passed");
    return 0;
}
