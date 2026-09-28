/* Instruction isolation (work plan I1.2a). An instruction's side conditions
 * are syntactic, and so are the reducers that Step, HComp and Trans call:
 * an untrusted query made before an instruction cannot change whether it is
 * accepted, and conversion never decides a reduction step. The work-plan
 * audit of 2026-09-28 (docs/roadmaps/audits/2026-09-28-audit.md, finding 1)
 * found both broken; these are its regressions. */
#include "cubical_kernel.h"
#include "term_internal.h"
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
static cc_term_kind kind(cc_term t) { cc_term_kind result; assert(cc_kernel_node(k, t, &result, NULL, NULL)); return result; }

/* Reduce side 1 of refl(t) at its root by the rule: t ≡ t', and return t'. */
static cc_term reduct(cc_judgement_id typing, cc_step_rule rule) {
    return other_of(OK(cc_instr_step(k, OK(cc_instr_refl(k, typing)), 1, NULL, 0, rule)));
}

/* The audit's probe. x : (λ (a : U0). a)(Nat) is not syntactically an
 * argument of λ (y : Nat). y, so Apply refuses it. Asking conversion, weak
 * heads, normal forms or the old checker about the two types in between
 * changes nothing: before the fix, a successful conversion query entered
 * the memo that the syntactic comparison reads, and Apply then accepted. */
static void queries_leave_acceptance_unchanged(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term l0 = cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0);
    cc_judgement_id u0 = OK(cc_instr_universe(k, l0)), nat = OK(cc_instr_nat(k));
    cc_entry_id a = OK(cc_instr_extend(k, u0, 100));
    cc_judgement_id identity = OK(cc_instr_lambda(k, a, OK(cc_instr_variable(k, a))));
    cc_judgement_id beta_nat = OK(cc_instr_apply(k, identity, nat));
    cc_entry_id x = OK(cc_instr_extend(k, beta_nat, 101)), y = OK(cc_instr_extend(k, nat, 102));
    cc_judgement_id argument = OK(cc_instr_variable(k, x));
    cc_judgement_id function = OK(cc_instr_lambda(k, y, OK(cc_instr_variable(k, y))));
    cc_term redex = term_of(beta_nat), plain = term_of(nat);
    rejects(cc_instr_apply(k, function, argument), "wrong type");

    assert(cc_kernel_convertible(k, redex, plain, 10000));
    rejects(cc_instr_apply(k, function, argument), "wrong type");
    assert(cc_kernel_whnf(k, redex) == plain && cc_kernel_normalize(k, redex) == plain);
    rejects(cc_instr_apply(k, function, argument), "wrong type");
    /* The old checker accepts the application, by conversion. */
    cc_checked_result checked;
    cc_term application = cc_kernel_term(k, CC_APP, 0, term_of(function), term_of(argument), 0, 0);
    assert(cc_kernel_check(k, application, plain, (cc_assumption[]){{101, redex}}, 1, &checked));
    rejects(cc_instr_apply(k, function, argument), "wrong type");

    /* The derivation instructions accept: a Beta step converts x's type. */
    cc_judgement_id beta = OK(cc_instr_step(k, OK(cc_instr_refl(k, beta_nat)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id applied = OK(cc_instr_apply(k, function, OK(cc_instr_convert(k, argument, beta))));
    assert(type_of(applied) == plain);
    cc_kernel_free(k);
}

/* The memo keeps the two kinds of evidence apart: a success of conversion
 * is reused by conversion, never by the syntactic comparison, whichever
 * runs first. */
static void folded_comparison_reads_only_its_own_results(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term x = cc_kernel_term(k, CC_VAR, 10, 0, 0, 0, 0);
    cc_term z = cc_kernel_term(k, CC_VAR, 11, 0, 0, 0, 0);
    cc_term identity = cc_kernel_term(k, CC_LAM, 11, nat, z, 0, 0);
    cc_term beta_x = cc_kernel_term(k, CC_APP, 0, identity, x, 0, 0);
    assert(cc_kernel_convertible(k, beta_x, x, 0));
    assert(!ck_alpha_equal(k, beta_x, x) && !k->error[0]);
    assert(cc_kernel_convertible(k, beta_x, x, 0));
    assert(!ck_alpha_equal(k, beta_x, x) && !k->error[0]);
    /* Syntactic equality is evidence for both. */
    cc_term w = cc_kernel_term(k, CC_VAR, 12, 0, 0, 0, 0);
    cc_term renamed = cc_kernel_term(k, CC_LAM, 12, nat, w, 0, 0);
    assert(ck_alpha_equal(k, identity, renamed));
    assert(cc_kernel_convertible(k, identity, renamed, 0));
    cc_kernel_free(k);
}

/* The reducers decide eta syntactically. (fst p, snd q) is p, and
 * glue [φ ↦ b|φ] (unglue b) is b, only when the two sides are the same
 * syntax up to bound names. Otherwise Whnf leaves the redex, and Normalize,
 * which reduces the parts first, reaches the contraction when their normal
 * forms agree. Before the fix both rules asked conversion. */
static void reduction_decides_eta_syntactically(void) {
    k = cc_kernel_new();
    assert(k);
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_entry_id n = OK(cc_instr_extend(k, nat, 200));
    cc_judgement_id sigma = OK(cc_instr_sigma(k, n, nat));
    cc_entry_id p = OK(cc_instr_extend(k, sigma, 201)), q = OK(cc_instr_extend(k, sigma, 202));
    cc_judgement_id pv = OK(cc_instr_variable(k, p));
    cc_judgement_id identity = OK(cc_instr_lambda(k, q, OK(cc_instr_variable(k, q))));
    cc_judgement_id beta_p = OK(cc_instr_apply(k, identity, pv));
    cc_judgement_id first = OK(cc_instr_first(k, pv));
    cc_judgement_id same = OK(cc_instr_pair(k, sigma, first, OK(cc_instr_second(k, pv))));
    assert(reduct(same, CC_STEP_WHNF) == term_of(pv));
    cc_judgement_id other = OK(cc_instr_pair(k, sigma, first, OK(cc_instr_second(k, beta_p))));
    /* Conversion, which is untrusted, finds p and (λ q. q)(p) equal. Asked
     * first, about the very pair the reducer compares, its answer must not
     * reach the reducer's syntactic comparison. */
    assert(cc_kernel_convertible(k, term_of(pv), term_of(beta_p), 0));
    assert(kind(reduct(other, CC_STEP_WHNF)) == CC_PAIR);
    assert(reduct(other, CC_STEP_NORMALIZE) == term_of(pv));
    /* Conversion identifies the pair with p, by surjective pairing. */
    assert(cc_kernel_convertible(k, term_of(other), term_of(pv), 0));

    /* Glue over (λ (T : U0). T)(Nat) and over Nat, each with one piece on
     * the empty face, which needs no equivalence and no image. */
    cc_term l0 = cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0);
    cc_entry_id t = OK(cc_instr_extend(k, OK(cc_instr_universe(k, l0)), 203));
    cc_judgement_id beta_nat = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, t, OK(cc_instr_variable(k, t)))), nat));
    cc_formula formula;
    cc_init(&formula, CC_FACE);
    assert(cc_zero(&formula) == CC_OK);
    cc_formula_id never = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id unit = OK(cc_instr_unit(k)), point = OK(cc_instr_point(k)), zero = OK(cc_instr_zero(k));
    cc_judgement_id over_redex = OK(cc_instr_glue(k, OK(cc_instr_glue_piece(k, OK(cc_instr_glue_base(k, beta_nat)), never, unit, zero))));
    cc_judgement_id over_nat = OK(cc_instr_glue(k, OK(cc_instr_glue_piece(k, OK(cc_instr_glue_base(k, nat)), never, unit, zero))));
    cc_entry_id b = OK(cc_instr_extend(k, over_redex, 204));
    cc_judgement_id bv = OK(cc_instr_variable(k, b));
    cc_judgement_id unglued = OK(cc_instr_unglue(k, bv));
    /* At b's own Glue type, the Glue term of unglue b is b. */
    cc_judgement_id own = OK(cc_instr_glue_term(k, OK(cc_instr_glue_term_piece(k,
        OK(cc_instr_glue_term_base(k, over_redex, unglued)), point, 0))));
    assert(reduct(own, CC_STEP_WHNF) == term_of(bv));
    /* At the Glue type over Nat, equal to b's only after a Beta step, Whnf
     * leaves a Glue term; Normalize reduces both types first. */
    cc_judgement_id beta = OK(cc_instr_step(k, OK(cc_instr_refl(k, beta_nat)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id at_nat = OK(cc_instr_glue_term(k, OK(cc_instr_glue_term_piece(k,
        OK(cc_instr_glue_term_base(k, over_nat, OK(cc_instr_convert(k, unglued, beta)))), point, 0))));
    /* The two Glue types are convertible, and asking first changes nothing
     * for the reducer, which compares exactly them. */
    assert(cc_kernel_convertible(k, term_of(over_nat), term_of(over_redex), 0));
    assert(kind(reduct(at_nat, CC_STEP_WHNF)) == CC_GLUE_TERM);
    assert(reduct(at_nat, CC_STEP_NORMALIZE) == term_of(bv));
    /* The Glue step reaches it too, normalizing only the two Glue types, and
     * refuses a Glue term whose base is no unglue, and any other term. */
    assert(reduct(at_nat, CC_STEP_GLUE) == term_of(bv));
    cc_judgement_id plain_glue = OK(cc_instr_glue_term(k, OK(cc_instr_glue_term_piece(k,
        OK(cc_instr_glue_term_base(k, over_nat, OK(cc_instr_variable(k, n)))), point, 0))));
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, plain_glue)), 1, NULL, 0, CC_STEP_GLUE), "A Glue step needs");
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, pv)), 1, NULL, 0, CC_STEP_GLUE), "A Glue step needs");
    /* Conversion has Glue eta of its own, by conversion. */
    assert(cc_kernel_convertible(k, term_of(at_nat), term_of(bv), 0));
    cc_kernel_free(k);
}

/* G(d) = Glue [d = 0 ↦ (Unit, e)] Unit, as raw syntax. */
static cc_term glue_line(cc_term unit, cc_term e, unsigned d) {
    cc_formula face;
    cc_init(&face, CC_FACE);
    assert(cc_generator(&face, d, false) == CC_OK);
    cc_formula_id at_zero = cc_kernel_formula(k, &face);
    cc_clear(&face);
    return ck_make(k, CC_GLUE, 0, unit, ck_make(k, CC_GLUE_SYSTEM, at_zero, unit, e, 0, 0), 0, 0);
}

/* The review of #72 found two contractions the syntactic rules had lost.
 * Normalize must still make Glue eta on a nonempty face, where the base's
 * restriction is a redex: with p a path over G from point to b1 and
 * b = p @ i, glue [i = 0 ↦ point] (unglue b) is b, because b at i = 0 is
 * p @ 0, which is point. And conversion must make pair eta when both sides
 * are pairs: (fst p, snd ((λ r. r) p)) annotated Σ (x : Nat). U0 and the same
 * annotated Σ (x : Nat). U1 are both p. Raw syntax, as reduction inspects
 * it and conversion compares it. */
static void normal_forms_and_conversion_keep_eta(void) {
    k = cc_kernel_new();
    assert(k);
    unsigned i = 0, j = 1;
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), point = ck_make(k, CC_POINT, 0, 0, 0, 0, 0);
    cc_term e = ck_var(k, 300), p = ck_var(k, 301), b1 = ck_var(k, 302);
    cc_term along = ck_make(k, CC_PATH, j, glue_line(unit, e, j), point, b1, 0);
    cc_term b = ck_make(k, CC_PAPP, ck_interval_variable(k, i), p, along, 0, 0);
    cc_term over_i = glue_line(unit, e, i);
    cc_term piece = ck_make(k, CC_TUBE, k->nodes[k->nodes[over_i].child[1]].payload, point, 0, 0, 0);
    cc_term glued = ck_make(k, CC_GLUE_TERM, 0, over_i, ck_make(k, CC_UNGLUE, 0, over_i, b, 0, 0), piece, 0);
    assert(k->nodes[cc_kernel_whnf(k, glued)].kind == CC_GLUE_TERM);
    assert(cc_kernel_normalize(k, glued) == b);
    assert(cc_kernel_convertible(k, glued, b, 0));

    cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term small = ck_make(k, CC_SIGMA, 400, nat, ck_universe_at(k, 0), 0, 0);
    cc_term large = ck_make(k, CC_SIGMA, 400, nat, ck_universe_at(k, 1), 0, 0);
    cc_term q = ck_var(k, 401);
    cc_term beta = ck_make(k, CC_APP, 0, ck_make(k, CC_LAM, 402, small, ck_var(k, 402), 0, 0), q, 0, 0);
    cc_term first = ck_make(k, CC_FST, 0, q, 0, 0, 0), second = ck_make(k, CC_SND, 0, beta, 0, 0, 0);
    cc_term at_small = ck_make(k, CC_PAIR, 0, small, first, second, 0);
    cc_term at_large = ck_make(k, CC_PAIR, 0, large, first, second, 0);
    assert(k->nodes[cc_kernel_whnf(k, at_small)].kind == CC_PAIR);
    assert(cc_kernel_convertible(k, at_small, at_large, 0));
    assert(!k->error[0]);

    /* The second review: conversion must also expose a base through eta
     * that holds only by conversion. With A = Glue [] Nat,
     * A' = Glue [] ((λ X. X)(Nat)), G = Glue [] A, g : G and u = unglue_G(g),
     * glue_G [] (glue_A' [] (unglue_A(u))) is g: the inner Glue term is u only
     * because A' is A by a Beta step. */
    cc_term identity = ck_make(k, CC_LAM, 403, ck_universe_at(k, 0), ck_var(k, 403), 0, 0);
    cc_term a = ck_make(k, CC_GLUE, 0, nat, 0, 0, 0);
    cc_term a_redex = ck_make(k, CC_GLUE, 0, ck_make(k, CC_APP, 0, identity, nat, 0, 0), 0, 0, 0);
    cc_term g_type = ck_make(k, CC_GLUE, 0, a, 0, 0, 0), g = ck_var(k, 404);
    cc_term u = ck_make(k, CC_UNGLUE, 0, g_type, g, 0, 0);
    cc_term inner = ck_make(k, CC_GLUE_TERM, 0, a_redex, ck_make(k, CC_UNGLUE, 0, a, u, 0, 0), 0, 0);
    cc_term outer = ck_make(k, CC_GLUE_TERM, 0, g_type, inner, 0, 0);
    assert(cc_kernel_convertible(k, outer, g, 0));
    assert(!k->error[0]);
    cc_kernel_free(k);
}

/* The review of #73: exposing a nested base must count toward the
 * comparison's depth. Syntax is at most 512 deep, but reduction reaches past
 * that: here D_i := glue_(Glue [] T_(i-1)) [] D_(i-1), with T_i := Glue [] T_(i-1), 600
 * definitions, each weak head cached as it is made. Exposing D_600's base
 * goes through every level with no other guard reached; it now stops with a
 * recorded error, where a longer chain would have overflowed the stack. */
static void nested_glue_exposure_is_depth_guarded(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term u0 = ck_universe_at(k, 0), zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term type = cc_kernel_define(k, 1000, ck_make(k, CC_NAT, 0, 0, 0, 0, 0), u0);
    cc_term value = cc_kernel_define(k, 2000, zero, type);
    assert(type && value);
    for (unsigned depth = 1; depth <= 600; ++depth) {
        cc_term glue_type = ck_make(k, CC_GLUE, 0, type, 0, 0, 0);
        type = cc_kernel_define(k, 1000 + depth, glue_type, u0);
        value = cc_kernel_define(k, 2000 + depth, ck_make(k, CC_GLUE_TERM, 0, glue_type, value, 0, 0), glue_type);
        if (!type || !value) fprintf(stderr, "depth %u: %s\n", depth, cc_kernel_error(k));
        assert(type && value && cc_kernel_whnf(k, value));
    }
    assert(!cc_kernel_convertible(k, value, zero, 0));
    assert(strstr(cc_kernel_error(k), "recursion depth"));
    cc_kernel_clear_error(k);
    cc_kernel_free(k);
}

/* The fourth review of #73: the glue move normalized the whole Glue term,
 * where Glue eta needs only its side conditions. With b = p @ i as above,
 * but p's right endpoint a Glue term over t(40), where t(n + 1) is
 * f(t(n))(t(n)): 41 nodes, 2^40 paths. The Glue step reduces the piece and
 * b at i = 0, which is point, and never reaches the endpoint p's annotation
 * carries; Normalize walks it, path by path, and runs out of budget. The
 * piece is restricted too, so glue [i = 0 ↦ b] (unglue b), which Whnf
 * leaves, is b; and a piece that is b's restriction as a weak head needs no
 * normal form, here t(40) itself, as p's left endpoint. */
static void glue_step_normalizes_only_its_side_conditions(void) {
    k = cc_kernel_new();
    assert(k);
    unsigned i = 0, j = 1;
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), point = ck_make(k, CC_POINT, 0, 0, 0, 0, 0);
    cc_term e = ck_var(k, 300), p = ck_var(k, 301), f = ck_var(k, 303), t = ck_var(k, 302);
    for (unsigned n = 0; n < 40; ++n) t = ck_make(k, CC_APP, 0, ck_make(k, CC_APP, 0, f, t, 0, 0), t, 0, 0);
    cc_term end = ck_make(k, CC_GLUE_TERM, 0, ck_make(k, CC_GLUE, 0, unit, 0, 0, 0), t, 0, 0);
    cc_term along = ck_make(k, CC_PATH, j, glue_line(unit, e, j), point, end, 0);
    cc_term b = ck_make(k, CC_PAPP, ck_interval_variable(k, i), p, along, 0, 0);
    cc_term over_i = glue_line(unit, e, i);
    cc_term piece = ck_make(k, CC_TUBE, k->nodes[k->nodes[over_i].child[1]].payload, point, 0, 0, 0);
    cc_term glued = ck_make(k, CC_GLUE_TERM, 0, over_i, ck_make(k, CC_UNGLUE, 0, over_i, b, 0, 0), piece, 0);
    cc_kernel_set_step_budget(k, 100000);
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    ck_operation(k, CC_WORK_INSTRUCTION);
    assert(ck_glue_step(k, glued) == b && !k->error[0]);
    ck_standalone(k);
    cc_kernel_work(k, &after);
    assert(after.instruction_steps - before.instruction_steps < 1000);
    assert(!cc_kernel_normalize(k, glued) && strstr(cc_kernel_error(k), "budget"));
    cc_kernel_clear_error(k);

    uint32_t at_zero = k->nodes[piece].payload;
    cc_term itself = ck_make(k, CC_GLUE_TERM, 0, over_i, ck_make(k, CC_UNGLUE, 0, over_i, b, 0, 0),
                             ck_make(k, CC_TUBE, at_zero, b, 0, 0, 0), 0);
    assert(kind(cc_kernel_whnf(k, itself)) == CC_GLUE_TERM);
    ck_operation(k, CC_WORK_INSTRUCTION);
    assert(ck_glue_step(k, itself) == b && !k->error[0]);

    cc_term from_graph = ck_make(k, CC_PAPP, ck_interval_variable(k, i), p,
                                 ck_make(k, CC_PATH, j, glue_line(unit, e, j), t, end, 0), 0, 0);
    cc_term graph_piece = ck_make(k, CC_GLUE_TERM, 0, over_i, ck_make(k, CC_UNGLUE, 0, over_i, from_graph, 0, 0),
                                  ck_make(k, CC_TUBE, at_zero, t, 0, 0, 0), 0);
    cc_kernel_work(k, &before);
    ck_operation(k, CC_WORK_INSTRUCTION);
    assert(ck_glue_step(k, graph_piece) == from_graph && !k->error[0]);
    ck_standalone(k);
    cc_kernel_work(k, &after);
    assert(after.instruction_steps - before.instruction_steps < 1000);
    cc_kernel_free(k);
}

/* The boundary is enforced, not only kept: conversion refuses to run while
 * an instruction does, so no later path can reach it unnoticed. */
static void conversion_refused_inside_an_instruction(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    ck_operation(k, CC_WORK_INSTRUCTION);
    assert(!ck_convertible(k, nat, nat));
    assert(strstr(cc_kernel_error(k), "reached the conversion search"));
    cc_kernel_clear_error(k);
    ck_operation(k, CC_WORK_QUERY);
    assert(ck_convertible(k, nat, nat));
    cc_kernel_free(k);
}

int main(void) {
    queries_leave_acceptance_unchanged();
    folded_comparison_reads_only_its_own_results();
    reduction_decides_eta_syntactically();
    normal_forms_and_conversion_keep_eta();
    nested_glue_exposure_is_depth_guarded();
    glue_step_normalizes_only_its_side_conditions();
    conversion_refused_inside_an_instruction();
    printf("instruction isolation: ok\n");
    return 0;
}
