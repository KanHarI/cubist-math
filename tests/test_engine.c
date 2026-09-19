#include "kernel/internal.h"
#include <stdlib.h>

#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "%s:%d: CHECK(%s) failed\n", __FILE__, __LINE__, #x);                  \
            exit(1);                                                                               \
        }                                                                                          \
    } while (0)
static tt_id apply(tt_engine *e, tt_opcode op, tt_id a, tt_id b, tt_id c, tt_id d, tt_id g,
                   tt_id ctx, tt_id f0, tt_id f1, tt_id f2, tt_id f3) {
    tt_id js[] = {a, b, c, d, g}, fs[] = {f0, f1, f2, f3}, out = 0;
    const tt_opcode_info *m = tt_opcode_metadata(op);
    tt_status status = tt_apply(e, op, js, m->judgements, ctx, fs, m->free_contexts, &out);
    if (status != TT_OK)
        fprintf(stderr, "Failed %s, status %d\n", m->name, status);
    CHECK(status == TT_OK && out);
    return out;
}
#define A(op, a, b, c, d, g, ctx, f0, f1, f2, f3)                                                  \
    apply(e, TT_##op, a, b, c, d, g, ctx, f0, f1, f2, f3)
#define ZERO(op) A(op, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
#define ONE(op, a) A(op, a, 0, 0, 0, 0, 0, 0, 0, 0, 0)
static void check_computation(tt_engine *e, tt_id eq, tt_id expected) {
    tt_id lhs = ONE(DefEqExtL, eq), rhs = ONE(DefEqExtR, eq);
    for (unsigned i = 0; i < 4; i++)
        lhs = ONE(BetaReduceGrossKnuth, lhs);
    CHECK(e->judgements[lhs].expr == e->judgements[rhs].expr);
    CHECK(e->judgements[rhs].expr == e->judgements[expected].expr);
}
static void cover_rules(tt_engine *e) {
    tt_id u = ZERO(UIntro0), unit = ZERO(UnitForm), one = ZERO(UnitIntro), nat = ZERO(NatForm),
          zero = ZERO(NatIntroZ), void_t = ZERO(VoidForm);
    ONE(UCumul, u);
    ONE(UCumulKappa, u);
    tt_id succ = ONE(NatIntroS, zero);
    tt_id idctx = A(CtxExt, unit, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id var = A(Vble, 0, 0, 0, 0, 0, idctx, 0, 0, 0, 0);
    tt_id identity = A(PiIntro, unit, var, 0, 0, 0, 0, idctx, 0, 0, 0);
    ONE(PiUniq, identity);
    tt_id def = ONE(Def, identity), named = ONE(DefEqExtL, def);
    tt_id hi = ONE(HighExp, named);
    tt_id unfolded = ONE(DefReducePointed, hi);
    CHECK(e->judgements[unfolded].expr == e->judgements[identity].expr);
    tt_id eq = ONE(EqIntro, zero);
    ONE(High2, ONE(HighType, eq));
    tt_id elim = A(EqElim, unit, one, zero, zero, eq, 0, 0, 0, 0, 0);
    ONE(High3, ONE(HighExp, elim));
    check_computation(e, A(EqComp, unit, one, zero, 0, 0, 0, 0, 0, 0, 0), one);
    check_computation(e, A(UnitComp, unit, one, 0, 0, 0, 0, 0, 0, 0, 0), one);
    /* The Unit point branch has no bound variable: reducing it inside a
     * lambda must preserve that lambda's variable, rather than replace it
     * with the Unit point or decrement its index. */
    tt_id natctx = A(CtxExt, nat, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id natvar = A(Vble, 0, 0, 0, 0, 0, natctx, 0, 0, 0, 0);
    tt_id unit_case = A(UnitElim, nat, natvar, one, 0, 0, 0, idctx, 0, 0, 0);
    tt_id closed_case = A(PiIntro, nat, unit_case, 0, 0, 0, 0, natctx, 0, 0, 0);
    tt_id nat_identity = A(PiIntro, nat, natvar, 0, 0, 0, 0, natctx, 0, 0, 0);
    CHECK(e->judgements[ONE(BetaReduceGrossKnuth, closed_case)].expr ==
          e->judgements[nat_identity].expr);
    check_computation(e, A(SumCompL, unit, one, one, one, 0, 0, 0, 0, 0, 0), one);
    check_computation(e, A(SumCompR, unit, one, one, one, 0, 0, 0, 0, 0, 0), one);
    tt_id ni = A(NatElim, unit, one, one, succ, 0, 0, 0, 0, 0, 0);
    CHECK(e->judgements[ONE(BetaReduceGrossKnuth, ni)].expr == e->judgements[one].expr);
    check_computation(e, A(NatCompZ, unit, one, one, 0, 0, 0, 0, 0, 0, 0), one);
    check_computation(e, A(NatCompS, unit, one, one, zero, 0, 0, 0, 0, 0, 0), one);
    tt_id wt = A(WForm, unit, void_t, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id vc = A(CtxExt, void_t, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          vv = A(Vble, 0, 0, 0, 0, 0, vc, 0, 0, 0, 0);
    tt_id absurd = A(VoidElim, wt, vv, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id arity = A(PiIntro, void_t, absurd, 0, 0, 0, 0, vc, 0, 0, 0);
    tt_id tree = A(WIntro, one, void_t, arity, 0, 0, 0, 0, 0, 0, 0);
    tt_id recursive_type = A(PiForm, void_t, unit, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id branch = A(PiIntro, recursive_type, one, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id wi = A(WElim, unit, branch, tree, 0, 0, 0, 0, 0, 0, 0);
    tt_id wr = ONE(BetaReduceGrossKnuth, ONE(BetaReduceGrossKnuth, wi));
    CHECK(e->judgements[wr].expr == e->judgements[one].expr);
    tt_id wc = A(WComp, unit, branch, one, arity, 0, 0, 0, 0, 0, 0);
    tt_id wl = ONE(DefEqExtL, wc), rr = ONE(DefEqExtR, wc);
    for (unsigned i = 0; i < 4; i++) {
        wl = ONE(BetaReduceGrossKnuth, wl);
        rr = ONE(BetaReduceGrossKnuth, rr);
    }
    CHECK(e->judgements[wl].expr == e->judgements[rr].expr);
    CHECK(!tt_verify(e, unit, zero));
    CHECK(tt_verify(e, nat, succ));
}
static void invalid_inputs(tt_engine *e) {
    tt_id u = ZERO(UIntro0), unit = ZERO(UnitForm), one = ZERO(UnitIntro), zero = ZERO(NatIntroZ),
          out = 99;
    CHECK(tt_apply(NULL, TT_UnitIntro, NULL, 0, 0, NULL, 0, &out) == TT_INVALID && out == 0);
    CHECK(tt_apply(e, (tt_opcode)999, NULL, 0, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_PiElim, NULL, 2, 0, NULL, 0, &out) == TT_INVALID);
    tt_id bad[] = {UINT32_MAX, 0};
    CHECK(tt_apply(e, TT_PiElim, bad, 2, 0, NULL, 0, &out) == TT_INVALID);
    tt_id pair[] = {one, zero};
    CHECK(tt_apply(e, TT_PiElim, pair, 2, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_High3, &one, 1, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_Axiom, &one, 1, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_Vble, NULL, 0, UINT32_MAX, NULL, 0, &out) == TT_INVALID);
    tt_id fc[] = {UINT32_MAX};
    CHECK(tt_apply(e, TT_CtxExt, &u, 1, 0, fc, 1, &out) == TT_INVALID);
    /* A cannot be discharged while an undischarged x:A still depends on it. */
    tt_id ac = A(CtxExt, u, 0, 0, 0, 0, 0, 0, 0, 0, 0), av = A(Vble, 0, 0, 0, 0, 0, ac, 0, 0, 0, 0);
    tt_id xc = A(CtxExt, av, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          xv = A(Vble, 0, 0, 0, 0, 0, xc, 0, 0, 0, 0);
    tt_id js[] = {u, xv};
    CHECK(tt_apply(e, TT_PiIntro, js, 2, 0, &ac, 1, &out) == TT_INVALID);
    CHECK(!tt_verify(e, unit, xv));
    CHECK(!tt_verify(e, UINT32_MAX, one));
    /* Failed legality checks must not retain their temporary AST allocations. */
    uint32_t before = e->nn;
    tt_id args[] = {unit, zero, one};
    for (unsigned i = 0; i < 1000; i++)
        CHECK(tt_apply(e, TT_EqForm, args, 3, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(e->nn == before);
}
static void limits(void) {
    tt_config cfg = tt_default_config();
    cfg.max_expression_nodes = 2;
    cfg.max_counter = 0;
    tt_engine *e = tt_new(&cfg);
    CHECK(e);
    tt_id unit = ZERO(UnitForm), one = ZERO(UnitIntro), out = 0;
    CHECK(tt_apply(e, TT_EqIntro, &one, 1, 0, NULL, 0, &out) == TT_LIMIT && out == 0);
    tt_id ctx = A(CtxExt, unit, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    CHECK(tt_apply(e, TT_CtxExt, &unit, 1, 0, &ctx, 1, &out) == TT_LIMIT);
    CHECK(tt_apply(e, TT_Axiom, &unit, 1, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_DefEqRefl, &one, 1, 0, NULL, 0, &out) == TT_LIMIT);
    tt_free(e);
    cfg = tt_default_config();
    cfg.max_judgements = 1;
    e = tt_new(&cfg);
    CHECK(e);
    ZERO(UnitIntro);
    CHECK(tt_apply(e, TT_NatIntroZ, NULL, 0, 0, NULL, 0, &out) == TT_LIMIT);
    tt_free(e);
    cfg = tt_default_config();
    cfg.max_ast_nodes = 2;
    e = tt_new(&cfg);
    CHECK(e);
    ZERO(UnitIntro);
    CHECK(tt_apply(e, TT_UIntro0, NULL, 0, 0, NULL, 0, &out) == TT_LIMIT);
    CHECK(e->nn == 2);
    tt_free(e);
}
static void storage_growth(void) {
    tt_config cfg = tt_default_config();
    cfg.max_counter = 8192;
    CHECK(cfg.max_ast_nodes == 0 && cfg.max_judgements == 0);
    tt_engine *e = tt_new(&cfg);
    CHECK(e);
    tt_id unit = ZERO(UnitForm), one = ZERO(UnitIntro), previous = 0, first = 0;
    for (unsigned i = 0; i < 4096; i++) {
        tt_id ctx = A(CtxExt, unit, 0, 0, 0, 0, 0, previous, 0, 0, 0);
        tt_id value = A(Vble, 0, 0, 0, 0, 0, ctx, 0, 0, 0, 0);
        if (!first)
            first = value;
        CHECK(value != first || i == 0);
        previous = ctx;
    }
    /* Surpass the initial pools and preserve old checked handles after growth. */
    tt_stats stats;
    tt_get_stats(e, &stats);
    CHECK(stats.judgements > 4096 && stats.ast_nodes > 4096);
    CHECK(tt_verify(e, unit, one));
    tt_judgement_view view;
    CHECK(tt_judgement(e, first, &view));
    CHECK(view.type == e->judgements[unit].expr);
    tt_free(e);
}
/* Dependent Nat induction must advance the motive in the successor case.
 * Run outside the frozen upstream trace, whose old rule has this defect. */
static void dependent_nat(void) {
    tt_engine *e = tt_new(NULL);
    CHECK(e);
    tt_id nat = ZERO(NatForm), zero = ZERO(NatIntroZ), one = ONE(NatIntroS, zero);
    tt_id zc = A(CtxExt, nat, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id z = A(Vble, 0, 0, 0, 0, 0, zc, 0, 0, 0, 0);
    tt_id nc = A(CtxExt, nat, 0, 0, 0, 0, 0, zc, 0, 0, 0);
    tt_id n = A(Vble, 0, 0, 0, 0, 0, nc, 0, 0, 0, 0);
    tt_id motive = A(EqForm, nat, z, z, 0, 0, 0, 0, 0, 0, 0);
    tt_id base = ONE(EqIntro, zero), correct = ONE(EqIntro, ONE(NatIntroS, n));
    tt_id wrong = ONE(EqIntro, n), fs[] = {zc, nc, 0}, out = 0;
    tt_id ih_type = A(EqForm, nat, n, n, 0, 0, 0, 0, 0, 0, 0);
    tt_id ih = A(CtxExt, ih_type, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id sn = ONE(NatIntroS, n);
    tt_id bad_ih_type = A(EqForm, nat, sn, sn, 0, 0, 0, 0, 0, 0, 0);
    tt_id bad_ih = A(CtxExt, bad_ih_type, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_opcode ops[] = {TT_NatElim, TT_NatCompZ, TT_NatCompS};
    for (unsigned i = 0; i < 3; i++) {
        const tt_opcode_info *m = tt_opcode_metadata(ops[i]);
        tt_id js[] = {motive, base, wrong, one};
        CHECK(tt_apply(e, ops[i], js, m->judgements, 0, fs, 3, &out) == TT_INVALID);
        js[2] = correct;
        CHECK(tt_apply(e, ops[i], js, m->judgements, 0, fs, 3, &out) == TT_OK);
        fs[2] = bad_ih;
        CHECK(tt_apply(e, ops[i], js, m->judgements, 0, fs, 3, &out) == TT_INVALID);
        fs[2] = ih;
        CHECK(tt_apply(e, ops[i], js, m->judgements, 0, fs, 3, &out) == TT_OK);
        fs[2] = 0;
    }
    tt_id result = A(NatElim, motive, base, correct, one, 0, 0, zc, nc, 0, 0);
    tt_id expected = ONE(EqIntro, one);
    for (unsigned i = 0; i < 4; i++)
        result = ONE(BetaReduceGrossKnuth, result);
    CHECK(e->judgements[result].expr == e->judgements[expected].expr);
    CHECK(e->judgements[result].type == e->judgements[expected].type);
    tt_free(e);
}
/* Normalize both sides independently; beta must commute with closing an
 * external context. Closed numeral tests alone miss escaping de Bruijn indices. */
static void same_normal_form(tt_engine *e, tt_id a, tt_id b) {
    for (unsigned i = 0; i < 12; i++) {
        a = ONE(BetaReduceGrossKnuth, a);
        b = ONE(BetaReduceGrossKnuth, b);
    }
    CHECK(e->judgements[a].expr == e->judgements[b].expr);
    CHECK(e->judgements[a].type == e->judgements[b].type);
}
static void recursive_binding(void) {
    tt_engine *e = tt_new(NULL);
    CHECK(e);
    tt_id nat = ZERO(NatForm), zero = ZERO(NatIntroZ);
    tt_id nc = A(CtxExt, nat, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id n = A(Vble, 0, 0, 0, 0, 0, nc, 0, 0, 0, 0);
    tt_id ic = A(CtxExt, nat, 0, 0, 0, 0, 0, nc, 0, 0, 0);
    tt_id ih = A(Vble, 0, 0, 0, 0, 0, ic, 0, 0, 0, 0);
    tt_id step = ONE(NatIntroS, ih), sn = ONE(NatIntroS, n);
    tt_id recursive = A(NatElim, nat, zero, step, sn, 0, 0, 0, 0, ic, 0);
    tt_id reduced = ONE(BetaReduceGrossKnuth, recursive);
    same_normal_form(e, A(PiIntro, nat, recursive, 0, 0, 0, 0, nc, 0, 0, 0),
                     A(PiIntro, nat, reduced, 0, 0, 0, 0, nc, 0, 0, 0));
    tt_id at_zero = A(NatElim, nat, n, ih, zero, 0, 0, 0, 0, ic, 0);
    same_normal_form(e, A(PiIntro, nat, at_zero, 0, 0, 0, 0, nc, 0, 0, 0),
                     A(PiIntro, nat, n, 0, 0, 0, 0, nc, 0, 0, 0));

    tt_id unit = ZERO(UnitForm), star = ZERO(UnitIntro);
    tt_id w = A(WForm, unit, unit, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id child_type = A(PiForm, unit, w, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id cc = A(CtxExt, child_type, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id children = A(Vble, 0, 0, 0, 0, 0, cc, 0, 0, 0, 0);
    tt_id rec_type = A(PiForm, unit, nat, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id rc = A(CtxExt, rec_type, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id rec = A(Vble, 0, 0, 0, 0, 0, rc, 0, 0, 0, 0);
    tt_id branch_body = ONE(NatIntroS, A(PiElim, rec, star, 0, 0, 0, 0, 0, 0, 0, 0));
    tt_id branch = A(PiIntro, rec_type, branch_body, 0, 0, 0, 0, rc, 0, 0, 0);
    tt_id tree = A(WIntro, star, unit, children, 0, 0, 0, 0, 0, 0, 0);
    tt_id folded = A(WElim, nat, branch, tree, 0, 0, 0, 0, 0, 0, 0);
    tt_id child = A(PiElim, children, star, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id expected = ONE(NatIntroS, A(WElim, nat, branch, child, 0, 0, 0, 0, 0, 0, 0));
    tt_id closed_fold = A(PiIntro, child_type, folded, 0, 0, 0, 0, cc, 0, 0, 0);
    same_normal_form(e, closed_fold, A(PiIntro, child_type, expected, 0, 0, 0, 0, cc, 0, 0, 0));
    tt_id comp = A(WComp, nat, branch, star, children, 0, 0, 0, 0, 0, 0);
    same_normal_form(e, closed_fold,
                     A(PiIntro, child_type, ONE(DefEqExtR, comp), 0, 0, 0, 0, cc, 0, 0, 0));
    tt_free(e);
}
/* Native suspension rules are tested after the frozen upstream trace. Closed
 * test postulates supply arbitrary fibers and sections; wrong boundaries must
 * still be rejected, regardless of whether those postulates are inhabited. */
static void cover_suspension(tt_engine *e) {
    tt_id unit = ZERO(UnitForm), star = ZERO(UnitIntro), u = ZERO(UIntro0);
    tt_id S = ONE(SuspForm, unit), n = ONE(SuspNorth, unit), s = ONE(SuspSouth, unit);
    tt_id meridian = A(SuspMerid, unit, star, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id family_type = A(PiForm, S, u, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id family = ONE(Axiom, family_type);
    tt_id Cn = A(PiElim, family, n, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id Cs = A(PiElim, family, s, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id cn = ONE(Axiom, Cn), cs = ONE(Axiom, Cs);
    tt_id ctx = ONE(CtxExt, unit), a = A(Vble, 0, 0, 0, 0, 0, ctx, 0, 0, 0, 0);
    tt_id path = A(SuspMerid, unit, a, 0, 0, 0, 0, 0, 0, 0, 0);
    tt_id moved = A(Transport, family, n, s, path, cn, 0, 0, 0, 0, 0);
    tt_id equality = A(EqForm, Cs, moved, cs, 0, 0, 0, 0, 0, 0, 0);
    tt_id H = A(PiForm, unit, equality, 0, 0, 0, 0, ctx, 0, 0, 0);
    tt_id h = ONE(Axiom, H);
    tt_id at_n = A(SuspElim, family, cn, cs, h, n, 0, 0, 0, 0, 0);
    tt_id at_s = A(SuspElim, family, cn, cs, h, s, 0, 0, 0, 0, 0);
    tt_id rn = ONE(BetaReduceGrossKnuth, at_n), rs = ONE(BetaReduceGrossKnuth, at_s);
    CHECK(e->judgements[rn].expr == e->judgements[cn].expr);
    CHECK(e->judgements[rs].expr == e->judgements[cs].expr);
    tt_id xctx = ONE(CtxExt, S), x = A(Vble, 0, 0, 0, 0, 0, xctx, 0, 0, 0, 0);
    tt_id body = A(SuspElim, family, cn, cs, h, x, 0, 0, 0, 0, 0);
    tt_id section = A(PiIntro, S, body, 0, 0, 0, 0, xctx, 0, 0, 0);
    A(Apd, section, n, s, meridian, 0, 0, 0, 0, 0, 0);
    A(SuspMeridComp, family, cn, cs, h, star, 0, 0, 0, 0, 0);
    tt_id out = 0, bad[] = {family, cs, cn, h, n};
    CHECK(tt_apply(e, TT_SuspElim, bad, 5, 0, NULL, 0, &out) == TT_INVALID && out == 0);
    tt_id wrong_boundary[] = {family, n, n, meridian, cn};
    CHECK(tt_apply(e, TT_Transport, wrong_boundary, 5, 0, NULL, 0, &out) == TT_INVALID);
    tt_id wrong_coherence[] = {family, cn, cs, section, n};
    CHECK(tt_apply(e, TT_SuspElim, wrong_coherence, 5, 0, NULL, 0, &out) == TT_INVALID);
    tt_id wrong_parameter[] = {unit, ZERO(NatIntroZ)};
    CHECK(tt_apply(e, TT_SuspMerid, wrong_parameter, 2, 0, NULL, 0, &out) == TT_INVALID);
}

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    tt_config c = tt_default_config();
    c.allow_axioms = true;
    c.max_expression_nodes = 0;
    tt_engine *e = tt_new(&c);
    CHECK(e);
    FILE *trace = NULL;
    const char *path = getenv("TT_TRACE_FILE");
    if (path) {
        trace = fopen(path, "w");
        CHECK(trace);
        tt_set_trace(e, trace);
    }
    CHECK(tt_run_proof_suite(e, stdout));
    cover_rules(e);
    invalid_inputs(e);
    if (trace)
        CHECK(fclose(trace) == 0);
    tt_set_trace(e, NULL);
    cover_suspension(e);
    unsigned coverage = 0;
    for (unsigned i = 0; i < 204; i++)
        if (tt_opcode_metadata((tt_opcode)i)) {
            if (!e->accepted_opcodes[i])
                fprintf(stderr, "UNCOVERED %s\n", tt_opcode_metadata((tt_opcode)i)->name);
            CHECK(e->accepted_opcodes[i]);
            coverage++;
        }
    printf("positive opcode coverage: %u/75\n", coverage);
    tt_free(e);
    dependent_nat();
    recursive_binding();
    limits();
    storage_growth();
    puts("invalid inputs, dependency discharge, limits, rollback, deterministic cache equivalence: "
         "PASS");
    return 0;
}
