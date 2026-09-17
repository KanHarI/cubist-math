#include "internal.h"
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
    unsigned coverage = 0;
    for (unsigned i = 0; i < 204; i++)
        if (tt_opcode_metadata((tt_opcode)i)) {
            if (!e->accepted_opcodes[i])
                fprintf(stderr, "UNCOVERED %s\n", tt_opcode_metadata((tt_opcode)i)->name);
            CHECK(e->accepted_opcodes[i]);
            coverage++;
        }
    printf("positive opcode coverage: %u/67\n", coverage);
    if (trace)
        CHECK(fclose(trace) == 0);
    tt_set_trace(e, NULL);
    tt_free(e);
    limits();
    puts("invalid inputs, dependency discharge, limits, rollback, deterministic cache equivalence: "
         "PASS");
    return 0;
}
