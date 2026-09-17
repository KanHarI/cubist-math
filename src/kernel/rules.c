#include "internal.h"

/* Each case checks premises before constructing the conclusion. EXPR(i) and
 * TYPE(i) are the expression and type of premise i (zero-based); f[] contains
 * optional contexts to discharge, in metadata order. REQUIRE is a failed rule,
 * not an assertion: tt_apply rejects it and rolls back tentative allocations.
 * Interned-ID equality here is exact structural equality, not hash equality.
 * No rule in this file may call save_judgement or save_context. */
bool infer_rule(tt_engine *e, tt_opcode op, const tt_id *ids, const judgement *j, tt_id ctx,
                const tt_id *f, judgement *r) {
#define EXPR(i) (j[i].expr)
#define TYPE(i) (j[i].type)
#define KIND(id) (e->nodes[(id)].kind)
#define CHILD(id, i) (e->nodes[(id)].ch[i])
#define REQUIRE(x)                                                                                 \
    do {                                                                                           \
        if (!(x))                                                                                  \
            return false;                                                                          \
    } while (0)
    node first_term = e->nodes[EXPR(0)], first_type = e->nodes[TYPE(0)];
    switch (op) {
    /* Universe formation and cumulativity. */
    case TT_UIntro0:
        r->expr = leaf(e, N_U, 0);
        r->type = leaf(e, N_U, 1);
        break;
    case TT_UIntroOmega:
        r->expr = leaf(e, N_UUOmega, 0);
        r->type = leaf(e, N_UUKappa, 0);
        break;
    case TT_UIntro:
        REQUIRE(first_term.kind == N_U && first_type.kind == N_U &&
                first_term.param < INT32_MAX - 2);
        r->expr = leaf(e, N_U, first_term.param + 1);
        r->type = leaf(e, N_U, first_term.param + 2);
        break;
    case TT_UCumul:
        REQUIRE(first_type.kind == N_U && first_type.param < INT32_MAX - 1);
        r->expr = EXPR(0);
        r->type = leaf(e, N_U, first_type.param + 1);
        break;
    case TT_UCumulOmega:
        REQUIRE(first_type.kind == N_U || first_type.kind == N_UCRef);
        r->expr = EXPR(0);
        r->type = leaf(e, N_UUOmega, 0);
        break;
    case TT_UCumulKappa:
        REQUIRE(universe(e, TYPE(0)) && first_type.kind != N_UUKappa && first_term.kind == N_U);
        r->expr = EXPR(0);
        r->type = leaf(e, N_UUKappa, 0);
        break;
    case TT_UCumulContext:
        REQUIRE(universe(e, TYPE(0)) && TYPE(0) == EXPR(1) && universe(e, TYPE(1)));
        r->expr = EXPR(0);
        r->type = TYPE(1);
        break;
    case TT_UCumul0:
        REQUIRE(first_type.kind == N_U && first_type.param == 0 && universe(e, EXPR(1)) &&
                universe(e, TYPE(1)));
        r->expr = EXPR(0);
        r->type = EXPR(1);
        break;
    /* Variables are introduced only from a validated context handle. */
    case TT_Vble:
        r->expr = leaf(e, N_CRef, ctx);
        r->type = e->contexts[ctx].type;
        break;
    case TT_UVble: {
        tt_id context_type = 0;
        context_type = e->contexts[ctx].type;
        REQUIRE(KIND(context_type) == N_UUOmega || KIND(context_type) == N_UUKappa ||
                KIND(context_type) == N_UCRef);
        r->expr = leaf(e, N_UCRef, ctx);
        r->type = context_type;
        break;
    }
    /* Explicit trust boundary: axioms require opt-in and a closed type. */
    case TT_Axiom:
        REQUIRE(e->conf.allow_axioms && universe(e, TYPE(0)) && !j[0].set);
        r->expr = leaf(e, N_Axiom, ids[0]);
        r->type = EXPR(0);
        break;
    /* Definitional equalities retain their common type; definitions are closed. */
    case TT_Def:
        REQUIRE(!j[0].set);
        r->expr = make2(e, N_DefEq, leaf(e, N_DRef, ids[0]), EXPR(0));
        r->type = TYPE(0);
        break;
    case TT_DefEqRefl:
        r->expr = make2(e, N_DefEq, EXPR(0), EXPR(0));
        r->type = TYPE(0);
        break;
    case TT_DefEqSwp:
        REQUIRE(first_term.kind == N_DefEq);
        r->expr = make2(e, N_DefEq, first_term.ch[1], first_term.ch[0]);
        r->type = TYPE(0);
        break;
    case TT_DefEqExtL:
    case TT_DefEqExtR:
        REQUIRE(first_term.kind == N_DefEq);
        r->expr = first_term.ch[op == TT_DefEqExtR];
        r->type = TYPE(0);
        break;
    case TT_DefLookup: {
        tt_id definition_ref = 0, definition_id = 0;
        REQUIRE(j[0].highlight);
        definition_ref = pointed(e, j[0].highlight == 1 ? EXPR(0) : TYPE(0), j[0].path);
        REQUIRE(definition_ref && KIND(definition_ref) == N_DRef);
        definition_id = e->nodes[definition_ref].param;
        REQUIRE(definition_id && definition_id <= e->nj);
        r->expr = make2(e, N_DefEq, definition_ref, e->judgements[definition_id].expr);
        r->type = e->judgements[definition_id].type;
        break;
    }
    /* A : U, B : V under x:A => (Pi/Sigma/W x:A.B) : max(U,V). */
    case TT_PiForm:
    case TT_SigmaForm:
    case TT_WForm: {
        tt_id bound_family = 0;
        REQUIRE(universe(e, TYPE(0)) && universe(e, TYPE(1)) && context_matches(e, f[0], EXPR(0)));
        bound_family = bind_ctx(e, EXPR(1), f[0], 0);
        r->expr = make2(e,
                        op == TT_PiForm      ? N_Pi
                        : op == TT_SigmaForm ? N_Sigma
                                             : N_W,
                        EXPR(0), bound_family);
        r->type = max_universe(e, TYPE(0), TYPE(1));
        break;
    }
    /* Abstract x in both the body and its dependent result type. */
    case TT_PiIntro: {
        tt_id bound_body = 0, bound_type = 0;
        REQUIRE(universe(e, TYPE(0)) && context_matches(e, f[0], EXPR(0)));
        bound_body = bind_ctx(e, EXPR(1), f[0], 0);
        bound_type = bind_ctx(e, TYPE(1), f[0], 0);
        r->expr = make1(e, N_Lambda, bound_body);
        r->type = make2(e, N_Pi, EXPR(0), bound_type);
        break;
    }
    /* f : Pi x:A.B, a : A => f(a) : B[a/x]. */
    case TT_PiElim:
        REQUIRE(first_type.kind == N_Pi && first_type.ch[0] == TYPE(1));
        r->expr = make2(e, N_Ap, EXPR(0), EXPR(1));
        r->type = instantiate(e, first_type.ch[1], EXPR(1));
        break;
    case TT_PiComp: {
        tt_id lambda = 0, application = 0, substituted_body = 0;
        REQUIRE(context_matches(e, f[0], TYPE(1)));
        lambda = make1(e, N_Lambda, bind_ctx(e, EXPR(0), f[0], 0));
        application = make2(e, N_Ap, lambda, EXPR(1));
        substituted_body = replace_ctx(e, EXPR(0), f[0], EXPR(1));
        r->expr = make2(e, N_DefEq, application, substituted_body);
        r->type = replace_ctx(e, TYPE(0), f[0], EXPR(1));
        break;
    }
    case TT_PiUniq: {
        tt_id eta_body = 0;
        REQUIRE(first_type.kind == N_Pi);
        eta_body = make2(e, N_Ap, EXPR(0), leaf(e, N_VRef, 0));
        r->expr = make2(e, N_DefEq, EXPR(0), make1(e, N_Lambda, eta_body));
        r->type = TYPE(0);
        break;
    }
    /* Sigma checks the second component; W checks the child function. */
    case TT_SigmaIntro:
    case TT_WIntro: {
        tt_id bound_family = 0, component_type = 0;
        REQUIRE(universe(e, TYPE(1)) && context_matches(e, f[0], TYPE(0)));
        bound_family = bind_ctx(e, EXPR(1), f[0], 0);
        component_type = replace_ctx(e, EXPR(1), f[0], EXPR(0));
        r->type = make2(e, op == TT_SigmaIntro ? N_Sigma : N_W, TYPE(0), bound_family);
        REQUIRE(TYPE(2) ==
                (op == TT_SigmaIntro ? component_type : make2(e, N_Pi, component_type, r->type)));
        r->expr = make2(e, op == TT_SigmaIntro ? N_Tuple : N_WSup, EXPR(0), EXPR(2));
        break;
    }
    case TT_SumForm:
    case TT_SumIntroL:
    case TT_SumIntroR: {
        tt_id sum_type = 0;
        REQUIRE(universe(e, TYPE(0)) && universe(e, TYPE(1)));
        sum_type = make2(e, N_Sum, EXPR(0), EXPR(1));
        if (op == TT_SumForm) {
            r->expr = sum_type;
            r->type = max_universe(e, TYPE(0), TYPE(1));
        } else {
            REQUIRE(TYPE(2) == EXPR(op == TT_SumIntroR));
            r->expr = make1(e, op == TT_SumIntroL ? N_Inl : N_Inr, EXPR(2));
            r->type = sum_type;
        }
        break;
    }
    case TT_VoidForm:
        r->expr = leaf(e, N_Void, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_UnitForm:
        r->expr = leaf(e, N_Unit, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_UnitIntro:
        r->expr = leaf(e, N_Singleton, 0);
        r->type = leaf(e, N_Unit, 0);
        break;
    case TT_NatForm:
        r->expr = leaf(e, N_Nat, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_NatIntroZ:
        r->expr = leaf(e, N_ZN, 0);
        r->type = leaf(e, N_Nat, 0);
        break;
    case TT_NatIntroS:
        REQUIRE(first_type.kind == N_Nat);
        r->expr = make1(e, N_SN, EXPR(0));
        r->type = TYPE(0);
        break;
    case TT_EqForm:
        REQUIRE(universe(e, TYPE(0)) && TYPE(1) == EXPR(0) && TYPE(2) == EXPR(0));
        r->expr = make3(e, N_Eq, EXPR(0), EXPR(1), EXPR(2));
        r->type = TYPE(0);
        break;
    case TT_EqIntro:
        r->expr = make1(e, N_Refl, EXPR(0));
        r->type = make3(e, N_Eq, TYPE(0), EXPR(0), EXPR(0));
        break;
    /* Rewrite by an explicit DefEq judgement; there is no implicit conversion
     * search during ordinary premise matching. */
    case TT_Subs:
    case TT_HighSubs: {
        tt_id rewrite_from = 0, rewrite_to = 0;
        REQUIRE(KIND(EXPR(1)) == N_DefEq);
        rewrite_from = CHILD(EXPR(1), 0);
        rewrite_to = CHILD(EXPR(1), 1);
        r->expr = EXPR(0);
        r->type = TYPE(0);
        if (op == TT_HighSubs) {
            REQUIRE(j[0].highlight);
            r->highlight = j[0].highlight;
            r->path = j[0].path;
            tt_id *root = r->highlight == 1 ? &r->expr : &r->type;
            tt_id selected_term = pointed(e, *root, r->path);
            REQUIRE(selected_term);
            selected_term =
                transform(e, selected_term, MAP_REPLACE, &rewrite_from, &rewrite_to, 1, 0);
            *root = at_path(e, *root, r->path, selected_term);
        } else {
            r->expr = transform(e, EXPR(0), MAP_REPLACE, &rewrite_from, &rewrite_to, 1, 0);
            r->type = transform(e, TYPE(0), MAP_REPLACE, &rewrite_from, &rewrite_to, 1, 0);
        }
        break;
    }
    /* Highlights are checked paths into an expression or type. */
    case TT_HighExp:
    case TT_HighType:
        r->expr = EXPR(0);
        r->type = TYPE(0);
        r->highlight = op == TT_HighExp ? 1 : 2;
        break;
    case TT_UnHigh:
        REQUIRE(j[0].highlight);
        r->expr = EXPR(0);
        r->type = TYPE(0);
        break;
    case TT_HighUp:
        REQUIRE(j[0].highlight && j[0].path);
        r->expr = EXPR(0);
        r->type = TYPE(0);
        r->highlight = j[0].highlight;
        r->path = path_pop(e, j[0].path);
        break;
    case TT_High0:
    case TT_High1:
    case TT_High2:
    case TT_High3: {
        tt_id selected_term = 0;
        REQUIRE(j[0].highlight);
        selected_term = pointed(e, j[0].highlight == 1 ? EXPR(0) : TYPE(0), j[0].path);
        REQUIRE(selected_term && (unsigned)(op - TT_High0) < e->nodes[selected_term].arity);
        r->expr = EXPR(0);
        r->type = TYPE(0);
        r->highlight = j[0].highlight;
        r->path = path_append(e, j[0].path, op - TT_High0);
        break;
    }
    case TT_BetaReduceGrossKnuth:
    case TT_BetaReducePointed:
    case TT_DefBetaReduceGrossKnuth:
    case TT_DefReducePointed: {
        bool defs = op == TT_DefBetaReduceGrossKnuth || op == TT_DefReducePointed;
        bool rec = op == TT_BetaReduceGrossKnuth || op == TT_DefBetaReduceGrossKnuth;
        REQUIRE(rec || j[0].highlight);
        r->expr = EXPR(0);
        r->type = TYPE(0);
        r->highlight = j[0].highlight;
        r->path = j[0].path;
        if (r->highlight) {
            tt_id *root = r->highlight == 1 ? &r->expr : &r->type;
            tt_id selected_term = pointed(e, *root, r->path);
            REQUIRE(selected_term && (rec || reducible(e, selected_term, defs)));
            selected_term = reduce(e, selected_term, defs, rec);
            *root = at_path(e, *root, r->path, selected_term);
        } else {
            r->expr = reduce(e, EXPR(0), defs, true);
            r->type = reduce(e, TYPE(0), defs, true);
        }
        break;
    }
    default:
        return infer_eliminator(e, op, j, f, r);
    }
    return !e->error && r->expr && r->type;
#undef EXPR
#undef TYPE
#undef KIND
#undef CHILD
#undef REQUIRE
}
