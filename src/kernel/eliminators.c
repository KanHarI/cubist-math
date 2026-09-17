#include "internal.h"

static tt_id substitute_two_contexts(tt_engine *e, tt_id a, tt_id x, tt_id y, tt_id u, tt_id v) {
    tt_id cs[] = {x, y}, vs[] = {u, v};
    return transform(e, a, MAP_CONTEXT, cs, vs, 2, 0);
}
static tt_id bind_two_contexts(tt_engine *e, tt_id a, tt_id x, tt_id y) {
    tt_id cs[] = {x, y}, vs[] = {1, 0};
    return transform(e, a, MAP_BIND, cs, vs, 2, 0);
}

/* Premise notation matches rules.c: EXPR(i) : TYPE(i), with optional
 * discharged contexts f[]. Each family below documents its premise order.
 * q0/q1 are private symbolic test terms: simultaneous substitution compares
 * dependent types without accidentally identifying distinct context variables.
 * They are never public constructors. tt_apply owns rollback and publication. */
bool infer_eliminator(tt_engine *e, tt_opcode op, const judgement *j, const tt_id *f,
                      judgement *r) {
#define EXPR(i) (j[i].expr)
#define TYPE(i) (j[i].type)
#define KIND(a) (e->nodes[(a)].kind)
#define CHILD(a, i) (e->nodes[(a)].ch[i])
#define REQUIRE(x)                                                                                 \
    do {                                                                                           \
        if (!(x))                                                                                  \
            return false;                                                                          \
    } while (0)
    REQUIRE(universe(e, TYPE(0)));
    tt_id q0 = leaf(e, N_Temp, 0), q1 = leaf(e, N_Temp, 1);
    switch (op) {
    case TT_VoidElim: {
        /* C(z) : U, v : Void; f = [z:Void]. Conclude abort(v) : C(v). */
        tt_id void_type = 0;
        void_type = leaf(e, N_Void, 0);
        REQUIRE(context_matches(e, f[0], void_type) && TYPE(1) == void_type);
        r->expr = make1(e, N_IndVoid, EXPR(1));
        r->type = replace_ctx(e, EXPR(0), f[0], EXPR(1));
        break;
    }
    case TT_UnitElim:
    case TT_UnitComp: {
        /* C(z) : U, d : C(*), [u : Unit]; f = [z:Unit]. */
        tt_id unit_type = 0, singleton = 0, input = 0;
        unit_type = leaf(e, N_Unit, 0);
        singleton = leaf(e, N_Singleton, 0);
        REQUIRE(context_matches(e, f[0], unit_type) &&
                TYPE(1) == replace_ctx(e, EXPR(0), f[0], singleton));
        if (op == TT_UnitElim) {
            REQUIRE(TYPE(2) == unit_type);
            input = EXPR(2);
        } else
            input = singleton;
        r->expr = make2(e, N_IndUnit, EXPR(1), input);
        r->type = replace_ctx(e, EXPR(0), f[0], input);
        if (op == TT_UnitComp)
            r->expr = make2(e, N_DefEq, r->expr, EXPR(1));
        break;
    }
    case TT_SigmaElim:
    case TT_SigmaComp: {
        /* C(z) : U, d(x,y) : C((x,y)), pair (or two components).
         * f = [z:Sigma(A,B), x:A, y:B(x)]. */
        tt_id motive_type = 0, branch_type = 0, input = 0, body = 0;
        if (op == TT_SigmaElim) {
            REQUIRE(KIND(TYPE(2)) == N_Sigma);
            node st = e->nodes[TYPE(2)];
            REQUIRE(context_matches(e, f[0], TYPE(2)) && context_matches(e, f[1], st.ch[0]));
            if (f[2])
                REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) ==
                        instantiate(e, st.ch[1], q0));
            REQUIRE(!f[0] || (f[1] && f[2]));
            input = EXPR(2);
        } else {
            REQUIRE(context_matches(e, f[1], TYPE(2)));
            if (f[2]) {
                tt_id family = bind_ctx(e, e->contexts[f[2]].type, f[1], 0);
                tt_id sigma_type = make2(e, N_Sigma, TYPE(2), family);
                REQUIRE(context_matches(e, f[0], sigma_type) &&
                        TYPE(3) == instantiate(e, family, EXPR(2)));
            } else if (f[0]) {
                tt_id sigma_type = e->contexts[f[0]].type;
                REQUIRE(KIND(sigma_type) == N_Sigma &&
                        TYPE(3) == instantiate(e, CHILD(sigma_type, 1), q0));
            }
            input = make2(e, N_Tuple, EXPR(2), EXPR(3));
        }
        motive_type = replace_ctx(e, EXPR(0), f[0], make2(e, N_Tuple, q0, q1));
        branch_type = substitute_two_contexts(e, TYPE(1), f[1], f[2], q0, q1);
        REQUIRE(motive_type == branch_type);
        body = bind_two_contexts(e, EXPR(1), f[1], f[2]);
        r->expr = make2(e, N_IndSigma, body, input);
        r->type = replace_ctx(e, EXPR(0), f[0], input);
        if (op == TT_SigmaComp) {
            tt_id computed_branch =
                substitute_two_contexts(e, EXPR(1), f[1], f[2], EXPR(2), EXPR(3));
            r->expr = make2(e, N_DefEq, r->expr, computed_branch);
        }
        break;
    }
    case TT_SumElim:
    case TT_SumCompL:
    case TT_SumCompR: {
        /* C(z), left branch, right branch, input; f = [z:A+B, x:A, y:B].
         * Compare each branch type after substituting its injection into C. */
        tt_id left_type = 0, right_type = 0, motive_type = 0, branch_type = 0, input = 0;
        bool comp = op != TT_SumElim;
        bool right = op == TT_SumCompR;
        if (!comp) {
            REQUIRE(KIND(TYPE(3)) == N_Sum);
            left_type = CHILD(TYPE(3), 0);
            right_type = CHILD(TYPE(3), 1);
            REQUIRE(context_matches(e, f[0], TYPE(3)));
            input = EXPR(3);
        } else {
            /* Computation rules require the opposite branch context (or sum
             * context) to supply the otherwise unavailable summand type. */
            if (f[0]) {
                tt_id sum_type = e->contexts[f[0]].type;
                REQUIRE(KIND(sum_type) == N_Sum);
                left_type = CHILD(sum_type, 0);
                right_type = CHILD(sum_type, 1);
            } else {
                left_type = right ? (f[1] ? e->contexts[f[1]].type : 0) : TYPE(3);
                right_type = right ? TYPE(3) : (f[2] ? e->contexts[f[2]].type : 0);
            }
            REQUIRE((right ? right_type : left_type) == TYPE(3));
            input = make1(e, right ? N_Inr : N_Inl, EXPR(3));
        }
        REQUIRE(context_matches(e, f[1], left_type) && context_matches(e, f[2], right_type));
        REQUIRE(!f[0] || (f[1] && f[2]));
        motive_type = replace_ctx(e, EXPR(0), f[0], make1(e, N_Inl, q0));
        branch_type = replace_ctx(e, TYPE(1), f[1], q0);
        REQUIRE(motive_type == branch_type);
        motive_type = replace_ctx(e, EXPR(0), f[0], make1(e, N_Inr, q1));
        branch_type = replace_ctx(e, TYPE(2), f[2], q1);
        REQUIRE(motive_type == branch_type);
        tt_id left_branch = bind_ctx(e, EXPR(1), f[1], 1);
        tt_id right_branch = bind_ctx(e, EXPR(2), f[2], 0);
        r->expr = make3(e, N_IndSum, left_branch, right_branch, input);
        r->type = replace_ctx(e, EXPR(0), f[0], input);
        if (comp) {
            tt_id computed_branch = replace_ctx(e, EXPR(right ? 2 : 1), f[right ? 2 : 1], EXPR(3));
            r->expr = make2(e, N_DefEq, r->expr, computed_branch);
        }
        break;
    }
    case TT_EqElim:
    case TT_EqComp: {
        /* C(x,y,p), reflexive branch d(z), x, [y, p]; f = [x,y,p,z].
         * The branch must have type C(z,z,refl(z)); EqComp supplies refl(x). */
        tt_id motive_type = 0, branch_type = 0, input = 0, body = 0;
        bool comp = op == TT_EqComp;
        REQUIRE(context_matches(e, f[0], TYPE(2)) && context_matches(e, f[1], TYPE(2)) &&
                context_matches(e, f[3], TYPE(2)));
        if (!comp) {
            REQUIRE(TYPE(2) == TYPE(3) && KIND(TYPE(4)) == N_Eq);
            node eq = e->nodes[TYPE(4)];
            REQUIRE(eq.ch[0] == TYPE(2) && eq.ch[1] == EXPR(2) && eq.ch[2] == EXPR(3));
        }
        REQUIRE(!f[2] || (f[0] && f[1]));
        REQUIRE(!(f[0] || f[1]) || f[3]);
        if (f[2]) {
            tt_id equality_type =
                make3(e, N_Eq, TYPE(2), leaf(e, N_CRef, f[0]), leaf(e, N_CRef, f[1]));
            REQUIRE(e->contexts[f[2]].type == equality_type);
        }
        tt_id cs[] = {f[0], f[1], f[2]}, vs[] = {q0, q0, make1(e, N_Refl, q0)};
        motive_type = transform(e, EXPR(0), MAP_CONTEXT, cs, vs, 3, 0);
        branch_type = replace_ctx(e, TYPE(1), f[3], q0);
        REQUIRE(motive_type == branch_type);
        body = bind_ctx(e, EXPR(1), f[3], 0);
        input = comp ? make1(e, N_Refl, EXPR(2)) : EXPR(4);
        r->expr = make4(e, N_IndEq, body, EXPR(2), comp ? EXPR(2) : EXPR(3), input);
        vs[0] = EXPR(2);
        vs[1] = comp ? EXPR(2) : EXPR(3);
        vs[2] = input;
        r->type = transform(e, EXPR(0), MAP_CONTEXT, cs, vs, 3, 0);
        if (comp) {
            tt_id computed_branch = replace_ctx(e, EXPR(1), f[3], EXPR(2));
            r->expr = make2(e, N_DefEq, r->expr, computed_branch);
        }
        break;
    }
    case TT_NatElim:
    case TT_NatCompZ:
    case TT_NatCompS: {
        /* C(n), zero branch, successor branch, [n]; f = [n, predecessor, ih].
         * The induction hypothesis has type C(predecessor), while the branch
         * must prove C(succ(predecessor)). These are distinct checks. */
        tt_id nat_type = 0, zero = 0, input = 0, body = 0, expected = 0;
        nat_type = leaf(e, N_Nat, 0);
        zero = leaf(e, N_ZN, 0);
        REQUIRE(context_matches(e, f[0], nat_type) && context_matches(e, f[1], nat_type));
        if (op != TT_NatCompZ)
            REQUIRE(TYPE(3) == nat_type);
        REQUIRE(TYPE(1) == replace_ctx(e, EXPR(0), f[0], zero));
        expected = replace_ctx(e, EXPR(0), f[0], q0);
        if (f[2])
            REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) == expected);
        expected = replace_ctx(e, EXPR(0), f[0], make1(e, N_SN, q0));
        REQUIRE(substitute_two_contexts(e, TYPE(2), f[1], f[2], q0, q1) == expected);
        body = bind_two_contexts(e, EXPR(2), f[1], f[2]);
        input = op == TT_NatCompZ ? zero : op == TT_NatCompS ? make1(e, N_SN, EXPR(3)) : EXPR(3);
        r->expr = make3(e, N_IndNat, EXPR(1), body, input);
        r->type = replace_ctx(e, EXPR(0), f[0], input);
        if (op == TT_NatCompZ)
            r->expr = make2(e, N_DefEq, r->expr, EXPR(1));
        if (op == TT_NatCompS) {
            tt_id recursive_call = make3(e, N_IndNat, EXPR(1), body, EXPR(3));
            tt_id computed_step =
                substitute_two_contexts(e, EXPR(2), f[1], f[2], EXPR(3), recursive_call);
            r->expr = make2(e, N_DefEq, r->expr, computed_step);
        }
        break;
    }
    case TT_WElim:
    case TT_WComp: {
        /* C(z), branch d(a,f), tree (or label and child function).
         * f[] = [z:W(A,B), a:A, children:Pi b:B(a).W(A,B)]. */
        tt_id label_type = 0, arity_family = 0, arity_type = 0, recursive_motive = 0, input = 0,
              body = 0, expected = 0;
        bool comp = op == TT_WComp;
        tt_id wtype;
        if (!comp) {
            REQUIRE(KIND(TYPE(2)) == N_W);
            wtype = TYPE(2);
            input = EXPR(2);
        } else {
            REQUIRE(KIND(TYPE(3)) == N_Pi);
            wtype = CHILD(TYPE(3), 1);
            REQUIRE(KIND(wtype) == N_W && CHILD(wtype, 0) == TYPE(2));
            REQUIRE(CHILD(TYPE(3), 0) == instantiate(e, CHILD(wtype, 1), EXPR(2)));
            input = make2(e, N_WSup, EXPR(2), EXPR(3));
        }
        label_type = CHILD(wtype, 0);
        arity_family = CHILD(wtype, 1);
        REQUIRE(context_matches(e, f[0], wtype) && context_matches(e, f[1], label_type));
        REQUIRE(!f[0] || (f[1] && f[2]));
        arity_type = instantiate(e, arity_family, q0);
        if (f[2])
            REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) ==
                    make2(e, N_Pi, arity_type, wtype));
        /* z is replaced by an application containing a locally bound y. */
        recursive_motive = transform(e, EXPR(0), MAP_W_MOTIVE, &f[0], &q1, 1, 0);
        expected = make2(e, N_Pi, make2(e, N_Pi, arity_type, recursive_motive),
                         replace_ctx(e, EXPR(0), f[0], make2(e, N_WSup, q0, q1)));
        REQUIRE(substitute_two_contexts(e, TYPE(1), f[1], f[2], q0, q1) == expected);
        body = bind_two_contexts(e, EXPR(1), f[1], f[2]);
        r->expr = make2(e, N_IndW, body, input);
        r->type = replace_ctx(e, EXPR(0), f[0], input);
        if (comp) {
            tt_id specialized_branch =
                substitute_two_contexts(e, EXPR(1), f[1], f[2], EXPR(2), EXPR(3));
            tt_id shift = 1;
            tt_id shifted_f = transform(e, EXPR(3), MAP_SHIFT, NULL, &shift, 1, 0);
            tt_id shifted_body = transform(e, body, MAP_SHIFT, NULL, &shift, 1, 2);
            tt_id child = make2(e, N_Ap, shifted_f, leaf(e, N_VRef, 2));
            tt_id recursive = make1(e, N_Lambda, make2(e, N_IndW, shifted_body, child));
            r->expr = make2(e, N_DefEq, r->expr, make2(e, N_Ap, specialized_branch, recursive));
        }
        break;
    }
    default:
        return false;
    }
    return !e->error && r->expr && r->type;
#undef EXPR
#undef TYPE
#undef KIND
#undef CHILD
#undef REQUIRE
}
