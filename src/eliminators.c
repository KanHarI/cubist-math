#include "internal.h"

static bool matches(tt_engine *e, tt_id c, tt_id t) {
    return !c || e->contexts[c].type == t;
}
static tt_id sub2(tt_engine *e, tt_id a, tt_id x, tt_id y, tt_id u, tt_id v) {
    tt_id cs[] = {x, y}, vs[] = {u, v};
    return transform(e, a, MAP_CONTEXT, cs, vs, 2, 0);
}
static tt_id bind2(tt_engine *e, tt_id a, tt_id x, tt_id y) {
    tt_id cs[] = {x, y}, vs[] = {1, 0};
    return transform(e, a, MAP_BIND, cs, vs, 2, 0);
}

bool infer_eliminator(tt_engine *e, tt_opcode op, const judgement *j, const tt_id *f,
                      judgement *r) {
#define E(i) (j[i].expr)
#define T(i) (j[i].type)
#define K(a) (e->nodes[(a)].kind)
#define CH(a, i) (e->nodes[(a)].ch[i])
#define REQUIRE(x)                                                                                 \
    do {                                                                                           \
        if (!(x))                                                                                  \
            return false;                                                                          \
    } while (0)
    REQUIRE(universe(e, T(0)));
    tt_id q0 = leaf(e, N_Temp, 0), q1 = leaf(e, N_Temp, 1);
    tt_id a = 0, b = 0, c = 0, d = 0, input = 0, body = 0, expected = 0;
    switch (op) {
    case TT_VoidElim:
        a = leaf(e, N_Void, 0);
        REQUIRE(matches(e, f[0], a) && T(1) == a);
        r->expr = make1(e, N_IndVoid, E(1));
        r->type = replace_ctx(e, E(0), f[0], E(1));
        break;
    case TT_UnitElim:
    case TT_UnitComp:
        a = leaf(e, N_Unit, 0);
        b = leaf(e, N_Singleton, 0);
        REQUIRE(matches(e, f[0], a) && T(1) == replace_ctx(e, E(0), f[0], b));
        if (op == TT_UnitElim) {
            REQUIRE(T(2) == a);
            input = E(2);
        } else
            input = b;
        r->expr = make2(e, N_IndUnit, E(1), input);
        r->type = replace_ctx(e, E(0), f[0], input);
        if (op == TT_UnitComp)
            r->expr = make2(e, N_DefEq, r->expr, E(1));
        break;
    case TT_SigmaElim:
    case TT_SigmaComp: {
        if (op == TT_SigmaElim) {
            REQUIRE(K(T(2)) == N_Sigma);
            node st = e->nodes[T(2)];
            REQUIRE(matches(e, f[0], T(2)) && matches(e, f[1], st.ch[0]));
            if (f[2])
                REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) ==
                        instantiate(e, st.ch[1], q0));
            REQUIRE(!f[0] || (f[1] && f[2]));
            input = E(2);
        } else {
            REQUIRE(matches(e, f[1], T(2)));
            if (f[2]) {
                a = bind_ctx(e, e->contexts[f[2]].type, f[1], 0);
                b = make2(e, N_Sigma, T(2), a);
                REQUIRE(matches(e, f[0], b) && T(3) == instantiate(e, a, E(2)));
            } else if (f[0]) {
                a = e->contexts[f[0]].type;
                REQUIRE(K(a) == N_Sigma && T(3) == instantiate(e, CH(a, 1), q0));
            }
            input = make2(e, N_Tuple, E(2), E(3));
        }
        a = replace_ctx(e, E(0), f[0], make2(e, N_Tuple, q0, q1));
        b = sub2(e, T(1), f[1], f[2], q0, q1);
        REQUIRE(a == b);
        body = bind2(e, E(1), f[1], f[2]);
        r->expr = make2(e, N_IndSigma, body, input);
        r->type = replace_ctx(e, E(0), f[0], input);
        if (op == TT_SigmaComp) {
            c = sub2(e, E(1), f[1], f[2], E(2), E(3));
            r->expr = make2(e, N_DefEq, r->expr, c);
        }
        break;
    }
    case TT_SumElim:
    case TT_SumCompL:
    case TT_SumCompR: {
        bool comp = op != TT_SumElim;
        bool right = op == TT_SumCompR;
        if (!comp) {
            REQUIRE(K(T(3)) == N_Sum);
            a = CH(T(3), 0);
            b = CH(T(3), 1);
            REQUIRE(matches(e, f[0], T(3)));
            input = E(3);
        } else {
            /* Computation rules require the opposite branch context (or sum
             * context) to supply the otherwise unavailable summand type. */
            if (f[0]) {
                c = e->contexts[f[0]].type;
                REQUIRE(K(c) == N_Sum);
                a = CH(c, 0);
                b = CH(c, 1);
            } else {
                a = right ? (f[1] ? e->contexts[f[1]].type : 0) : T(3);
                b = right ? T(3) : (f[2] ? e->contexts[f[2]].type : 0);
            }
            REQUIRE((right ? b : a) == T(3));
            input = make1(e, right ? N_Inr : N_Inl, E(3));
        }
        REQUIRE(matches(e, f[1], a) && matches(e, f[2], b));
        REQUIRE(!f[0] || (f[1] && f[2]));
        c = replace_ctx(e, E(0), f[0], make1(e, N_Inl, q0));
        d = replace_ctx(e, T(1), f[1], q0);
        REQUIRE(c == d);
        c = replace_ctx(e, E(0), f[0], make1(e, N_Inr, q1));
        d = replace_ctx(e, T(2), f[2], q1);
        REQUIRE(c == d);
        a = bind_ctx(e, E(1), f[1], 1);
        b = bind_ctx(e, E(2), f[2], 0);
        r->expr = make3(e, N_IndSum, a, b, input);
        r->type = replace_ctx(e, E(0), f[0], input);
        if (comp) {
            c = replace_ctx(e, E(right ? 2 : 1), f[right ? 2 : 1], E(3));
            r->expr = make2(e, N_DefEq, r->expr, c);
        }
        break;
    }
    case TT_EqElim:
    case TT_EqComp: {
        bool comp = op == TT_EqComp;
        REQUIRE(matches(e, f[0], T(2)) && matches(e, f[1], T(2)) && matches(e, f[3], T(2)));
        if (!comp) {
            REQUIRE(T(2) == T(3) && K(T(4)) == N_Eq);
            node eq = e->nodes[T(4)];
            REQUIRE(eq.ch[0] == T(2) && eq.ch[1] == E(2) && eq.ch[2] == E(3));
        }
        REQUIRE(!f[2] || (f[0] && f[1]));
        REQUIRE(!(f[0] || f[1]) || f[3]);
        if (f[2]) {
            a = make3(e, N_Eq, T(2), leaf(e, N_CRef, f[0]), leaf(e, N_CRef, f[1]));
            REQUIRE(e->contexts[f[2]].type == a);
        }
        tt_id cs[] = {f[0], f[1], f[2]}, vs[] = {q0, q0, make1(e, N_Refl, q0)};
        a = transform(e, E(0), MAP_CONTEXT, cs, vs, 3, 0);
        b = replace_ctx(e, T(1), f[3], q0);
        REQUIRE(a == b);
        body = bind_ctx(e, E(1), f[3], 0);
        input = comp ? make1(e, N_Refl, E(2)) : E(4);
        r->expr = make4(e, N_IndEq, body, E(2), comp ? E(2) : E(3), input);
        vs[0] = E(2);
        vs[1] = comp ? E(2) : E(3);
        vs[2] = input;
        r->type = transform(e, E(0), MAP_CONTEXT, cs, vs, 3, 0);
        if (comp) {
            a = replace_ctx(e, E(1), f[3], E(2));
            r->expr = make2(e, N_DefEq, r->expr, a);
        }
        break;
    }
    case TT_NatElim:
    case TT_NatCompZ:
    case TT_NatCompS: {
        a = leaf(e, N_Nat, 0);
        b = leaf(e, N_ZN, 0);
        REQUIRE(matches(e, f[0], a) && matches(e, f[1], a));
        if (op != TT_NatCompZ)
            REQUIRE(T(3) == a);
        REQUIRE(T(1) == replace_ctx(e, E(0), f[0], b));
        expected = replace_ctx(e, E(0), f[0], q0);
        if (f[2])
            REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) == expected);
        /* Preserve the upstream Nat rule's exact syntactic motive check. */
        REQUIRE(sub2(e, T(2), f[1], f[2], q0, q1) == expected);
        body = bind2(e, E(2), f[1], f[2]);
        input = op == TT_NatCompZ ? b : op == TT_NatCompS ? make1(e, N_SN, E(3)) : E(3);
        r->expr = make3(e, N_IndNat, E(1), body, input);
        r->type = replace_ctx(e, E(0), f[0], input);
        if (op == TT_NatCompZ)
            r->expr = make2(e, N_DefEq, r->expr, E(1));
        if (op == TT_NatCompS) {
            c = make3(e, N_IndNat, E(1), body, E(3));
            d = sub2(e, E(2), f[1], f[2], E(3), c);
            r->expr = make2(e, N_DefEq, r->expr, d);
        }
        break;
    }
    case TT_WElim:
    case TT_WComp: {
        bool comp = op == TT_WComp;
        tt_id wtype;
        if (!comp) {
            REQUIRE(K(T(2)) == N_W);
            wtype = T(2);
            input = E(2);
        } else {
            REQUIRE(K(T(3)) == N_Pi);
            wtype = CH(T(3), 1);
            REQUIRE(K(wtype) == N_W && CH(wtype, 0) == T(2));
            REQUIRE(CH(T(3), 0) == instantiate(e, CH(wtype, 1), E(2)));
            input = make2(e, N_WSup, E(2), E(3));
        }
        a = CH(wtype, 0);
        b = CH(wtype, 1);
        REQUIRE(matches(e, f[0], wtype) && matches(e, f[1], a));
        REQUIRE(!f[0] || (f[1] && f[2]));
        c = instantiate(e, b, q0);
        if (f[2])
            REQUIRE(replace_ctx(e, e->contexts[f[2]].type, f[1], q0) == make2(e, N_Pi, c, wtype));
        /* z is replaced by an application containing a locally bound y. */
        d = transform(e, E(0), MAP_W_MOTIVE, &f[0], &q1, 1, 0);
        expected = make2(e, N_Pi, make2(e, N_Pi, c, d),
                         replace_ctx(e, E(0), f[0], make2(e, N_WSup, q0, q1)));
        REQUIRE(sub2(e, T(1), f[1], f[2], q0, q1) == expected);
        body = bind2(e, E(1), f[1], f[2]);
        r->expr = make2(e, N_IndW, body, input);
        r->type = replace_ctx(e, E(0), f[0], input);
        if (comp) {
            a = sub2(e, E(1), f[1], f[2], E(2), E(3));
            tt_id shift = 1;
            tt_id shifted_f = transform(e, E(3), MAP_SHIFT, NULL, &shift, 1, 0);
            tt_id shifted_body = transform(e, body, MAP_SHIFT, NULL, &shift, 1, 2);
            b = make2(e, N_Ap, shifted_f, leaf(e, N_VRef, 0));
            b = make1(e, N_Lambda, make2(e, N_IndW, shifted_body, b));
            r->expr = make2(e, N_DefEq, r->expr, make2(e, N_Ap, a, b));
        }
        break;
    }
    default:
        return false;
    }
    return !e->error && r->expr && r->type;
#undef E
#undef T
#undef K
#undef CH
#undef REQUIRE
}
