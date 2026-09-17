#include "internal.h"

/* Suspension is a higher inductive type, with two points and an A-indexed
 * family of paths. The eliminator accepts a dependent motive and a section
 * over each meridian. Point computation is definitional; meridian computation
 * is a propositional equality (SuspBeta), never a rewrite of arbitrary paths.
 *
 * All premises are ordinary checked functions: this extension introduces no
 * new context-discharge convention. IndSusp stores C, n, s, and (h, x), and
 * binds no variables. The nested pair is private storage, not an extra premise.
 */
static tt_id application(tt_engine *e, tt_id f, tt_id x) {
    return make2(e, N_Ap, f, x);
}
/* Existing J encoding of transport: J (lambda z. lambda u. u) x y p, applied
 * to u. The family is erased from terms, exactly as in the existing EqElim.
 * Its type is validated separately by the calling rule. */
static tt_id transport_term(tt_engine *e, tt_id x, tt_id y, tt_id p, tt_id u) {
    tt_id identity = make1(e, N_Lambda, leaf(e, N_VRef, 0));
    return application(e, make4(e, N_IndEq, identity, x, y, p), u);
}
/* J's reflexive branch for dependent application is refl(f(z)). IndEq binds
 * z in its branch, with the same virtual level as existing equality induction. */
static tt_id apd_term(tt_engine *e, tt_id f, tt_id x, tt_id y, tt_id p) {
    tt_id shift = 1;
    tt_id lifted = transform(e, f, MAP_SHIFT, NULL, &shift, 1, 0);
    tt_id base = make1(e, N_Refl, application(e, lifted, leaf(e, N_VRef, 0)));
    return make4(e, N_IndEq, base, x, y, p);
}
static bool path_has_type(tt_engine *e, tt_id t, tt_id A, tt_id x, tt_id y) {
    node n = e->nodes[t];
    return n.kind == N_Eq && n.ch[0] == A && n.ch[1] == x && n.ch[2] == y;
}

bool infer_suspension(tt_engine *e, tt_opcode op, const judgement *j, judgement *r) {
#define E(i) (j[i].expr)
#define T(i) (j[i].type)
#define REQUIRE(test)                                                                              \
    do {                                                                                           \
        if (!(test))                                                                               \
            return false;                                                                          \
    } while (0)
    if (op == TT_SuspForm || op == TT_SuspNorth || op == TT_SuspSouth || op == TT_SuspMerid) {
        REQUIRE(universe(e, T(0)));
        tt_id suspension = make1(e, N_Susp, E(0));
        r->type = suspension;
        if (op == TT_SuspForm) {
            r->expr = suspension;
            r->type = T(0);
        } else if (op == TT_SuspNorth || op == TT_SuspSouth) {
            r->expr = make1(e, op == TT_SuspNorth ? N_North : N_South, E(0));
        } else {
            REQUIRE(T(1) == E(0));
            r->expr = make2(e, N_Merid, E(0), E(1));
            r->type = make3(e, N_Eq, suspension, make1(e, N_North, E(0)), make1(e, N_South, E(0)));
        }
    } else if (op == TT_Transport || op == TT_Apd) {
        node ft = e->nodes[T(0)];
        REQUIRE(ft.kind == N_Pi && T(1) == ft.ch[0] && T(2) == ft.ch[0]);
        REQUIRE(path_has_type(e, T(3), ft.ch[0], E(1), E(2)));
        if (op == TT_Transport) {
            REQUIRE(universe(e, ft.ch[1]));
            REQUIRE(T(4) == application(e, E(0), E(1)));
            r->expr = transport_term(e, E(1), E(2), E(3), E(4));
            r->type = application(e, E(0), E(2));
        } else {
            tt_id fx = application(e, E(0), E(1));
            tt_id fy = application(e, E(0), E(2));
            r->expr = apd_term(e, E(0), E(1), E(2), E(3));
            r->type = make3(e, N_Eq, instantiate(e, ft.ch[1], E(2)),
                           transport_term(e, E(1), E(2), E(3), fx), fy);
        }
    } else {
        REQUIRE(op == TT_SuspElim || op == TT_SuspMeridComp);
        node motive_type = e->nodes[T(0)];
        REQUIRE(motive_type.kind == N_Pi && universe(e, motive_type.ch[1]));
        node suspension = e->nodes[motive_type.ch[0]];
        REQUIRE(suspension.kind == N_Susp);
        tt_id A = suspension.ch[0];
        tt_id north = make1(e, N_North, A), south = make1(e, N_South, A);
        REQUIRE(T(1) == application(e, E(0), north));
        REQUIRE(T(2) == application(e, E(0), south));
        node coherence_type = e->nodes[T(3)];
        REQUIRE(coherence_type.kind == N_Pi && coherence_type.ch[0] == A);
        tt_id a = leaf(e, N_Temp, 0);
        tt_id meridian = make2(e, N_Merid, A, a);
        tt_id expected = make3(e, N_Eq, T(2), transport_term(e, north, south, meridian, E(1)), E(2));
        REQUIRE(instantiate(e, coherence_type.ch[1], a) == expected);
        if (op == TT_SuspElim) {
            REQUIRE(T(4) == motive_type.ch[0]);
            r->expr = make4(e, N_IndSusp, E(0), E(1), E(2), make2(e, N_Tuple, E(3), E(4)));
            r->type = application(e, E(0), E(4));
        } else {
            REQUIRE(T(4) == A);
            meridian = make2(e, N_Merid, A, E(4));
            tt_id shift = 1, data[4];
            for (unsigned i = 0; i < 4; i++)
                data[i] = transform(e, E(i), MAP_SHIFT, NULL, &shift, 1, 0);
            tt_id body = make4(e, N_IndSusp, data[0], data[1], data[2],
                               make2(e, N_Tuple, data[3], leaf(e, N_VRef, 0)));
            tt_id section = make1(e, N_Lambda, body);
            tt_id equality = make3(e, N_Eq, T(2), transport_term(e, north, south, meridian, E(1)), E(2));
            r->expr = make4(e, N_SuspBeta, E(0), E(1), E(2), make2(e, N_Tuple, E(3), E(4)));
            r->type = make3(e, N_Eq, equality, apd_term(e, section, north, south, meridian),
                            application(e, E(3), E(4)));
        }
    }
    return !e->error && r->expr && r->type;
#undef E
#undef T
#undef REQUIRE
}
