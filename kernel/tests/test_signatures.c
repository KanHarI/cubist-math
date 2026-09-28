/* Declared types (H1), families F1 and F6: signatures are admitted one
 * constructor at a time, and refused where the specification's acceptance
 * cases say (docs/roadmaps/h1-signature-specification.md, section 10). Every
 * constructor type is derived here by ordinary instructions, as the driver
 * derives it. */
#include "cubical_kernel.h"
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static cc_kernel *k;
/* Signatures admitted by the sections below, for the instance tests. */
static uint32_t nat_signature, list_signature, circle_signature, trunc_signature, pointed_signature,
    tagged_signature, tree_signature, wrapped_signature, branch_signature, torus_signature, susp_signature,
    set_signature, groupoid_signature;

static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) {
        fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k));
        assert(0);
    }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)

static void rejects(uint32_t id, const char *fragment, int line) {
    if (id || !strstr(cc_kernel_error(k), fragment)) {
        fprintf(stderr, "line %d: expected a refusal with \"%s\", got %u and \"%s\"\n", line, fragment, id,
                cc_kernel_error(k));
        assert(0);
    }
    cc_kernel_clear_error(k);
}
#define REJECTS(x, fragment) rejects((x), (fragment), __LINE__)

static cc_term lconst(unsigned n) { return cc_kernel_term(k, CC_LCONST, n, 0, 0, 0, 0); }
static cc_term lvar(uint32_t symbol) { return cc_kernel_term(k, CC_VAR, symbol, 0, 0, 0, 0); }
static cc_term lsucc(cc_term level) { return cc_kernel_term(k, CC_LSUCC, 1, level, 0, 0, 0); }
static cc_judgement_id var(cc_entry_id e) { return OK(cc_instr_variable(k, e)); }
static cc_judgement_id universe(cc_term level) { return OK(cc_instr_universe(k, level)); }
static cc_signature_info signature(uint32_t index) {
    cc_signature_info info;
    assert(cc_kernel_signature(k, index, &info));
    return info;
}
static cc_constructor_info constructor(uint32_t index, uint32_t c) {
    cc_constructor_info info;
    assert(cc_kernel_signature_constructor(k, index, c, &info));
    return info;
}
static cc_term_kind kind(cc_term t) { cc_term_kind result; assert(cc_kernel_node(k, t, &result, NULL, NULL)); return result; }

static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info result; assert(cc_kernel_judgement(k, j, &result)); return result; }
static cc_term term_of(cc_judgement_id j) { return info(j).term; }
static cc_term type_of(cc_judgement_id j) { return info(j).type; }
static cc_term child(cc_term t, unsigned i) { cc_term c[4]; assert(cc_kernel_node(k, t, NULL, NULL, c)); return c[i]; }
static uint32_t payload(cc_term t) { uint32_t p; assert(cc_kernel_node(k, t, NULL, &p, NULL)); return p; }
static cc_term tier1(unsigned n) { return cc_kernel_term(k, CC_LCONST, 1u << 16 | n, 0, 0, 0, 0); }

/* Symbols. Each signature gets its own, as a driver's supply would give. */
enum {
    X = 1, Y, A, B, L, P,
    S_N = 10, ZERO, SUCC, M,
    S_LIST = 20, NIL, CONS, HEAD, TAIL,
    S_S1 = 30, BASE, LOOP,
    S_T = 40, TB, TP, TQ, SURF,
    S_S2 = 50, S2BASE, S2SURF,
    S_TR = 60, POINT, VALUE,
    S_PT = 70, PT, CARRIER, ELEMENT,
    S_H = 80, HOLD, HB,
    S_BAD = 90, BAD, BF, BG, BN, BX, C1, C2, LATER, OTHER, BH, Z,
    S_Q = 110, CLASS, QA,
    S_G = 120, GPOINT, GA,
    S_BOTH = 130, MK, BOTH_A, BOTH_B,
    S_TREE = 400, TREE_L, TREE_ARG, TREE_B, TREE_LV, TREE_BV, TREE_C, SUP,
    S_QUO = 410, QUO_A, QUO_ARG1, QUO_ARG2, QUO_R, QUO_X, QUO_Y, QUO_RR, CLS, QEQ,
    S_CAN = 420, CAN_LEAF, CAN_NODE, CAN_N, CAN_F,
    S_WR = 430, WR_BASE, WR_LOOP, WR_P, WR_WRAP, WR_FIX,
    S_BR = 440, BR_A, BR_LEAF, BR_NODE, BR_X, BR_F, BR_COLLAPSE,
    S_TAG = 450, TAG_A, TAG_X, TAG_B, TAG,
    S_HID = 460, HID_BASE, HID_LOOP, HID_Y, HID_T, HID_C,
    S_GEN = 470, GEN_C,
    S_OPEN = 480, OPEN_C, TREE_N, S_GONE,
    S_SUSP = 490, SUSP_A, NORTH, SOUTH, MERID, SUSP_X,
    S_PUSH = 500, PUSH_C, PUSH_A, PUSH_B, PUSH_ARG, PUSH_F, PUSH_G, PUSH_X, PUSH_Y, INL, INR, PUSH_Z, PUSH, PUSH_N,
    KAN_A = 520, KAN_B, KAN_E, KAN_X, KAN_M, KAN_Q, KAN_Y = 540,
    ELIM_P = 600, ELIM_PZ = 602, ELIM_N, ELIM_H, ELIM_PS, ELIM_Z, ELIM_Q, ELIM_PB = 609, ELIM_PB2, ELIM_PL, ELIM_PL2,
    ELIM_T = 620, ELIM_A = 622, ELIM_PP, ELIM_B, ELIM_W, ELIM_L = 627, ELIM_BB, ELIM_C, ELIM_CBAR, ELIM_MS,
    ELIM_V = 640, ELIM_PV = 642, ELIM_PW, ELIM_WV, ELIM_WP, ELIM_WPB, ELIM_MW,
    S_PW = 700, PW_BASE, PW_LOOP, PW_P, PW_WRAP, PW_V, PW_PV = 707, PW_PL, PW_PE, PW_PBAR, PW_MW, PW_P0,
    S_BOX = 720, BOX_N, BOX, BOX_Z, BOX_X, AMB_Z = 730, AMB_P, AMB_F, AMB_FB, AMB_FL,
    ACC_C = 740, ACC_R, A6_N, A6_X, A6_G, E9_Y, E9_Z, E9_YB, E9_ZB, E9_SQ, E10_Z, E10_P, E10_PB, E10_PL,
    S_RES = 760, S_ARGS, S_DEEP, RES_B, RES_F, RES_A = RES_F + 3,
    HB_X = 780, HB_A, HB_B, HB_MA, HB_MB, HB_MK, HB_TA, HB_HERE, HB_T, HB_WRAP, HB_FA, HB_F, HB_BB, HB_PACK, HB_Z,
    HB_FF, HB_WRAP2, HB_WRAP3, HB_UZ,
    S_MIXED = 810, S_TAG2, S_OUTER, S_HID2, S_BIG, S_OUTER2,
    RES_C = 3000, RES_N = 3400
};

/* ⊢ U(0) : U(1), the former of a signature with no parameters in U0. */
static cc_judgement_id former_u0(void) { return universe(lconst(0)); }

/* ⊢ Π (x < ω). Π (A : U(x)). U(x) : U(ω), with x and A named by the
 * given symbols: the former of List, Trunc and the like. */
static cc_judgement_id former_generic(uint32_t x, uint32_t a, cc_entry_id *xe, cc_entry_id *ae) {
    *xe = OK(cc_instr_level(k, x));
    cc_judgement_id ux = universe(lvar(x));
    *ae = OK(cc_instr_extend(k, ux, a));
    cc_judgement_id body = OK(cc_instr_pi(k, *ae, ux));
    return OK(cc_instr_level_pi(k, *xe, body));
}

static void natural_numbers(void) {
    /* inductive N { zero; succ(n : N); } */
    uint32_t index;
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_N, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_N));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), ZERO));
    cc_entry_id zero = OK(cc_instr_extend(k, var(s), ZERO));
    (void)zero;
    cc_entry_id n = OK(cc_instr_extend(k, var(s), M));
    cc_judgement_id succ_type = OK(cc_instr_pi(k, n, var(s)));
    sig = OK(cc_instr_signature_constructor(k, sig, succ_type, SUCC));
    index = OK(cc_instr_signature_close(k, sig));
    nat_signature = index;
    cc_signature_info info = signature(index);
    assert(info.admitted && info.experimental && info.constructor_count == 2 && !info.level_count);
    cc_constructor_info succ = constructor(index, 1);
    assert(succ.symbol == SUCC && succ.data == 0 && succ.positions == 1 && succ.dimensions == 0 && !succ.generated);
    /* A14: an admitted signature never changes. */
    REJECTS(cc_instr_signature_close(k, sig), "already admitted");
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), OTHER), "already admitted");
}

static void lists(void) {
    /* inductive List(U < UU0, A : U) { nil; cons(head : A, tail : List); }: the
     * universe parameter is erased, determined by A : U(x). */
    cc_entry_id xe, ae;
    cc_judgement_id former = former_generic(X, A, &xe, &ae);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_LIST, 0));
    cc_entry_id s = OK(cc_instr_extend(k, universe(lvar(X)), S_LIST));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), NIL));
    OK(cc_instr_extend(k, var(s), NIL));
    cc_entry_id head = OK(cc_instr_extend(k, var(ae), HEAD));
    cc_entry_id tail = OK(cc_instr_extend(k, var(s), TAIL));
    cc_judgement_id cons_type = OK(cc_instr_pi(k, head, OK(cc_instr_pi(k, tail, var(s)))));
    sig = OK(cc_instr_signature_constructor(k, sig, cons_type, CONS));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    list_signature = index;
    cc_signature_info info = signature(index);
    assert(info.level_count == 1 && info.parameter_count == 1 && info.recorded == 0);
    assert(cc_kernel_signature_symbol(k, index, 0) == X && cc_kernel_signature_symbol(k, index, 1) == A);
    cc_constructor_info cons = constructor(index, 1);
    assert(cons.data == 1 && cons.positions == 1 && cons.dimensions == 0);
}

/* The circle: base; loop : Path(i; s, base, base). */
static void circle(void) {
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_S1, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_S1));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), BASE));
    cc_entry_id base = OK(cc_instr_extend(k, var(s), BASE));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, LOOP));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    circle_signature = index;
    cc_constructor_info loop = constructor(index, 1);
    assert(loop.dimensions == 1 && loop.data == 0 && loop.positions == 0);
}

/* A2: the torus, whose square's inner endpoints are p @ i, and S2, whose
 * outer endpoints are path abstractions ⟨j⟩ base. */
static void squares(void) {
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_T, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_T));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), TB));
    cc_entry_id b = OK(cc_instr_extend(k, var(s), TB));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    /* p and q : Path(j; s, b, b), over the dimension the square's inner paths use. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, j, var(s), var(b), var(b)));
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, TP));
    cc_entry_id p = OK(cc_instr_extend(k, loop_type, TP));
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, TQ));
    cc_entry_id q = OK(cc_instr_extend(k, loop_type, TQ));
    /* surf : Path(i; Path(j; s, p @ i, p @ i), q, q). At i = 0 the family is
     * Path(j; s, p @ 0, p @ 0), which reduces to q's type; the driver
     * converts q there, as it would. */
    cc_judgement_id p_i = OK(cc_instr_path_apply(k, var(p), i, 0));
    cc_judgement_id inner = OK(cc_instr_path(k, j, var(s), p_i, p_i));
    cc_judgement_id at0 = OK(cc_instr_endpoint(k, inner, i, 0));
    cc_judgement_id at1 = OK(cc_instr_endpoint(k, inner, i, 1));
    /* inner(0) = Path(j; s, p @ 0, p @ 0); p @ 0 steps to b by the path step. */
    cc_judgement_id eq0 = OK(cc_instr_refl(k, at0));
    eq0 = OK(cc_instr_step(k, eq0, 1, (const uint8_t[]){1}, 1, CC_STEP_PATH));
    eq0 = OK(cc_instr_step(k, eq0, 1, (const uint8_t[]){2}, 1, CC_STEP_PATH));
    cc_judgement_id eq1 = OK(cc_instr_refl(k, at1));
    eq1 = OK(cc_instr_step(k, eq1, 1, (const uint8_t[]){1}, 1, CC_STEP_PATH));
    eq1 = OK(cc_instr_step(k, eq1, 1, (const uint8_t[]){2}, 1, CC_STEP_PATH));
    cc_judgement_id q0 = OK(cc_instr_convert(k, var(q), OK(cc_instr_symmetry(k, eq0))));
    cc_judgement_id q1 = OK(cc_instr_convert(k, var(q), OK(cc_instr_symmetry(k, eq1))));
    cc_judgement_id surf_type = OK(cc_instr_path(k, i, inner, q0, q1));
    sig = OK(cc_instr_signature_constructor(k, sig, surf_type, SURF));
    uint32_t torus = torus_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(torus, 3).dimensions == 2);
    /* A10: a square whose sides do not meet the inner paths at a corner.
     * Over the constant inner family Path(j; s, b, b), a side q : Path(j; s,
     * b, b) meets it at every corner, and the square's path type is formed;
     * r : Path(j; s, c, c), for another point c, does not, and it is not. */
    cc_judgement_id flat_inner = OK(cc_instr_path(k, j, var(s), var(b), var(b)));
    cc_entry_id side = OK(cc_instr_extend(k, flat_inner, ACC_R + 100));
    OK(cc_instr_path(k, i, flat_inner, var(side), var(side)));
    cc_entry_id c = OK(cc_instr_extend(k, var(s), ACC_C));
    cc_entry_id r = OK(cc_instr_extend(k, OK(cc_instr_path(k, j, var(s), var(c), var(c))), ACC_R));
    REJECTS(cc_instr_path(k, i, flat_inner, var(r), var(r)), "endpoint has the wrong type");

    /* S2: base; surf : Path(i; Path(j; s, base, base), ⟨j⟩ base, ⟨j⟩ base). */
    sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_S2, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_S2));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), S2BASE));
    cc_entry_id base = OK(cc_instr_extend(k, var(s), S2BASE));
    cc_judgement_id flat = OK(cc_instr_path(k, j, var(s), var(base), var(base)));
    cc_judgement_id constant = OK(cc_instr_path_lambda(k, j, var(base)));
    cc_judgement_id s2_type = OK(cc_instr_path(k, i, flat, constant, constant));
    sig = OK(cc_instr_signature_constructor(k, sig, s2_type, S2SURF));
    uint32_t sphere = OK(cc_instr_signature_close(k, sig));
    assert(constructor(sphere, 1).dimensions == 2);
}

/* A3, A17 and the squash of 1.6: prop, set and trunc(1) add one generated
 * constructor with 1, 2 and 3 dimensions. */
static void truncations(void) {
    const uint32_t modifiers[] = {1, 2, 3};
    const uint32_t sorts[] = {S_TR, S_Q, S_G};
    for (unsigned m = 0; m < 3; ++m) {
        cc_entry_id xe, ae;
        uint32_t base = 200 + 10 * m;
        cc_judgement_id former = former_generic(base, base + 1, &xe, &ae);
        cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, modifiers[m], sorts[m], 0));
        cc_entry_id s = OK(cc_instr_extend(k, universe(lvar(base)), sorts[m]));
        cc_entry_id a = OK(cc_instr_extend(k, var(ae), base + 2));
        sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, a, var(s))), base + 3));
        uint32_t index = OK(cc_instr_signature_close(k, sig));
        if (m == 0) trunc_signature = index;
        if (m == 1) set_signature = index;
        if (m == 2) groupoid_signature = index;
        cc_signature_info info = signature(index);
        assert(info.constructor_count == 2 && info.modifier == modifiers[m]);
        cc_constructor_info squash = constructor(index, 1);
        assert(squash.generated && squash.data == 0);
        assert(squash.dimensions == modifiers[m] && squash.positions == 2 * modifiers[m]);
        /* Its type: pairs of cells, then a path type; the carrier is the sort. */
        assert(kind(squash.type) == CC_PI);
    }
}

/* Q15, V20: Pointed(U < UU0) : next(U) { pt(X : U, x : X); } has a recorded
 * universe parameter, which its constructor type mentions. V24: proposed
 * erased, a parameter a constructor type mentions is refused. */
static void recorded_parameters(void) {
    cc_entry_id xe = OK(cc_instr_level(k, Y));
    cc_judgement_id next = universe(lsucc(lvar(Y)));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, next));
    /* V14: with nothing to read it from, the parameter is not erasable. */
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_PT, 0), "determining occurrence");
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_PT, 1));
    cc_entry_id s = OK(cc_instr_extend(k, next, S_PT));
    cc_entry_id carrier = OK(cc_instr_extend(k, universe(lvar(Y)), CARRIER));
    cc_entry_id element = OK(cc_instr_extend(k, var(carrier), ELEMENT));
    cc_judgement_id pt_type = OK(cc_instr_pi(k, carrier, OK(cc_instr_pi(k, element, var(s)))));
    /* pt's type lives in U(y + 1), the declared level. */
    sig = OK(cc_instr_signature_constructor(k, sig, pt_type, PT));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    pointed_signature = index;
    assert(signature(index).recorded == 1 && constructor(index, 0).data == 2);

    /* Holder(x < ω, A : U(x)) : U(x + 1) { hold(B : U(x)); } with x proposed
     * erased: A : U(x) determines it, but hold's type mentions it. */
    cc_entry_id he = OK(cc_instr_level(k, X));
    cc_judgement_id ux = universe(lvar(X));
    cc_entry_id ha = OK(cc_instr_extend(k, ux, A));
    cc_judgement_id hnext = universe(lsucc(lvar(X)));
    cc_judgement_id hformer = OK(cc_instr_level_pi(k, he, OK(cc_instr_pi(k, ha, hnext))));
    cc_judgement_id hsig = OK(cc_instr_signature_begin(k, hformer, CC_UNTRUNCATED, S_H, 0));
    cc_entry_id hs = OK(cc_instr_extend(k, hnext, S_H));
    cc_entry_id hb = OK(cc_instr_extend(k, ux, HB));
    cc_judgement_id hold_type = OK(cc_instr_pi(k, hb, var(hs)));
    REJECTS(cc_instr_signature_constructor(k, hsig, hold_type, HOLD), "erased universe parameter");
    /* Recorded, the same signature is admitted. */
    cc_judgement_id recorded = OK(cc_instr_signature_begin(k, hformer, CC_UNTRUNCATED, S_H, 1));
    recorded = OK(cc_instr_signature_constructor(k, recorded, hold_type, HOLD));
    OK(cc_instr_signature_close(k, recorded));
}

/* F2: instances and constructors (section 5.3, formation 3.1, constructors
 * 3.2). */
static void instances(void) {
    /* N, with no parameters, is complete at once; succ(zero) : N. */
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    assert(info(n).kind == 1 && kind(term_of(n)) == CC_SORT && kind(type_of(n)) == CC_U);
    cc_judgement_id zero = OK(cc_instr_construct(k, n, 0)), succ = OK(cc_instr_construct(k, n, 1));
    assert(kind(term_of(zero)) == CC_CON && payload(term_of(zero)) == 0 && type_of(zero) == term_of(n));
    assert(kind(type_of(succ)) == CC_PI && child(type_of(succ), 0) == term_of(n) && child(type_of(succ), 1) == term_of(n));
    assert(type_of(OK(cc_instr_apply(k, succ, zero))) == term_of(n));
    REJECTS(cc_instr_construct(k, n, 2), "no such constructor");

    /* V1, V7: List(Nat) reads x := 0 from Nat : U0. Lifted to U1, the same
     * instance term lives in U1: the erased level is not part of it. */
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_judgement_id list0 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, list_signature)), nat));
    cc_judgement_id nat1 = OK(cc_instr_lift(k, nat, universe(lconst(1))));
    cc_judgement_id list1 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, list_signature)), nat1));
    assert(term_of(list1) == term_of(list0));
    assert(type_of(list0) == term_of(universe(lconst(0))) && type_of(list1) == term_of(universe(lconst(1))));
    cc_term cons_type = type_of(OK(cc_instr_construct(k, list0, 1)));
    assert(kind(child(cons_type, 0)) == CC_NAT && child(child(cons_type, 1), 0) == term_of(list0));
    /* V8: a reading at tier 1 is refused. */
    cc_judgement_id big = OK(cc_instr_lift(k, nat, universe(tier1(0))));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, list_signature)), big), "finite levels only");

    /* The loop at the circle's instance: Path(i; S1, base, base). */
    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_term loop = type_of(OK(cc_instr_construct(k, s1, 1)));
    assert(kind(loop) == CC_PATH && kind(child(loop, 1)) == CC_CON && payload(child(loop, 1)) == 0);
    assert(child(child(loop, 1), 0) == term_of(s1));
    /* The squash at Trunc(Nat): Π (y z : Trunc(Nat)). Path(Trunc(Nat), y, z). */
    cc_judgement_id tr = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), nat));
    cc_term squash = type_of(OK(cc_instr_construct(k, tr, 1)));
    assert(kind(squash) == CC_PI && child(squash, 0) == term_of(tr));

    /* V20: Pointed(U0) : U1 and Pointed(U1) : U2 are distinct. Recorded
     * levels come first, and are finite. */
    cc_judgement_id p = OK(cc_instr_sort_begin(k, pointed_signature));
    REJECTS(cc_instr_sort_parameter(k, p, nat), "recorded levels");
    REJECTS(cc_instr_sort_level(k, p, tier1(0)), "finite levels only");
    cc_judgement_id p0 = OK(cc_instr_sort_level(k, p, lconst(0))), p1 = OK(cc_instr_sort_level(k, p, lconst(1)));
    assert(term_of(p0) != term_of(p1));
    assert(type_of(p0) == term_of(universe(lconst(1))) && type_of(p1) == term_of(universe(lconst(2))));
    cc_term pt0 = type_of(OK(cc_instr_construct(k, p0, 0)));
    assert(child(pt0, 0) == term_of(universe(lconst(0))));

    /* V15: Both(x < ω, A, B : U(x)) { mk(a : A, b : B); }: two readings of x
     * must agree; lifting the lower parameter makes them agree. */
    cc_entry_id xe = OK(cc_instr_level(k, X));
    cc_judgement_id ux = universe(lvar(X));
    cc_entry_id ae = OK(cc_instr_extend(k, ux, A)), be = OK(cc_instr_extend(k, ux, B));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, ae, OK(cc_instr_pi(k, be, ux))))));
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_BOTH, 0));
    cc_entry_id s = OK(cc_instr_extend(k, ux, S_BOTH));
    cc_entry_id a = OK(cc_instr_extend(k, var(ae), BOTH_A)), b = OK(cc_instr_extend(k, var(be), BOTH_B));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, b, var(s))))), MK));
    uint32_t both = OK(cc_instr_signature_close(k, sig));
    cc_judgement_id unit1 = OK(cc_instr_lift(k, OK(cc_instr_unit(k)), universe(lconst(1))));
    cc_judgement_id half = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, both)), nat));
    REJECTS(cc_instr_sort_parameter(k, half, unit1), "lift the lower parameter first");
    cc_judgement_id lifted = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, both)), nat1));
    assert(type_of(OK(cc_instr_sort_parameter(k, lifted, unit1))) == term_of(universe(lconst(1))));

    /* V16: λ (x < ω). Trunc(U(x)) at 0 is Trunc(U(0)) : U(1), by LevelApply and
     * a Beta step: level substitution reaches the instance's parameters. */
    cc_judgement_id trunc_ux = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), ux));
    assert(type_of(trunc_ux) == term_of(universe(lsucc(lvar(X)))));
    cc_judgement_id at0 = OK(cc_instr_level_apply(k, OK(cc_instr_level_lambda(k, xe, trunc_ux)), lconst(0)));
    assert(type_of(at0) == term_of(universe(lconst(1))));
    cc_judgement_id reduced = OK(cc_instr_step(k, OK(cc_instr_refl(k, at0)), 1, NULL, 0, CC_STEP_BETA));
    cc_term instance = info(reduced).other;
    assert(kind(instance) == CC_SORT && child(child(instance, 0), 0) == term_of(universe(lconst(0))));
    /* A recorded level may be a level variable in the context, and no other;
     * an instance in progress has no constructors. */
    cc_judgement_id px = OK(cc_instr_sort_level(k, p, lvar(X)));
    assert(type_of(px) == term_of(universe(lsucc(lvar(X)))) && cc_kernel_judgement_context(k, px, 0) == xe);
    REJECTS(cc_instr_sort_level(k, p, lvar(S_GONE)), "Unbound level variable");
    REJECTS(cc_instr_construct(k, p, 0), "Expected a typing judgement");
    REJECTS(cc_instr_sort_level(k, p0, lconst(0)), "Expected an instance in progress");

    /* V25: Tagged{0}(Nat) reads x from Nat; Nat lifted to U1 gives the same
     * term, and y := 1 another. tag : Π (a : Nat). Π (B : U0). Tagged{0}(Nat). */
    cc_judgement_id t0 = OK(cc_instr_sort_level(k, OK(cc_instr_sort_begin(k, tagged_signature)), lconst(0)));
    cc_judgement_id tagged_nat = OK(cc_instr_sort_parameter(k, t0, nat));
    cc_judgement_id tagged_lifted = OK(cc_instr_sort_parameter(k, t0, nat1));
    assert(term_of(tagged_nat) == term_of(tagged_lifted));
    assert(type_of(tagged_nat) == term_of(universe(lconst(1))) && type_of(tagged_lifted) == type_of(tagged_nat));
    cc_judgement_id t1 = OK(cc_instr_sort_level(k, OK(cc_instr_sort_begin(k, tagged_signature)), lconst(1)));
    cc_judgement_id tagged_up = OK(cc_instr_sort_parameter(k, t1, nat));
    assert(term_of(tagged_up) != term_of(tagged_nat) && type_of(tagged_up) == term_of(universe(lconst(2))));
    cc_term tag = type_of(OK(cc_instr_construct(k, tagged_nat, 0)));
    assert(kind(child(tag, 0)) == CC_NAT && child(child(tag, 1), 0) == term_of(universe(lconst(0))));
    assert(child(child(tag, 1), 1) == term_of(tagged_nat));

    /* Tree(Nat, λ n. Nat) : U0; sup : Π (l : Nat). Π (c : Π (b : (λ n. Nat)(l)). T). T,
     * with T the instance: the position's arity is instantiated too. */
    cc_entry_id tn = OK(cc_instr_extend(k, nat, TREE_N));
    cc_judgement_id tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k,
        OK(cc_instr_sort_begin(k, tree_signature)), nat)), OK(cc_instr_lambda(k, tn, nat))));
    assert(type_of(tree) == term_of(universe(lconst(0))));
    /* An instance in progress is not rewritten: a copy would lose its count
     * of the arguments supplied, and a later argument would be dropped. */
    cc_judgement_id half_tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, tree_signature)), nat));
    REJECTS(cc_instr_step(k, half_tree, 0, NULL, 0, CC_STEP_WHNF), "not rewritten");
    REJECTS(cc_instr_replace(k, half_tree, 0, (const uint8_t[]){0, 0}, 2, OK(cc_instr_refl(k, nat))), "not rewritten");
    cc_term sup = type_of(OK(cc_instr_construct(k, tree, 0)));
    cc_term position = child(child(sup, 1), 0);
    assert(kind(child(sup, 0)) == CC_NAT && kind(position) == CC_PI && kind(child(position, 0)) == CC_APP);
    assert(child(position, 1) == term_of(tree) && child(child(sup, 1), 1) == term_of(tree));

    /* Constructor expressions at an instance: fix : wrap(⟨i⟩ loop @ i) = base,
     * and collapse's λ, mention the signature's names nowhere, in the
     * annotations they carry included. */
    cc_term fix = type_of(OK(cc_instr_construct(k, OK(cc_instr_sort_begin(k, wrapped_signature)), 3)));
    const uint32_t wrapped_names[] = {S_WR, WR_BASE, WR_LOOP, WR_WRAP, WR_P};
    for (unsigned n = 0; n < 5; ++n) assert(!ck_term_free(k, fix, wrapped_names[n]));
    cc_term wrap_at = child(fix, 1);
    assert(kind(wrap_at) == CC_APP && kind(child(wrap_at, 0)) == CC_CON && payload(child(wrap_at, 0)) == 2);
    cc_judgement_id branch = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, branch_signature)), nat));
    cc_term collapse = type_of(OK(cc_instr_construct(k, branch, 2)));
    const uint32_t branch_names[] = {S_BR, BR_A, BR_LEAF, BR_NODE};
    for (unsigned n = 0; n < 4; ++n) assert(!ck_term_free(k, collapse, branch_names[n]));

    /* Section 5.3's refusals: an open signature, and a rolled-back one. */
    cc_judgement_id open = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_OPEN, 0));
    REJECTS(cc_instr_sort_begin(k, payload(term_of(open))), "Only an admitted signature");
    cc_entry_id os = OK(cc_instr_extend(k, former_u0(), S_OPEN));
    OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, open, var(os), OPEN_C))));
    REJECTS(cc_instr_sort_begin(k, 0), "Only an admitted signature");
    cc_kernel_checkpoint(k);
    cc_judgement_id gone = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_GONE, 0));
    cc_entry_id gs = OK(cc_instr_extend(k, former_u0(), S_GONE));
    uint32_t forgotten = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, gone, var(gs), OPEN_C))));
    OK(cc_instr_sort_begin(k, forgotten));
    cc_kernel_rollback(k);
    REJECTS(cc_instr_sort_begin(k, forgotten), "Only an admitted signature");
}

/* Section 1.3's positions with arities, and boundaries that apply earlier
 * constructors to data and to positional arguments. */
static void shapes(void) {
    /* V4: Tree(x, y < ω, L : U(x), B : L → U(y)) : U(max(x, y))
     * { sup(l : L, c : Π (b : B(l)). s); }: a position of arity one. */
    cc_entry_id xe = OK(cc_instr_level(k, X)), ye = OK(cc_instr_level(k, Y));
    cc_judgement_id ux = universe(lvar(X)), uy = universe(lvar(Y));
    cc_judgement_id top = universe(cc_kernel_term(k, CC_LMAX, 0, lvar(X), lvar(Y), 0, 0));
    cc_entry_id le = OK(cc_instr_extend(k, ux, TREE_L));
    cc_entry_id arg = OK(cc_instr_extend(k, var(le), TREE_ARG));
    cc_entry_id be = OK(cc_instr_extend(k, OK(cc_instr_pi(k, arg, uy)), TREE_B));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_level_pi(k, ye,
        OK(cc_instr_pi(k, le, OK(cc_instr_pi(k, be, top))))))));
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_TREE, 0));
    cc_entry_id s = OK(cc_instr_extend(k, top, S_TREE));
    cc_entry_id l = OK(cc_instr_extend(k, var(le), TREE_LV));
    cc_entry_id b = OK(cc_instr_extend(k, OK(cc_instr_apply(k, var(be), var(l))), TREE_BV));
    cc_entry_id c = OK(cc_instr_extend(k, OK(cc_instr_pi(k, b, var(s))), TREE_C));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, l, OK(cc_instr_pi(k, c, var(s))))), SUP));
    uint32_t tree = tree_signature = OK(cc_instr_signature_close(k, sig));
    assert(signature(tree).level_count == 2 && signature(tree).recorded == 0);
    cc_constructor_info sup = constructor(tree, 0);
    assert(sup.data == 1 && sup.positions == 1 && sup.dimensions == 0);

    /* A3: Quotient(x < ω, A : U(x), R : A → A → U(x)) : set
     * { cls(a : A); eq(a b : A, r : R a b) : Path(s, cls(a), cls(b)); }: a
     * boundary applies an earlier constructor to data. */
    cc_entry_id qa = OK(cc_instr_extend(k, ux, QUO_A));
    cc_entry_id q1 = OK(cc_instr_extend(k, var(qa), QUO_ARG1)), q2 = OK(cc_instr_extend(k, var(qa), QUO_ARG2));
    cc_entry_id qr = OK(cc_instr_extend(k, OK(cc_instr_pi(k, q1, OK(cc_instr_pi(k, q2, ux)))), QUO_R));
    former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, qa, OK(cc_instr_pi(k, qr, ux))))));
    sig = OK(cc_instr_signature_begin(k, former, 2, S_QUO, 0));
    s = OK(cc_instr_extend(k, ux, S_QUO));
    cc_entry_id a = OK(cc_instr_extend(k, var(qa), QUO_X)), y = OK(cc_instr_extend(k, var(qa), QUO_Y));
    cc_judgement_id cls_type = OK(cc_instr_pi(k, a, var(s)));
    sig = OK(cc_instr_signature_constructor(k, sig, cls_type, CLS));
    cc_entry_id cls = OK(cc_instr_extend(k, cls_type, CLS));
    cc_entry_id r = OK(cc_instr_extend(k, OK(cc_instr_apply(k, OK(cc_instr_apply(k, var(qr), var(a))), var(y))), QUO_RR));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id related = OK(cc_instr_path(k, i, var(s), OK(cc_instr_apply(k, var(cls), var(a))),
                                               OK(cc_instr_apply(k, var(cls), var(y)))));
    cc_judgement_id eq_type = OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, y, OK(cc_instr_pi(k, r, related))))));
    sig = OK(cc_instr_signature_constructor(k, sig, eq_type, QEQ));
    uint32_t quotient = OK(cc_instr_signature_close(k, sig));
    cc_constructor_info eq = constructor(quotient, 1);
    assert(eq.data == 3 && eq.positions == 0 && eq.dimensions == 1);
    assert(constructor(quotient, 2).generated && constructor(quotient, 2).dimensions == 2);

    /* A15: Cantor : set { leaf; node(f : Nat → s); }, infinitary. */
    cc_judgement_id nat = OK(cc_instr_nat(k));
    sig = OK(cc_instr_signature_begin(k, former_u0(), 2, S_CAN, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_CAN));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), CAN_LEAF));
    cc_entry_id f = OK(cc_instr_extend(k, OK(cc_instr_pi(k, OK(cc_instr_extend(k, nat, CAN_N)), var(s))), CAN_F));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, f, var(s))), CAN_NODE));
    uint32_t cantor = OK(cc_instr_signature_close(k, sig));
    assert(constructor(cantor, 1).positions == 1 && constructor(cantor, 2).generated);

    /* A16: base; loop : base = base; wrap(p : base = base);
     * fix : wrap(⟨i⟩ loop @ i) = base: a positional argument of path type
     * given as a path abstraction. */
    sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_WR, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_WR));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), WR_BASE));
    cc_entry_id base = OK(cc_instr_extend(k, var(s), WR_BASE));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, WR_LOOP));
    cc_entry_id loop = OK(cc_instr_extend(k, loop_type, WR_LOOP));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, OK(cc_instr_extend(k, loop_type, WR_P)), var(s)));
    sig = OK(cc_instr_signature_constructor(k, sig, wrap_type, WR_WRAP));
    cc_entry_id wrap = OK(cc_instr_extend(k, wrap_type, WR_WRAP));
    /* ⟨i⟩ loop @ i : Path(i; s, loop @ 0, loop @ 1), which the path steps
     * bring to loop's type. */
    cc_judgement_id line = OK(cc_instr_path_lambda(k, i, OK(cc_instr_path_apply(k, var(loop), i, 0))));
    cc_judgement_id ends = OK(cc_instr_path(k, i, var(s), OK(cc_instr_path_apply(k, var(loop), 0, 0)),
                                            OK(cc_instr_path_apply(k, var(loop), 0, 1))));
    cc_judgement_id to_loop = OK(cc_instr_refl(k, ends));
    to_loop = OK(cc_instr_step(k, to_loop, 1, (const uint8_t[]){1}, 1, CC_STEP_PATH));
    to_loop = OK(cc_instr_step(k, to_loop, 1, (const uint8_t[]){2}, 1, CC_STEP_PATH));
    line = OK(cc_instr_convert(k, line, to_loop));
    cc_judgement_id fix_type = OK(cc_instr_path(k, j, var(s), OK(cc_instr_apply(k, var(wrap), line)), var(base)));
    sig = OK(cc_instr_signature_constructor(k, sig, fix_type, WR_FIX));
    uint32_t wrapped = wrapped_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(wrapped, 2).positions == 1 && constructor(wrapped, 3).dimensions == 1);

    /* Branch(A : U0) { leaf; node(f : A → s); collapse(f : A → s) :
     * node(λ x. f x) = leaf; }: a λ as a positional argument. */
    cc_entry_id pa = OK(cc_instr_extend(k, former_u0(), BR_A));
    sig = OK(cc_instr_signature_begin(k, OK(cc_instr_pi(k, pa, former_u0())), CC_UNTRUNCATED, S_BR, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_BR));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), BR_LEAF));
    cc_entry_id leaf = OK(cc_instr_extend(k, var(s), BR_LEAF));
    cc_entry_id x = OK(cc_instr_extend(k, var(pa), BR_X));
    cc_entry_id g = OK(cc_instr_extend(k, OK(cc_instr_pi(k, x, var(s))), BR_F));
    cc_judgement_id node_type = OK(cc_instr_pi(k, g, var(s)));
    sig = OK(cc_instr_signature_constructor(k, sig, node_type, BR_NODE));
    cc_entry_id node_entry = OK(cc_instr_extend(k, node_type, BR_NODE));
    cc_judgement_id expanded = OK(cc_instr_lambda(k, x, OK(cc_instr_apply(k, var(g), var(x)))));
    cc_judgement_id collapse = OK(cc_instr_pi(k, g, OK(cc_instr_path(k, i, var(s),
        OK(cc_instr_apply(k, var(node_entry), expanded)), var(leaf)))));
    sig = OK(cc_instr_signature_constructor(k, sig, collapse, BR_COLLAPSE));
    uint32_t branch = branch_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(branch, 2).positions == 1 && constructor(branch, 2).dimensions == 1);

    /* V25: Tagged(x, y < ω, A : U(x)) : U(max(x, y + 1)) { tag(a : A, B : U(y)); },
     * x erased and y recorded. */
    cc_judgement_id tagged_top = universe(cc_kernel_term(k, CC_LMAX, 0, lvar(X), lsucc(lvar(Y)), 0, 0));
    cc_entry_id ta = OK(cc_instr_extend(k, ux, TAG_A));
    former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_level_pi(k, ye, OK(cc_instr_pi(k, ta, tagged_top))))));
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_TAG, 2));
    s = OK(cc_instr_extend(k, tagged_top, S_TAG));
    cc_entry_id tx = OK(cc_instr_extend(k, var(ta), TAG_X)), tb = OK(cc_instr_extend(k, uy, TAG_B));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, tx, OK(cc_instr_pi(k, tb, var(s))))), TAG));
    uint32_t tagged = tagged_signature = OK(cc_instr_signature_close(k, sig));
    assert(signature(tagged).recorded == 2 && constructor(tagged, 0).data == 2);
}

/* Section 1.4: the types a boundary carries are checked as the boundary is.
 * A path application's annotation, whose endpoints the path step exposes,
 * and a path abstraction's family may hide nothing. */
static void carried_types(void) {
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_HID, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_HID));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), HID_BASE));
    cc_entry_id base = OK(cc_instr_extend(k, var(s), HID_BASE));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, HID_LOOP));
    cc_entry_id loop = OK(cc_instr_extend(k, loop_type, HID_LOOP));
    /* loop, at Path(i; s, (λ (y : s). y)(base), base): loop @ 0 steps to the redex. */
    cc_entry_id y = OK(cc_instr_extend(k, var(s), HID_Y));
    cc_judgement_id redex = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, y, var(y))), var(base)));
    cc_judgement_id hidden_type = OK(cc_instr_path(k, i, var(s), redex, var(base)));
    cc_judgement_id unfolded = OK(cc_instr_step(k, OK(cc_instr_refl(k, hidden_type)), 1, (const uint8_t[]){1}, 1,
                                                CC_STEP_BETA));
    cc_judgement_id hidden = OK(cc_instr_convert(k, var(loop), OK(cc_instr_symmetry(k, unfolded))));
    cc_judgement_id at0 = OK(cc_instr_path_apply(k, hidden, 0, 0));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_path(k, j, var(s), at0, var(base))), HID_C),
            "constructor expression");
    /* ⟨j⟩ base, with base at (λ (T : U0). T)(s): its family is no cube. */
    cc_entry_id t = OK(cc_instr_extend(k, former_u0(), HID_T));
    cc_judgement_id ids = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, t, var(t))), var(s)));
    cc_judgement_id to_s = OK(cc_instr_step(k, OK(cc_instr_refl(k, ids)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id base_ids = OK(cc_instr_convert(k, var(base), OK(cc_instr_symmetry(k, to_s))));
    cc_judgement_id line = OK(cc_instr_path_lambda(k, j, base_ids));
    cc_judgement_id flatten = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_path(k, j, ids, base_ids, base_ids)))),
                                               1, (const uint8_t[]){0}, 1, CC_STEP_BETA));
    line = OK(cc_instr_convert(k, line, flatten));
    cc_judgement_id flat = OK(cc_instr_path(k, j, var(s), var(base), var(base)));
    cc_judgement_id constant = OK(cc_instr_path_lambda(k, j, var(base)));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_path(k, i, flat, line, constant)), HID_C),
            "not a cube over the sort");
    /* As written, loop @ 0 is admitted. */
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_path(k, j, var(s),
        OK(cc_instr_path_apply(k, var(loop), 0, 0)), var(base))), HID_C));
    OK(cc_instr_signature_close(k, sig));
}

/* Q10: each admission is a new sort, and the gate and a signature's state
 * are checked on every call: none is answered from the derivation cache. The
 * names a signature takes are reserved from the fresh-symbol supply. */
static void generative(void) {
    cc_judgement_id first = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_GEN, 0));
    cc_judgement_id second = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_GEN, 0));
    assert(first != second && term_of(first) != term_of(second));
    cc_kernel_set_extensions(k, 0);
    REJECTS(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_GEN, 0), "kernel extension under review");
    cc_kernel_set_extensions(k, CC_EXTENSION_H1);
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_GEN));
    cc_judgement_id next = OK(cc_instr_signature_constructor(k, first, var(s), GEN_C));
    REJECTS(cc_instr_signature_constructor(k, first, var(s), GEN_C), "latest");
    /* Rewriting would copy a signature judgement without its state. */
    REJECTS(cc_instr_step(k, first, 2, NULL, 0, CC_STEP_WHNF), "not rewritten");
    REJECTS(cc_instr_replace(k, first, 2, NULL, 0, OK(cc_instr_refl(k, former_u0()))), "not rewritten");
    OK(cc_instr_signature_close(k, next));
    REJECTS(cc_instr_signature_constructor(k, first, var(s), GEN_C), "already admitted");
    OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, second, var(s), GEN_C))));

    /* A prop signature whose sort and constructor symbols are the next the
     * supply would give: the squash's names avoid both. */
    uint32_t sort = cc_kernel_fresh_symbol(k) + 1, point = sort + 1;
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), 1, sort, 0));
    cc_entry_id own = OK(cc_instr_extend(k, former_u0(), sort));
    sig = OK(cc_instr_signature_constructor(k, sig, var(own), point));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    cc_constructor_info squash = constructor(index, 1);
    assert(squash.symbol != point && squash.symbol != sort && cc_kernel_fresh_symbol(k) > point);

    /* An instance's recorded levels compare by normal form, under binders
     * too: Sort(i; ; [x]) = Sort(i; ; [max(x, x)]), and
     * λ (x < ω). Sort(i; ; [x]) = λ (y < ω). Sort(i; ; [max(y, y)]). */
    cc_term by_x = cc_kernel_term(k, CC_LIST, 0, lvar(X), 0, 0, 0);
    cc_term by_max = cc_kernel_term(k, CC_LIST, 0, cc_kernel_term(k, CC_LMAX, 0, lvar(X), lvar(X), 0, 0), 0, 0, 0);
    cc_term sort_x = cc_kernel_term(k, CC_SORT, index, 0, by_x, 0, 0);
    cc_term sort_max = cc_kernel_term(k, CC_SORT, index, 0, by_max, 0, 0);
    assert(sort_x != sort_max && ck_alpha_equal(k, sort_x, sort_max));
    cc_term by_y = cc_kernel_term(k, CC_LIST, 0, cc_kernel_term(k, CC_LMAX, 0, lvar(Y), lvar(Y), 0, 0), 0, 0, 0);
    cc_term bound = cc_kernel_term(k, CC_LBOUND, 1, 0, 0, 0, 0);
    cc_term over_x = cc_kernel_term(k, CC_LLAM, X, bound, sort_x, 0, 0);
    cc_term over_y = cc_kernel_term(k, CC_LLAM, Y, bound, cc_kernel_term(k, CC_SORT, index, 0, by_y, 0, 0), 0, 0);
    assert(ck_alpha_equal(k, over_x, over_y));
    /* Another level, another signature, or a longer list differ. */
    cc_term by_other = cc_kernel_term(k, CC_LIST, 0, lvar(Y), 0, 0, 0);
    cc_term longer = cc_kernel_term(k, CC_LIST, 0, lvar(X), by_x, 0, 0);
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index, 0, by_other, 0, 0)));
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index - 1, 0, by_x, 0, 0)));
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index, 0, longer, 0, 0)));
    assert(!cc_kernel_error(k)[0]);
}

/* The other side of a reflexivity after one step at its root. */
static cc_term reduct(cc_judgement_id j, cc_step_rule rule) {
    return info(OK(cc_instr_step(k, OK(cc_instr_refl(k, j)), 1, NULL, 0, rule))).other;
}

/* F3: a constructor at an endpoint of one of its dimensions reduces to that
 * boundary of its type, by the path step, Whnf and Normalize, in whichever
 * order the faces are reached (sections 2.5, 3.2 and 5.4). */
static void boundaries(void) {
    cc_judgement_id nat = OK(cc_instr_nat(k)), zero = OK(cc_instr_zero(k));
    cc_judgement_id u0 = universe(lconst(0));
    /* loop @ 0 and loop @ 1 are base. */
    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_term base = term_of(OK(cc_instr_construct(k, s1, 0)));
    cc_judgement_id loop = OK(cc_instr_construct(k, s1, 1));
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at = OK(cc_instr_path_apply(k, loop, 0, e));
        assert(reduct(at, CC_STEP_PATH) == base && reduct(at, CC_STEP_WHNF) == base);
        assert(reduct(at, CC_STEP_NORMALIZE) == base);
    }

    /* Susp(x < ω, A : U(x)) { north; south; merid(a : A) : north = south; }:
     * merid(0) @ 1 is south. */
    cc_entry_id xe = OK(cc_instr_level(k, X));
    cc_judgement_id ux = universe(lvar(X));
    cc_entry_id sa = OK(cc_instr_extend(k, ux, SUSP_A));
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, sa, ux)))),
                                                      CC_UNTRUNCATED, S_SUSP, 0));
    cc_entry_id s = OK(cc_instr_extend(k, ux, S_SUSP));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), NORTH));
    cc_entry_id north = OK(cc_instr_extend(k, var(s), NORTH));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), SOUTH));
    cc_entry_id south = OK(cc_instr_extend(k, var(s), SOUTH));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_entry_id a = OK(cc_instr_extend(k, var(sa), SUSP_X));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, a, OK(cc_instr_path(k, i, var(s), var(north),
                                                                                          var(south))))), MERID));
    cc_judgement_id susp = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature = OK(cc_instr_signature_close(k, sig)))),
                                                      nat));
    cc_judgement_id merid0 = OK(cc_instr_apply(k, OK(cc_instr_construct(k, susp, 2)), zero));
    cc_term south_term = term_of(OK(cc_instr_construct(k, susp, 1)));
    cc_judgement_id at1 = OK(cc_instr_path_apply(k, merid0, 0, 1));
    assert(reduct(at1, CC_STEP_PATH) == south_term && reduct(at1, CC_STEP_WHNF) == south_term);

    /* Push(x < ω, C A B : U(x), f : C → A, g : C → B) { inl(a : A); inr(b : B);
     * push(c : C) : inl(f(c)) = inr(g(c)); } at Nat, Nat, Nat, λ n. n and
     * succ: push(0) @ 0 is inl((λ n. n)(0)), which normalizes to inl(0), and
     * push(0) @ 1 normalizes to inr(1). */
    cc_entry_id pc = OK(cc_instr_extend(k, ux, PUSH_C)), pa = OK(cc_instr_extend(k, ux, PUSH_A));
    cc_entry_id pb = OK(cc_instr_extend(k, ux, PUSH_B));
    cc_entry_id arg = OK(cc_instr_extend(k, var(pc), PUSH_ARG));
    cc_entry_id pf = OK(cc_instr_extend(k, OK(cc_instr_pi(k, arg, var(pa))), PUSH_F));
    cc_entry_id pg = OK(cc_instr_extend(k, OK(cc_instr_pi(k, arg, var(pb))), PUSH_G));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, pc, OK(cc_instr_pi(k, pa,
        OK(cc_instr_pi(k, pb, OK(cc_instr_pi(k, pf, OK(cc_instr_pi(k, pg, ux))))))))))));
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_PUSH, 0));
    s = OK(cc_instr_extend(k, ux, S_PUSH));
    cc_entry_id left = OK(cc_instr_extend(k, var(pa), PUSH_X)), right = OK(cc_instr_extend(k, var(pb), PUSH_Y));
    cc_judgement_id inl_type = OK(cc_instr_pi(k, left, var(s))), inr_type = OK(cc_instr_pi(k, right, var(s)));
    sig = OK(cc_instr_signature_constructor(k, sig, inl_type, INL));
    cc_entry_id inl = OK(cc_instr_extend(k, inl_type, INL));
    sig = OK(cc_instr_signature_constructor(k, sig, inr_type, INR));
    cc_entry_id inr = OK(cc_instr_extend(k, inr_type, INR));
    cc_entry_id c = OK(cc_instr_extend(k, var(pc), PUSH_Z));
    cc_judgement_id glued = OK(cc_instr_path(k, i, var(s), OK(cc_instr_apply(k, var(inl), OK(cc_instr_apply(k, var(pf), var(c))))),
                                             OK(cc_instr_apply(k, var(inr), OK(cc_instr_apply(k, var(pg), var(c)))))));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, c, glued)), PUSH));
    uint32_t push_signature = OK(cc_instr_signature_close(k, sig));
    cc_entry_id n = OK(cc_instr_extend(k, nat, PUSH_N));
    cc_judgement_id push = OK(cc_instr_sort_begin(k, push_signature));
    const cc_judgement_id parameters[] = {nat, nat, nat, OK(cc_instr_lambda(k, n, var(n))),
                                          OK(cc_instr_lambda(k, n, OK(cc_instr_succ(k, var(n)))))};
    for (unsigned p = 0; p < 5; ++p)
        push = OK(cc_instr_sort_parameter(k, push, parameters[p]));
    assert(type_of(push) == term_of(u0));
    cc_judgement_id push0 = OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 2)), zero));
    cc_term inl0 = term_of(OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 0)), zero)));
    cc_term inr1 = term_of(OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 1)), OK(cc_instr_succ(k, zero)))));
    assert(reduct(OK(cc_instr_path_apply(k, push0, 0, 0)), CC_STEP_NORMALIZE) == inl0);
    assert(reduct(OK(cc_instr_path_apply(k, push0, 0, 1)), CC_STEP_NORMALIZE) == inr1);
    cc_term head = reduct(OK(cc_instr_path_apply(k, push0, 0, 0)), CC_STEP_WHNF);
    assert(kind(head) == CC_APP && child(head, 0) == term_of(OK(cc_instr_construct(k, push, 0))));

    /* The torus's four corners are its point, reached through the square's
     * outer endpoint first, as the whole application's step, or through its
     * inner one, as a step inside it. */
    cc_judgement_id torus = OK(cc_instr_sort_begin(k, torus_signature));
    cc_term point = term_of(OK(cc_instr_construct(k, torus, 0)));
    cc_judgement_id surf = OK(cc_instr_construct(k, torus, 3));
    for (unsigned e1 = 0; e1 < 2; ++e1)
        for (unsigned e2 = 0; e2 < 2; ++e2) {
            cc_judgement_id corner = OK(cc_instr_path_apply(k, OK(cc_instr_path_apply(k, surf, 0, e1)), 0, e2));
            assert(reduct(corner, CC_STEP_WHNF) == point && reduct(corner, CC_STEP_NORMALIZE) == point);
            /* Outer first: the corner, then p @ e1, then the point. Inner
             * first: surf @ e1 is q, and q @ e2 steps through the outer
             * annotation to p @ e1, then to the point. */
            cc_judgement_id outer = OK(cc_instr_refl(k, corner));
            for (unsigned step = 0; step < 2; ++step)
                outer = OK(cc_instr_step(k, outer, 1, NULL, 0, CC_STEP_PATH));
            cc_judgement_id inner = OK(cc_instr_step(k, OK(cc_instr_refl(k, corner)), 1, (const uint8_t[]){0}, 1,
                                                     CC_STEP_PATH));
            assert(kind(child(info(inner).other, 0)) == CC_CON && payload(child(info(inner).other, 0)) == 2);
            for (unsigned step = 0; step < 2; ++step)
                inner = OK(cc_instr_step(k, inner, 1, NULL, 0, CC_STEP_PATH));
            assert(info(outer).other == point && info(inner).other == point);
        }

    /* The open square (surf @ i) @ j, restricted in either order: restricting
     * i reaches into the outer application's annotation, the type of
     * surf @ i. Its faces are q @ j at i = 0 and 1 and p @ i at j = 0 and 1,
     * with no trace of the restricted dimension, and its corners the point. */
    cc_term p_term = term_of(OK(cc_instr_construct(k, torus, 1))), q_term = term_of(OK(cc_instr_construct(k, torus, 2)));
    cc_judgement_id square = OK(cc_instr_path_apply(k, OK(cc_instr_path_apply(k, surf, i, 0)), j, 0));
    uint32_t along_i = payload(child(term_of(square), 0)), along_j = payload(term_of(square));
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at_i = OK(cc_instr_endpoint(k, square, i, e)), at_j = OK(cc_instr_endpoint(k, square, j, e));
        cc_term face_i = reduct(at_i, CC_STEP_WHNF), face_j = reduct(at_j, CC_STEP_WHNF);
        assert(kind(face_i) == CC_PAPP && child(face_i, 0) == q_term && payload(face_i) == along_j);
        assert(kind(face_j) == CC_PAPP && child(face_j, 0) == p_term && payload(face_j) == along_i);
        assert(ck_free_dims(k, term_of(at_i)) == 2 && ck_free_dims(k, face_i) == 2);
        assert(ck_free_dims(k, term_of(at_j)) == 1 && ck_free_dims(k, face_j) == 1);
    }
    for (unsigned e1 = 0; e1 < 2; ++e1)
        for (unsigned e2 = 0; e2 < 2; ++e2) {
            cc_judgement_id i_first = OK(cc_instr_endpoint(k, OK(cc_instr_endpoint(k, square, i, e1)), j, e2));
            cc_judgement_id j_first = OK(cc_instr_endpoint(k, OK(cc_instr_endpoint(k, square, j, e2)), i, e1));
            assert(term_of(i_first) == term_of(j_first) && !ck_free_dims(k, term_of(i_first)));
            assert(reduct(i_first, CC_STEP_WHNF) == point && reduct(j_first, CC_STEP_NORMALIZE) == point);
            cc_judgement_id stepped = OK(cc_instr_refl(k, i_first));
            for (unsigned step = 0; step < 2; ++step)
                stepped = OK(cc_instr_step(k, stepped, 1, NULL, 0, CC_STEP_PATH));
            assert(info(stepped).other == point);
        }

    /* Replace keeps an annotation a path type: loop @ 0 with its annotation
     * P replaced by (λ (X : U0). X)(P) would no longer reduce. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, s1, OK(cc_instr_construct(k, s1, 0)),
                                                 OK(cc_instr_construct(k, s1, 0))));
    cc_entry_id xt = OK(cc_instr_extend(k, u0, PUSH_N + 1));
    cc_judgement_id wrapped = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, xt, var(xt))), loop_type));
    cc_judgement_id unwrap = OK(cc_instr_step(k, OK(cc_instr_refl(k, wrapped)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id at0 = OK(cc_instr_path_apply(k, loop, 0, 0));
    REJECTS(cc_instr_replace(k, at0, 0, (const uint8_t[]){1}, 1, OK(cc_instr_symmetry(k, unwrap))),
            "annotation is replaced only by a path type");
    /* Inside the annotation, and by another path type, rewriting is allowed. */
    cc_judgement_id same_type = OK(cc_instr_replace(k, at0, 0, (const uint8_t[]){1}, 1, OK(cc_instr_refl(k, loop_type))));
    assert(reduct(same_type, CC_STEP_WHNF) == base);

    /* loop @ (i ∧ j), restricted to j = 0, is loop @ 0, and so base. */
    cc_formula meet, left_i, right_j;
    cc_init(&meet, CC_INTERVAL); cc_init(&left_i, CC_INTERVAL); cc_init(&right_j, CC_INTERVAL);
    assert(cc_generator(&left_i, 0, true) == CC_OK && cc_generator(&right_j, 1, true) == CC_OK &&
           cc_meet(&meet, &left_i, &right_j) == CC_OK);
    cc_formula_id both = cc_kernel_formula(k, &meet);
    cc_clear(&meet); cc_clear(&left_i); cc_clear(&right_j);
    cc_judgement_id diagonal = OK(cc_instr_path_at(k, loop, both));
    cc_judgement_id restricted = OK(cc_instr_endpoint(k, diagonal, j, 0));
    assert(reduct(restricted, CC_STEP_PATH) == base && reduct(restricted, CC_STEP_WHNF) == base);
    (void)i;
}

static cc_formula_id face_at(unsigned dim, bool one) {
    cc_formula f;
    cc_init(&f, CC_FACE);
    assert(cc_generator(&f, dim, one) == CC_OK);
    cc_formula_id id = cc_kernel_formula(k, &f);
    cc_clear(&f);
    return id;
}

static cc_formula_id nowhere(void) {
    cc_formula f;
    cc_init(&f, CC_FACE);
    cc_formula_id id = cc_kernel_formula(k, &f);
    cc_clear(&f);
    return id;
}

/* The number of tubes of a composition node. */
static unsigned tubes(cc_term composition) {
    unsigned count = 0;
    for (cc_term cursor = child(composition, 1); cursor; cursor = child(cursor, 1)) ++count;
    return count;
}

/* Transport commutes with restriction to a face of a constructor's
 * dimensions (3.5): restricting the transport, or the hcomp it reduces to,
 * normalizes to the same term. */
static cc_term commutes(cc_judgement_id transported, cc_entry_id dim, unsigned e) {
    cc_judgement_id reduced = OK(cc_instr_step(k, OK(cc_instr_refl(k, transported)), 1, NULL, 0, CC_STEP_WHNF));
    cc_judgement_id as_hcomp = OK(cc_instr_side(k, reduced, 1));
    assert(kind(term_of(as_hcomp)) == CC_HCOMP);
    cc_term direct = reduct(OK(cc_instr_endpoint(k, transported, dim, e)), CC_STEP_NORMALIZE);
    cc_term through = reduct(OK(cc_instr_endpoint(k, as_hcomp, dim, e)), CC_STEP_NORMALIZE);
    assert(ck_alpha_equal(k, direct, through));
    return direct;
}

/* A normal form outside any instruction. */
static cc_term normal(cc_term t) {
    ck_standalone(k);
    cc_term result = ck_normal(k, t);
    assert(result);
    return result;
}

/* Each correction wall of a transport's hcomp starts, at h = 0, on the
 * hcomp's base: on its face r = ε, the wall at 0 and the base restricted
 * there normalize alike. The wall on φ, the empty face here, is skipped. */
static void walls_start_on_base(cc_term box) {
    unsigned h = payload(box);
    cc_term base = child(box, 2);
    unsigned checked = 0;
    for (cc_term cursor = child(box, 1); cursor; cursor = child(cursor, 1)) {
        const cc_formula *face = cc_kernel_get_formula(k, payload(cursor));
        if (!face->length)
            continue;
        assert(face->length == 1);
        cc_clause clause = face->clauses[0];
        assert(!(clause.positive & clause.negative) && __builtin_popcountll(clause.positive | clause.negative) == 1);
        unsigned dim = (unsigned)__builtin_ctzll(clause.positive | clause.negative), end = clause.positive ? 1 : 0;
        ck_standalone(k);
        cc_term wall = ck_endpoint_term(k, ck_endpoint_term(k, child(cursor, 0), h, 0), dim, end);
        cc_term restricted = ck_endpoint_term(k, base, dim, end);
        assert(ck_alpha_equal(k, normal(wall), normal(restricted)));
        ++checked;
    }
    assert(checked);
}

/* The argument a constructor application's i-th, under its path applications. */
static cc_term constructor_argument(cc_term t, uint32_t index, uint32_t count) {
    while (kind(t) == CC_PAPP)
        t = child(t, 0);
    for (uint32_t m = count; m-- > index + 1;)
        t = child(t, 0);
    return child(t, 1);
}

/* The squash of a truncated signature at an instance, applied to variables
 * y_s, z_s : B_s, B_{s+1} = Path(B_s, y_s, z_s), and then at the dimensions. */
static cc_judgement_id squash_at(cc_judgement_id instance, uint32_t steps, uint32_t symbols,
                                 const cc_entry_id *dimensions) {
    cc_judgement_id b = instance, applied = OK(cc_instr_construct(k, instance, 1));
    for (uint32_t s = 0; s < steps; ++s) {
        cc_entry_id y = OK(cc_instr_extend(k, b, symbols + 2 * s)), z = OK(cc_instr_extend(k, b, symbols + 2 * s + 1));
        applied = OK(cc_instr_apply(k, OK(cc_instr_apply(k, applied, var(y))), var(z)));
        b = OK(cc_instr_path(k, OK(cc_instr_dimension(k, 5 + s)), b, var(y), var(z)));
    }
    for (uint32_t s = 0; s < steps; ++s)
        applied = OK(cc_instr_path_apply(k, applied, dimensions[s], 0));
    return applied;
}

/* F4: the Kan structure of declared types (sections 3.3–3.5, 5.5). */
static void kan(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_entry_id dims[3] = {OK(cc_instr_dimension(k, 1)), OK(cc_instr_dimension(k, 2)), OK(cc_instr_dimension(k, 3))};
    cc_entry_id j = dims[0];

    /* K3: a data sort has no formal composition; comp^i N [] succ(zero)
     * composes succ's argument, and normalizes to succ(zero). */
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    cc_judgement_id one = OK(cc_instr_apply(k, OK(cc_instr_construct(k, n, 1)), OK(cc_instr_construct(k, n, 0))));
    cc_judgement_id at_one = OK(cc_instr_system(k, i, n, one));
    REJECTS(cc_instr_hcomp(k, at_one), "data sort has no formal");
    REJECTS(cc_instr_trans(k, at_one, nowhere()), "data sort has no formal");
    cc_judgement_id composed = OK(cc_instr_comp(k, at_one));
    cc_term head = reduct(composed, CC_STEP_WHNF);
    assert(kind(head) == CC_APP && kind(child(head, 0)) == CC_CON && payload(child(head, 0)) == 1);
    assert(ck_alpha_equal(k, reduct(composed, CC_STEP_NORMALIZE), term_of(one)));
    /* A neutral tube keeps it neutral: q @ i on j = 0, for q : succ(zero) = m. */
    cc_entry_id m = OK(cc_instr_extend(k, n, KAN_M));
    cc_entry_id q = OK(cc_instr_extend(k, OK(cc_instr_path(k, i, n, one, var(m))), KAN_Q));
    cc_judgement_id q_i = OK(cc_instr_path_apply(k, var(q), i, 0));
    cc_judgement_id starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, q_i, i, 0)))), 1, NULL, 0,
                                             CC_STEP_PATH));
    cc_judgement_id stuck = OK(cc_instr_comp(k, OK(cc_instr_system_tube(k, at_one, face_at(1, false), q_i, starts))));
    assert(kind(reduct(stuck, CC_STEP_WHNF)) == CC_COMP);

    /* A line of types e : A = B, and Susp(e @ i) along it. */
    cc_judgement_id u0 = universe(lconst(0));
    cc_entry_id ta = OK(cc_instr_extend(k, u0, KAN_A)), tb = OK(cc_instr_extend(k, u0, KAN_B));
    cc_entry_id e = OK(cc_instr_extend(k, OK(cc_instr_path(k, i, u0, var(ta), var(tb))), KAN_E));
    cc_judgement_id e_i = OK(cc_instr_path_apply(k, var(e), i, 0));
    cc_judgement_id e_0 = OK(cc_instr_path_apply(k, var(e), 0, 0)), e_1 = OK(cc_instr_path_apply(k, var(e), 0, 1));
    cc_judgement_id line = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_i));
    cc_judgement_id start = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_0));
    cc_judgement_id end = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_1));
    cc_judgement_id north = OK(cc_instr_construct(k, start, 0));
    /* North and south at the line's end, normalized: e @ 1 is B. */
    cc_term north_end = reduct(OK(cc_instr_construct(k, end, 0)), CC_STEP_NORMALIZE);
    cc_term south_end = reduct(OK(cc_instr_construct(k, end, 1)), CC_STEP_NORMALIZE);
    /* A higher sort composes formally, and comp reduces to hcomp. */
    cc_judgement_id formal = OK(cc_instr_hcomp(k, OK(cc_instr_system(k, j, start, north))));
    assert(kind(term_of(formal)) == CC_HCOMP && reduct(formal, CC_STEP_WHNF) == term_of(formal));
    assert(kind(reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, line, north)))), CC_STEP_WHNF)) == CC_HCOMP);
    /* K8: transport commutes with an hcomp (3.5, case 3): hcomp^j [] north,
     * moved along the line, is an hcomp at its end, of north moved. */
    cc_term moved_box = reduct(OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, formal)), nowhere())), CC_STEP_WHNF);
    assert(kind(moved_box) == CC_HCOMP && ck_alpha_equal(k, normal(child(moved_box, 2)), north_end));
    /* Face, unchanged: an hcomp with a tube on the face 1 is that tube at 1,
     * and a transport on a face that holds is its base. */
    cc_formula top;
    cc_init(&top, CC_FACE);
    assert(cc_one(&top) == CC_OK);
    cc_formula_id always = cc_kernel_formula(k, &top);
    cc_clear(&top);
    cc_judgement_id stay = OK(cc_instr_refl(k, north));
    cc_judgement_id held = OK(cc_instr_hcomp(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, j, start, north)),
                                                                        always, north, stay))));
    assert(reduct(held, CC_STEP_FACE) == term_of(north));
    cc_judgement_id still = OK(cc_instr_trans(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, start, north)),
                                                                         always, north, stay)), always));
    assert(reduct(still, CC_STEP_FACE) == term_of(north) && reduct(still, CC_STEP_WHNF) == term_of(north));
    /* Transport of a point constructor: north at the line's end. */
    cc_judgement_id moved = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, north)), nowhere()));
    assert(ck_alpha_equal(k, reduct(moved, CC_STEP_NORMALIZE), north_end));
    assert(ck_alpha_equal(k, reduct(moved, CC_STEP_WHNF), term_of(OK(cc_instr_construct(k, end, 0)))));
    /* merid(a) @ j along the line: an hcomp corrected on j = 0 and j = 1, whose
     * faces are the transports of north and south. */
    cc_entry_id a = OK(cc_instr_extend(k, var(ta), KAN_X));
    cc_judgement_id to_a = OK(cc_instr_step(k, OK(cc_instr_refl(k, e_0)), 1, NULL, 0, CC_STEP_PATH));
    cc_judgement_id a0 = OK(cc_instr_convert(k, var(a), OK(cc_instr_symmetry(k, to_a))));
    cc_judgement_id merid = OK(cc_instr_path_apply(k, OK(cc_instr_apply(k, OK(cc_instr_construct(k, start, 2)), a0)), j, 0));
    cc_judgement_id transported = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, merid)), nowhere()));
    cc_term corrected = reduct(transported, CC_STEP_WHNF);
    assert(kind(corrected) == CC_HCOMP && tubes(corrected) == 3);
    cc_term base = child(corrected, 2);
    assert(kind(base) == CC_PAPP && kind(child(base, 0)) == CC_APP && payload(child(child(base, 0), 0)) == 2);
    /* Its argument is a moved along e @ i, derived independently, and each
     * wall starts on the base. */
    cc_term moved_a = reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, e_i, a0)))), CC_STEP_NORMALIZE);
    assert(ck_alpha_equal(k, normal(constructor_argument(base, 0, 1)), moved_a));
    walls_start_on_base(corrected);
    assert(ck_alpha_equal(k, commutes(transported, j, 0), north_end));
    assert(ck_alpha_equal(k, commutes(transported, j, 1), south_end));

    /* The squash of set (two dimensions) and of trunc(1) (three), along the
     * line: 2d walls, and each face commutes with transport. */
    const uint32_t truncated[2] = {set_signature, groupoid_signature};
    for (uint32_t t = 0; t < 2; ++t) {
        uint32_t steps = t + 2;
        cc_judgement_id from = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, truncated[t])), e_0));
        cc_judgement_id along = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, truncated[t])), e_i));
        cc_judgement_id squash = squash_at(from, steps, KAN_Y + 10 * t, dims);
        cc_judgement_id carried = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, along, squash)), nowhere()));
        cc_term box = reduct(carried, CC_STEP_WHNF);
        assert(kind(box) == CC_HCOMP && tubes(box) == 2 * steps + 1);
        walls_start_on_base(box);
        /* The first argument, y_0, is moved along the line. */
        cc_judgement_id y0 = var(OK(cc_instr_extend(k, from, KAN_Y + 10 * t)));
        cc_term moved_y0 = reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, along, y0)))), CC_STEP_NORMALIZE);
        assert(ck_alpha_equal(k, normal(constructor_argument(child(box, 2), 0, 2 * steps)), moved_y0));
        for (uint32_t l = 0; l < steps; ++l)
            for (unsigned end_point = 0; end_point < 2; ++end_point)
                commutes(carried, dims[l], end_point);
    }
}

/* A motive P : Π (z : I). U0, as a variable. */
static cc_entry_id motive_over(cc_judgement_id instance, uint32_t symbol) {
    cc_entry_id z = OK(cc_instr_extend(k, instance, symbol + 1));
    return OK(cc_instr_extend(k, OK(cc_instr_pi(k, z, universe(lconst(0)))), symbol));
}

/* P(t), the motive applied, as a type. */
static cc_judgement_id at(cc_entry_id motive, cc_judgement_id t) { return OK(cc_instr_apply(k, var(motive), t)); }

/* PathP(i. P(loop @ i), point, point) for a loop : Path(i; I, b, b), with
 * point : P(b) moved to P(loop @ ε) at each end by the path step. */
static cc_judgement_id path_over(cc_entry_id motive, cc_judgement_id loop, cc_entry_id i, cc_judgement_id point) {
    cc_judgement_id ends[2];
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at_end = at(motive, OK(cc_instr_path_apply(k, loop, 0, e)));
        cc_judgement_id to_point = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_end)), 1, (const uint8_t[]){1}, 1,
                                                    CC_STEP_PATH));
        ends[e] = OK(cc_instr_convert(k, point, OK(cc_instr_symmetry(k, to_point))));
    }
    return OK(cc_instr_path(k, i, at(motive, OK(cc_instr_path_apply(k, loop, i, 0))), ends[0], ends[1]));
}

static cc_term iota_of(cc_judgement_id j) { return reduct(j, CC_STEP_IOTA); }

/* F5: elimination (sections 3.6, 3.7, 5.6). */
static void elimination(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id nat = OK(cc_instr_nat(k));

    /* N: P(zero), then Π (n : N). Π (n̄ : P(n)). P(succ(n)). */
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    cc_judgement_id zero = OK(cc_instr_construct(k, n, 0)), succ = OK(cc_instr_construct(k, n, 1));
    cc_entry_id p = motive_over(n, ELIM_P);
    cc_judgement_id opened = OK(cc_instr_eliminator(k, var(p)));
    assert(info(opened).kind == 6 && type_of(opened) == term_of(at(p, zero)) && !info(opened).other);
    REJECTS(cc_instr_eliminator_close(k, opened), "lacks a clause");
    /* E6: a clause of the wrong type. */
    REJECTS(cc_instr_eliminator_clause(k, opened, OK(cc_instr_zero(k))), "clause type");
    cc_entry_id pz = OK(cc_instr_extend(k, at(p, zero), ELIM_PZ));
    cc_judgement_id after_zero = OK(cc_instr_eliminator_clause(k, opened, var(pz)));
    cc_entry_id m = OK(cc_instr_extend(k, n, ELIM_N)), h = OK(cc_instr_extend(k, at(p, var(m)), ELIM_H));
    cc_judgement_id step_type = OK(cc_instr_pi(k, m, OK(cc_instr_pi(k, h, at(p, OK(cc_instr_apply(k, succ, var(m))))))));
    assert(ck_alpha_equal(k, term_of(step_type), type_of(after_zero)));
    cc_entry_id ps = OK(cc_instr_extend(k, step_type, ELIM_PS));
    cc_judgement_id full = OK(cc_instr_eliminator_clause(k, after_zero, var(ps)));
    REJECTS(cc_instr_eliminator_clause(k, full, var(ps)), "every constructor");
    cc_judgement_id elim = OK(cc_instr_eliminator_close(k, full));
    assert(kind(term_of(elim)) == CC_ELIM && kind(type_of(elim)) == CC_PI && child(type_of(elim), 0) == term_of(n));
    /* Iota: elim(zero) is pz, and elim(succ(zero)) is ps(zero, elim(zero)). */
    cc_judgement_id on_zero = OK(cc_instr_apply(k, elim, zero));
    assert(iota_of(on_zero) == term_of(var(pz)) && reduct(on_zero, CC_STEP_WHNF) == term_of(var(pz)));
    cc_term on_one = iota_of(OK(cc_instr_apply(k, elim, OK(cc_instr_apply(k, succ, zero)))));
    assert(child(on_one, 0) == term_of(OK(cc_instr_apply(k, var(ps), zero))) && child(on_one, 1) == term_of(on_zero));
    REJECTS(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_apply(k, elim, var(m))))), 1, NULL, 0, CC_STEP_IOTA),
            "Iota needs");
    /* A motive over no declared type is refused. */
    cc_entry_id z = OK(cc_instr_extend(k, nat, ELIM_Z));
    REJECTS(cc_instr_eliminator(k, OK(cc_instr_lambda(k, z, nat))), "instance of a declared type");

    /* The circle: loop's clause is PathP(i. P(loop @ i), pb, pb); E7: one
     * whose ends are not the base clause is refused. */
    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_judgement_id base = OK(cc_instr_construct(k, s1, 0)), loop = OK(cc_instr_construct(k, s1, 1));
    cc_entry_id q = motive_over(s1, ELIM_Q);
    cc_entry_id pb = OK(cc_instr_extend(k, at(q, base), ELIM_PB)), other = OK(cc_instr_extend(k, at(q, base), ELIM_PB2));
    cc_judgement_id circle = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(q))), var(pb)));
    cc_judgement_id loop_type = path_over(q, loop, i, var(pb));
    assert(term_of(loop_type) == type_of(circle));
    REJECTS(cc_instr_eliminator_clause(k, circle, var(OK(cc_instr_extend(k, path_over(q, loop, i, var(other)), ELIM_PL2)))),
            "clause type");
    cc_entry_id pl = OK(cc_instr_extend(k, loop_type, ELIM_PL));
    cc_judgement_id circle_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, circle, var(pl)))));
    /* elim(loop @ j) is pl @ j; at loop @ 0 both orders give pb (3.7). */
    cc_term on_loop = iota_of(OK(cc_instr_apply(k, circle_elim, OK(cc_instr_path_apply(k, loop, j, 0)))));
    assert(kind(on_loop) == CC_PAPP && child(on_loop, 0) == term_of(var(pl)) && kind(child(on_loop, 1)) == CC_PATH);
    cc_judgement_id at_zero = OK(cc_instr_apply(k, circle_elim, OK(cc_instr_path_apply(k, loop, 0, 0))));
    assert(reduct(at_zero, CC_STEP_WHNF) == term_of(var(pb)));
    cc_judgement_id by_iota = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_zero)), 1, NULL, 0, CC_STEP_IOTA));
    assert(info(OK(cc_instr_step(k, by_iota, 1, NULL, 0, CC_STEP_PATH))).other == term_of(var(pb)));
    /* elim(hcomp) computes by Whnf, as a composition in the motive. */
    cc_judgement_id box = OK(cc_instr_hcomp(k, OK(cc_instr_system(k, j, s1, base))));
    assert(kind(reduct(OK(cc_instr_apply(k, circle_elim, box)), CC_STEP_WHNF)) == CC_COMP);

    /* The prop squash: Π (y z : T). Π (ȳ : P(y)) (z̄ : P(z)). PathP(i. …, ȳ, z̄):
     * its boundary shows the positions y, z by their displayed variables. */
    cc_judgement_id tr = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), nat));
    cc_entry_id t = motive_over(tr, ELIM_T);
    cc_entry_id a = OK(cc_instr_extend(k, nat, ELIM_A));
    cc_judgement_id point_at = OK(cc_instr_apply(k, OK(cc_instr_construct(k, tr, 0)), var(a)));
    cc_entry_id pp = OK(cc_instr_extend(k, OK(cc_instr_pi(k, a, at(t, point_at))), ELIM_PP));
    cc_term squash = type_of(OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(t))), var(pp))));
    cc_term y_bar = child(child(squash, 1), 1), z_bar = child(y_bar, 1), inner = child(z_bar, 1);
    assert(kind(inner) == CC_PATH && payload(child(inner, 1)) == payload(y_bar) && payload(child(inner, 2)) == payload(z_bar));
    assert(kind(child(y_bar, 0)) == CC_APP && payload(child(child(y_bar, 0), 1)) == payload(squash));
    /* E9: Trunc(Nat)'s eliminator, with both clauses, is over its own
     * instance: a term of Trunc(Unit) is refused. The squash clause is
     * derived here as the kernel reports it. */
    cc_entry_id ty = OK(cc_instr_extend(k, tr, E9_Y)), tz = OK(cc_instr_extend(k, tr, E9_Z));
    const cc_entry_id bars[2] = {OK(cc_instr_extend(k, at(t, var(ty)), E9_YB)), OK(cc_instr_extend(k, at(t, var(tz)), E9_ZB))};
    cc_judgement_id sq = OK(cc_instr_apply(k, OK(cc_instr_apply(k, OK(cc_instr_construct(k, tr, 1)), var(ty))), var(tz)));
    cc_judgement_id ends[2];
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at_end = at(t, OK(cc_instr_path_apply(k, sq, 0, e)));
        cc_judgement_id to_bar = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_end)), 1, (const uint8_t[]){1}, 1, CC_STEP_PATH));
        ends[e] = OK(cc_instr_convert(k, var(bars[e]), OK(cc_instr_symmetry(k, to_bar))));
    }
    cc_judgement_id squash_type = OK(cc_instr_pi(k, ty, OK(cc_instr_pi(k, tz, OK(cc_instr_pi(k, bars[0], OK(cc_instr_pi(k, bars[1],
        OK(cc_instr_path(k, i, at(t, OK(cc_instr_path_apply(k, sq, i, 0))), ends[0], ends[1]))))))))));
    cc_judgement_id tr_open = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(t))), var(pp)));
    assert(ck_alpha_equal(k, type_of(tr_open), term_of(squash_type)));
    cc_judgement_id tr_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, tr_open,
        var(OK(cc_instr_extend(k, squash_type, E9_SQ)))))));
    OK(cc_instr_apply(k, tr_elim, point_at));
    cc_judgement_id unit_tr = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), OK(cc_instr_unit(k))));
    REJECTS(cc_instr_apply(k, tr_elim, OK(cc_instr_apply(k, OK(cc_instr_construct(k, unit_tr, 0)), OK(cc_instr_point(k))))),
            "wrong type");
    /* E10: a motive into UU0 for the circle, P : Π (z : S1). U(ω), with its
     * two clauses. */
    cc_entry_id wide = OK(cc_instr_extend(k, OK(cc_instr_pi(k, OK(cc_instr_extend(k, s1, E10_Z)), universe(tier1(0)))), E10_P));
    cc_entry_id wide_base = OK(cc_instr_extend(k, at(wide, base), E10_PB));
    cc_entry_id wide_loop = OK(cc_instr_extend(k, path_over(wide, loop, i, var(wide_base)), E10_PL));
    cc_judgement_id wide_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(wide))), var(wide_base))), var(wide_loop)))));
    assert(kind(type_of(wide_elim)) == CC_PI);

    /* Tree(Nat, λ n. Nat): sup's position has an arity, so q̄ is λ b. elim(c(b)). */
    cc_entry_id nb = OK(cc_instr_extend(k, nat, ELIM_B));
    cc_judgement_id family = OK(cc_instr_lambda(k, nb, nat));
    cc_judgement_id tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k,
        OK(cc_instr_sort_begin(k, tree_signature)), nat)), family));
    cc_entry_id w = motive_over(tree, ELIM_W);
    cc_entry_id l = OK(cc_instr_extend(k, nat, ELIM_L));
    cc_entry_id b = OK(cc_instr_extend(k, OK(cc_instr_apply(k, family, var(l))), ELIM_BB));
    cc_entry_id c = OK(cc_instr_extend(k, OK(cc_instr_pi(k, b, tree)), ELIM_C));
    cc_entry_id c_bar = OK(cc_instr_extend(k, OK(cc_instr_pi(k, b, at(w, OK(cc_instr_apply(k, var(c), var(b)))))), ELIM_CBAR));
    cc_judgement_id sup = OK(cc_instr_construct(k, tree, 0));
    cc_judgement_id sup_type = OK(cc_instr_pi(k, l, OK(cc_instr_pi(k, c, OK(cc_instr_pi(k, c_bar,
        at(w, OK(cc_instr_apply(k, OK(cc_instr_apply(k, sup, var(l))), var(c))))))))));
    cc_judgement_id tree_open = OK(cc_instr_eliminator(k, var(w)));
    assert(ck_alpha_equal(k, type_of(tree_open), term_of(sup_type)));
    cc_entry_id ms = OK(cc_instr_extend(k, sup_type, ELIM_MS));
    cc_judgement_id tree_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, tree_open, var(ms)))));
    cc_term on_sup = iota_of(OK(cc_instr_apply(k, tree_elim, OK(cc_instr_apply(k, OK(cc_instr_apply(k, sup, var(l))),
                                                                                  var(c))))));
    cc_term lifted = child(on_sup, 1);
    assert(kind(lifted) == CC_LAM && kind(child(lifted, 1)) == CC_APP && child(child(lifted, 1), 0) == term_of(tree_elim));
    assert(child(child(child(lifted, 1), 1), 0) == term_of(var(c)));

    /* A16: wrap's position is a path, displayed as a PathP between base's
     * clause; fix's boundary wrap(⟨i⟩ loop @ i) is shown as
     * m_wrap(⟨i⟩ loop @ i, ⟨i⟩ m_loop @ i). */
    cc_judgement_id wr = OK(cc_instr_sort_begin(k, wrapped_signature));
    cc_judgement_id wbase = OK(cc_instr_construct(k, wr, 0)), wloop = OK(cc_instr_construct(k, wr, 1));
    cc_entry_id v = motive_over(wr, ELIM_V);
    cc_entry_id pv = OK(cc_instr_extend(k, at(v, wbase), ELIM_PV));
    cc_entry_id pw = OK(cc_instr_extend(k, path_over(v, wloop, i, var(pv)), ELIM_PW));
    cc_judgement_id wrapped = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator(k, var(v))), var(pv))), var(pw)));
    cc_term wrap_clause = type_of(wrapped);
    cc_term path_bar = child(child(wrap_clause, 1), 0);
    assert(kind(path_bar) == CC_PATH && child(path_bar, 1) == term_of(var(pv)) && child(path_bar, 2) == term_of(var(pv)));
    cc_entry_id pw_var = OK(cc_instr_extend(k, wr, ELIM_WV));
    (void)pw_var;
    /* A clause for wrap, as a variable of the reported type's shape. */
    cc_entry_id loop_var = OK(cc_instr_extend(k, OK(cc_instr_path(k, i, wr, wbase, wbase)), ELIM_WP));
    cc_entry_id loop_bar = OK(cc_instr_extend(k, path_over(v, var(loop_var), i, var(pv)), ELIM_WPB));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, loop_var, OK(cc_instr_pi(k, loop_bar,
        at(v, OK(cc_instr_apply(k, OK(cc_instr_construct(k, wr, 2)), var(loop_var))))))));
    assert(ck_alpha_equal(k, term_of(wrap_type), wrap_clause));
    cc_entry_id mw = OK(cc_instr_extend(k, wrap_type, ELIM_MW));
    cc_term fix_clause = type_of(OK(cc_instr_eliminator_clause(k, wrapped, var(mw))));
    cc_term left = child(fix_clause, 1);
    assert(kind(fix_clause) == CC_PATH && kind(left) == CC_APP && child(child(left, 0), 0) == term_of(var(mw)));
    cc_term shown_line = child(left, 1);
    assert(kind(shown_line) == CC_PLAM && kind(child(shown_line, 1)) == CC_PAPP &&
           child(child(shown_line, 1), 0) == term_of(var(pw)));
    assert(child(fix_clause, 2) == term_of(var(pv)));
}

/* Review regressions of F5: Iota instantiates fresh placeholders only; the
 * displayed binders avoid ambient dimensions; a path-valued position is
 * lifted to a path abstraction. */
static void elimination_capture(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id nat = OK(cc_instr_nat(k)), zero = OK(cc_instr_zero(k));

    /* Box { box(n : Nat); }, and the clause λ x. n, whose n is the admission
     * entry, free: elim(box(0)) is (λ x. n)(0). */
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_BOX, 0));
    cc_entry_id bs = OK(cc_instr_extend(k, former_u0(), S_BOX));
    cc_entry_id bn = OK(cc_instr_extend(k, nat, BOX_N));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, bn, var(bs))), BOX));
    cc_judgement_id boxes = OK(cc_instr_sort_begin(k, OK(cc_instr_signature_close(k, sig))));
    cc_judgement_id box = OK(cc_instr_construct(k, boxes, 0));
    cc_judgement_id constant = OK(cc_instr_lambda(k, OK(cc_instr_extend(k, boxes, BOX_Z)), nat));
    cc_judgement_id opened = OK(cc_instr_eliminator(k, constant));
    cc_entry_id bx = OK(cc_instr_extend(k, nat, BOX_X));
    cc_judgement_id target = OK(cc_instr_pi(k, bx, OK(cc_instr_apply(k, constant, OK(cc_instr_apply(k, box, var(bx)))))));
    assert(ck_alpha_equal(k, term_of(target), type_of(opened)));
    cc_judgement_id to_nat = OK(cc_instr_step(k, OK(cc_instr_refl(k, target)), 1, (const uint8_t[]){1}, 1, CC_STEP_BETA));
    cc_judgement_id clause = OK(cc_instr_convert(k, OK(cc_instr_lambda(k, bx, var(bn))), OK(cc_instr_symmetry(k, to_nat))));
    cc_judgement_id box_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, opened, clause))));
    cc_term on_box = iota_of(OK(cc_instr_apply(k, box_elim, OK(cc_instr_apply(k, box, zero)))));
    assert(on_box == term_of(OK(cc_instr_apply(k, clause, zero))));

    /* The motive F @ i, whose free dimension is the circle loop's binder:
     * loop's clause is PathP(j. (F @ i)(loop @ j), fb, fb). */
    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_judgement_id base = OK(cc_instr_construct(k, s1, 0)), loop = OK(cc_instr_construct(k, s1, 1));
    cc_judgement_id family = OK(cc_instr_pi(k, OK(cc_instr_extend(k, s1, AMB_Z)), universe(lconst(0))));
    cc_entry_id pp = OK(cc_instr_extend(k, family, AMB_P));
    cc_entry_id f = OK(cc_instr_extend(k, OK(cc_instr_path(k, j, family, var(pp), var(pp))), AMB_F));
    cc_judgement_id motive = OK(cc_instr_path_apply(k, var(f), i, 0));
    cc_entry_id fb = OK(cc_instr_extend(k, OK(cc_instr_apply(k, motive, base)), AMB_FB));
    cc_judgement_id with_base = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, motive)), var(fb)));
    cc_judgement_id ends[2];
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at_end = OK(cc_instr_apply(k, motive, OK(cc_instr_path_apply(k, loop, 0, e))));
        cc_judgement_id to_base = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_end)), 1, (const uint8_t[]){1}, 1,
                                                   CC_STEP_PATH));
        ends[e] = OK(cc_instr_convert(k, var(fb), OK(cc_instr_symmetry(k, to_base))));
    }
    cc_judgement_id loop_type = OK(cc_instr_path(k, j, OK(cc_instr_apply(k, motive, OK(cc_instr_path_apply(k, loop, j, 0)))),
                                                 ends[0], ends[1]));
    assert(ck_alpha_equal(k, term_of(loop_type), type_of(with_base)));
    OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, with_base,
        var(OK(cc_instr_extend(k, loop_type, AMB_FL)))))));

    /* PW { base; loop : base = base; wrap(p : base = base) : base = base; }. */
    sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_PW, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_PW));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), PW_BASE));
    cc_entry_id pbase = OK(cc_instr_extend(k, var(s), PW_BASE));
    cc_judgement_id around = OK(cc_instr_path(k, i, var(s), var(pbase), var(pbase)));
    sig = OK(cc_instr_signature_constructor(k, sig, around, PW_LOOP));
    OK(cc_instr_extend(k, around, PW_LOOP));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, OK(cc_instr_extend(k, around, PW_P)), around)), PW_WRAP));
    cc_judgement_id pw = OK(cc_instr_sort_begin(k, OK(cc_instr_signature_close(k, sig))));
    cc_judgement_id b0 = OK(cc_instr_construct(k, pw, 0)), l0 = OK(cc_instr_construct(k, pw, 1));
    cc_judgement_id w0 = OK(cc_instr_construct(k, pw, 2));
    cc_entry_id v = motive_over(pw, PW_V);
    cc_entry_id pv = OK(cc_instr_extend(k, at(v, b0), PW_PV));
    cc_entry_id pl = OK(cc_instr_extend(k, path_over(v, l0, i, var(pv)), PW_PL));
    cc_judgement_id loops = OK(cc_instr_path(k, i, pw, b0, b0));
    cc_entry_id pe = OK(cc_instr_extend(k, loops, PW_PE));
    cc_entry_id pbar = OK(cc_instr_extend(k, path_over(v, var(pe), i, var(pv)), PW_PBAR));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, pe, OK(cc_instr_pi(k, pbar,
        path_over(v, OK(cc_instr_apply(k, w0, var(pe))), i, var(pv))))));
    cc_judgement_id opened_pw = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator(k, var(v))), var(pv))), var(pl)));
    assert(ck_alpha_equal(k, term_of(wrap_type), type_of(opened_pw)));
    cc_entry_id mw = OK(cc_instr_extend(k, wrap_type, PW_MW));
    cc_judgement_id pw_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, opened_pw, var(mw)))));
    /* elim(wrap(p0) @ j) is m_wrap(p0, ⟨i⟩ elim(p0 @ i)) @ j. */
    cc_entry_id p0 = OK(cc_instr_extend(k, loops, PW_P0));
    cc_term reduced = iota_of(OK(cc_instr_apply(k, pw_elim, OK(cc_instr_path_apply(k,
        OK(cc_instr_apply(k, w0, var(p0))), j, 0)))));
    assert(kind(reduced) == CC_PAPP && kind(child(reduced, 1)) == CC_PATH);
    cc_term applied = child(reduced, 0);
    cc_judgement_id lifted_p0 = OK(cc_instr_path_lambda(k, i, OK(cc_instr_apply(k, pw_elim,
        OK(cc_instr_path_apply(k, var(p0), i, 0))))));
    assert(child(child(applied, 0), 0) == term_of(var(mw)) && child(child(applied, 0), 1) == term_of(var(p0)));
    assert(ck_alpha_equal(k, child(applied, 1), term_of(lifted_p0)));
    /* At j = 0 both orders give pv: the boundary, then elim; or Iota, then
     * the path step through the displayed annotation. */
    cc_judgement_id at_zero = OK(cc_instr_apply(k, pw_elim, OK(cc_instr_path_apply(k,
        OK(cc_instr_apply(k, w0, var(p0))), 0, 0))));
    assert(reduct(at_zero, CC_STEP_WHNF) == term_of(var(pv)));
    cc_judgement_id by_iota = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_zero)), 1, NULL, 0, CC_STEP_IOTA));
    assert(info(OK(cc_instr_step(k, by_iota, 1, NULL, 0, CC_STEP_PATH))).other == term_of(var(pv)));
}

/* Section 3.2's invariant: every path application in a judgement carries
 * its annotation, a path type, which boundary reduction reads. */
static void annotated(cc_term t, unsigned char *seen) {
    if (!t || seen[t])
        return;
    seen[t] = 1;
    cc_term_kind node_kind;
    cc_term children[4];
    assert(cc_kernel_node(k, t, &node_kind, NULL, children));
    assert(node_kind != CC_PAPP || (children[1] && kind(children[1]) == CC_PATH));
    for (unsigned c = 0; c < 4; ++c)
        annotated(children[c], seen);
}

static void annotations(void) {
    size_t nodes = 0, bytes = 0;
    cc_kernel_arena(k, &nodes, &bytes);
    unsigned char *seen = calloc(nodes + 1, 1);
    assert(seen);
    for (cc_judgement_id id = 1; id < cc_kernel_judgement_count(k); ++id) {
        cc_judgement_info j = info(id);
        annotated(j.term, seen);
        annotated(j.other, seen);
        annotated(j.type, seen);
    }
    free(seen);
}

/* Refusals of section 10.1. Each uses a fresh open signature over U0 whose
 * sort entry is s. */
static cc_judgement_id open_bad(cc_entry_id *s, uint32_t sort) {
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, sort, 0));
    *s = OK(cc_instr_extend(k, former_u0(), sort));
    return sig;
}

static void refusals(void) {
    cc_entry_id s;
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_judgement_id sig = open_bad(&s, S_BAD);
    cc_entry_id f = OK(cc_instr_extend(k, OK(cc_instr_pi(k, OK(cc_instr_extend(k, var(s), BX)), nat)), BF));
    /* A4: s in data, as the domain of a function argument. */
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, f, var(s))), BAD), "arity mentions");
    /* A5: s in an arity: f : (s → Nat) → s. */
    cc_judgement_id s_to_nat = OK(cc_instr_pi(k, OK(cc_instr_extend(k, var(s), BX)), nat));
    cc_entry_id h = OK(cc_instr_extend(k, s_to_nat, BH));
    cc_entry_id g = OK(cc_instr_extend(k, OK(cc_instr_pi(k, h, var(s))), BG));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, g, var(s))), BAD), "arity mentions");
    /* A6: s under a function inside a position's arity: g : Nat → (s → s). */
    cc_entry_id an = OK(cc_instr_extend(k, nat, A6_N)), ax = OK(cc_instr_extend(k, var(s), A6_X));
    cc_entry_id ag = OK(cc_instr_extend(k, OK(cc_instr_pi(k, an, OK(cc_instr_pi(k, ax, var(s))))), A6_G));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, ag, var(s))), BAD), "arity mentions");
    /* A11: data after a position, in the kernel's order. */
    cc_entry_id x = OK(cc_instr_extend(k, var(s), BX));
    cc_entry_id n = OK(cc_instr_extend(k, nat, BN));
    cc_judgement_id late_data = OK(cc_instr_pi(k, x, OK(cc_instr_pi(k, n, var(s)))));
    REJECTS(cc_instr_signature_constructor(k, sig, late_data, BAD), "data argument follows a position");
    /* A13: a foreign entry in the constructor type's context: a type
     * variable T : U0 that is not the signature's. */
    cc_entry_id foreign = OK(cc_instr_extend(k, former_u0(), OTHER));
    REJECTS(cc_instr_signature_constructor(k, sig, var(foreign), BAD), "not the signature's");
    /* A constructor type in another universe: U0 itself lives in U1. */
    REJECTS(cc_instr_signature_constructor(k, sig, former_u0(), BAD), "signature's universe");
    /* A7: a boundary naming the constructor itself. */
    cc_entry_id self = OK(cc_instr_extend(k, var(s), C1));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_path(k, i, var(s), var(self), var(self))), C1),
            "itself");
    /* A8: a boundary naming a later constructor: the entry is not yet the
     * signature's. */
    cc_entry_id later = OK(cc_instr_extend(k, var(s), LATER));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_path(k, i, var(s), var(later), var(later))), C2),
            "not the signature's");
    /* A boundary with a composition (A9): comp^i s [] x, with x : s a position. */
    cc_judgement_id good = OK(cc_instr_signature_constructor(k, sig, var(s), C1));
    cc_entry_id c1 = OK(cc_instr_extend(k, var(s), C1));
    (void)c1;
    cc_entry_id z = OK(cc_instr_extend(k, var(s), Z));
    cc_judgement_id system = OK(cc_instr_system(k, i, var(s), var(z)));
    cc_judgement_id composed = OK(cc_instr_comp(k, system));
    cc_entry_id j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id with_comp = OK(cc_instr_pi(k, z, OK(cc_instr_path(k, j, var(s), composed, var(z)))));
    REJECTS(cc_instr_signature_constructor(k, good, with_comp, C2), "composition");
    /* Only the latest judgement continues a signature. */
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), C2), "latest");
    /* A12: a data argument that mentions a position, in a boundary. */
    cc_judgement_id nat_con = OK(cc_instr_pi(k, n, var(s)));
    cc_judgement_id with_nat = OK(cc_instr_signature_constructor(k, good, nat_con, C2));
    cc_entry_id c2 = OK(cc_instr_extend(k, nat_con, C2));
    cc_entry_id w = OK(cc_instr_extend(k, var(s), Z + 1));
    cc_judgement_id zero_of_w = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, OK(cc_instr_extend(k, var(s), Z + 2)),
                                                                           OK(cc_instr_zero(k)))), var(w)));
    cc_judgement_id tainted = OK(cc_instr_apply(k, var(c2), zero_of_w));
    cc_judgement_id tainted_type = OK(cc_instr_pi(k, w, OK(cc_instr_path(k, i, var(s), tainted, var(w)))));
    REJECTS(cc_instr_signature_constructor(k, with_nat, tainted_type, Z + 3), "data terms only");
    /* T7: a commit while a signature is open is refused; T5: rollback
     * forgets a signature opened since the checkpoint. */
    size_t before = cc_kernel_signature_count(k);
    cc_kernel_checkpoint(k);
    cc_entry_id s2;
    cc_judgement_id opened = open_bad(&s2, S_BAD + 50);
    (void)opened;
    assert(cc_kernel_signature_count(k) == before + 1);
    assert(!cc_kernel_commit_checkpoint(k));
    assert(strstr(cc_kernel_error(k), "still open"));
    cc_kernel_clear_error(k);
    cc_kernel_rollback(k);
    assert(cc_kernel_signature_count(k) == before);
}

/* V13, V17–V19: a bound of tier 1 in what a constructor type uses. H1
 * admits each signature, since for finite x the parameter A : U(x) lifts
 * into UU0, and refuses every instance that reads a level of tier 1 (Q16).
 * The later proposal's tier-parametric check (2.3) is not H1's. */
/* ⊢ Π (x < ω). Π (A : U(x)). U0, with x and A named by the given symbols. */
static cc_judgement_id former_into_u0(uint32_t x, uint32_t a, cc_entry_id *ae) {
    cc_entry_id xe = OK(cc_instr_level(k, x));
    *ae = OK(cc_instr_extend(k, universe(lvar(x)), a));
    return OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, *ae, universe(lconst(0))))));
}

static void hidden_bounds(void) {
    cc_judgement_id nat = OK(cc_instr_nat(k)), u0 = universe(lconst(0)), uu0 = universe(tier1(0));
    cc_judgement_id nat_big = OK(cc_instr_lift(k, nat, uu0)), uu0_itself = uu0;
    cc_entry_id ae;

    /* V13: Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); } lives in UU0;
     * Mixed(U2, Nat) reads x = 3, and Mixed(Nat) with Nat : UU0 reads ω. */
    cc_entry_id be = OK(cc_instr_extend(k, uu0, HB_B));
    cc_entry_id xe = OK(cc_instr_level(k, HB_X));
    ae = OK(cc_instr_extend(k, universe(lvar(HB_X)), HB_A));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, ae, OK(cc_instr_pi(k, be, uu0))))));
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_MIXED, 0));
    cc_entry_id s = OK(cc_instr_extend(k, uu0, S_MIXED));
    cc_entry_id a = OK(cc_instr_extend(k, var(ae), HB_MA)), b = OK(cc_instr_extend(k, var(be), HB_MB));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, b, var(s))))), HB_MK));
    uint32_t mixed = OK(cc_instr_signature_close(k, sig));
    cc_judgement_id at3 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, mixed)), universe(lconst(2))));
    assert(type_of(OK(cc_instr_sort_parameter(k, at3, nat_big))) == term_of(uu0));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, mixed)), nat_big)), nat_big),
            "finite levels only");

    /* V17: Tag(A : UU0) : U0 { here; } and Outer(x < ω, A : U(x)) : U0
     * { wrap(t : Tag(A)); }, with A lifted into UU0; Outer(Nat) is formed,
     * Outer(UU0) and Outer(A) for A : UU0 are not. */
    cc_entry_id ta = OK(cc_instr_extend(k, uu0, HB_TA));
    sig = OK(cc_instr_signature_begin(k, OK(cc_instr_pi(k, ta, u0)), CC_UNTRUNCATED, S_TAG2, 0));
    s = OK(cc_instr_extend(k, u0, S_TAG2));
    uint32_t tag = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, sig, var(s), HB_HERE))));
    former = former_into_u0(HB_X + 100, HB_A + 100, &ae);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_OUTER, 0));
    s = OK(cc_instr_extend(k, u0, S_OUTER));
    cc_judgement_id tag_a = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, tag)), OK(cc_instr_lift(k, var(ae), uu0))));
    cc_entry_id held = OK(cc_instr_extend(k, tag_a, HB_T));
    uint32_t outer = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, sig,
        OK(cc_instr_pi(k, held, var(s))), HB_WRAP))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), nat));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), uu0_itself), "finite levels only");
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), nat_big), "finite levels only");

    /* V18: the same bound through a definition F(A : UU0) : U0 := Unit, in
     * wrap(t : F(A)); refused at the instance that reads it. */
    cc_entry_id fa = OK(cc_instr_extend(k, uu0, HB_FA));
    cc_judgement_id f = OK(cc_instr_define(k, HB_F, OK(cc_instr_lambda(k, fa, OK(cc_instr_unit(k))))));
    former = former_into_u0(HB_X + 200, HB_A + 200, &ae);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_HID2, 0));
    s = OK(cc_instr_extend(k, u0, S_HID2));
    cc_entry_id through = OK(cc_instr_extend(k, OK(cc_instr_apply(k, f, OK(cc_instr_lift(k, var(ae), uu0)))), HB_T + 100));
    uint32_t hid = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, sig,
        OK(cc_instr_pi(k, through, var(s))), HB_WRAP2))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, hid)), nat));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, hid)), nat_big), "finite levels only");

    /* V19: Big : UU1 { pack(B : UU0); } and Outer2(x < ω, A : U(x),
     * F : Big → U0) : U0 { wrap(t : F(pack(A))); }: a bound in a
     * parameter-free signature's constructor type. */
    cc_judgement_id uu1 = universe(tier1(1));
    sig = OK(cc_instr_signature_begin(k, uu1, CC_UNTRUNCATED, S_BIG, 0));
    s = OK(cc_instr_extend(k, uu1, S_BIG));
    cc_entry_id bb = OK(cc_instr_extend(k, uu0, HB_BB));
    uint32_t big = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, bb, var(s))),
        HB_PACK))));
    cc_judgement_id big_instance = OK(cc_instr_sort_begin(k, big));
    cc_entry_id z = OK(cc_instr_extend(k, big_instance, HB_Z));
    cc_entry_id x2 = OK(cc_instr_level(k, HB_X + 300));
    cc_entry_id a2 = OK(cc_instr_extend(k, universe(lvar(HB_X + 300)), HB_A + 300));
    cc_entry_id fe = OK(cc_instr_extend(k, OK(cc_instr_pi(k, z, u0)), HB_FF));
    former = OK(cc_instr_level_pi(k, x2, OK(cc_instr_pi(k, a2, OK(cc_instr_pi(k, fe, u0))))));
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, S_OUTER2, 0));
    s = OK(cc_instr_extend(k, u0, S_OUTER2));
    cc_judgement_id packed = OK(cc_instr_apply(k, OK(cc_instr_construct(k, big_instance, 0)), OK(cc_instr_lift(k, var(a2), uu0))));
    cc_entry_id carried = OK(cc_instr_extend(k, OK(cc_instr_apply(k, var(fe), packed)), HB_T + 200));
    uint32_t outer2 = OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, sig,
        OK(cc_instr_pi(k, carried, var(s))), HB_WRAP3))));
    cc_judgement_id family = OK(cc_instr_lambda(k, OK(cc_instr_extend(k, big_instance, HB_UZ)), OK(cc_instr_unit(k))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), nat)), family));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), uu0_itself)), family),
            "finite levels only");
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), nat_big)), family),
            "finite levels only");
}

/* R2, R3: the resource bounds of 5.8, at their limits and above them. */
static void resources(void) {
    /* R2: 256 constructors are admitted, and a 257th is refused. */
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_RES, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), S_RES));
    for (uint32_t c = 0; c < CC_SIGNATURE_CONSTRUCTORS; ++c)
        sig = OK(cc_instr_signature_constructor(k, sig, var(s), RES_C + c));
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), RES_C + CC_SIGNATURE_CONSTRUCTORS), "too many constructors");
    assert(signature(OK(cc_instr_signature_close(k, sig))).constructor_count == CC_SIGNATURE_CONSTRUCTORS);

    /* R2: a constructor with 64 arguments is admitted, and one with 65 is
     * refused. */
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_entry_id args[CC_CONSTRUCTOR_ARGUMENTS + 1];
    for (uint32_t a = 0; a <= CC_CONSTRUCTOR_ARGUMENTS; ++a)
        args[a] = OK(cc_instr_extend(k, nat, RES_N + a));
    sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_ARGS, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_ARGS));
    cc_judgement_id at_limit = var(s);
    for (uint32_t a = CC_CONSTRUCTOR_ARGUMENTS; a-- > 0;)
        at_limit = OK(cc_instr_pi(k, args[a], at_limit));
    REJECTS(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, args[CC_CONSTRUCTOR_ARGUMENTS], at_limit)), RES_F),
            "too many arguments");
    sig = OK(cc_instr_signature_constructor(k, sig, at_limit, RES_F));
    assert(constructor(OK(cc_instr_signature_close(k, sig)), 0).data == CC_CONSTRUCTOR_ARGUMENTS);

    /* R3: a position of arity 64 into a cube of depth 8, ⟨i⟩ … b at each
     * level, is admitted within the budget. */
    sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_DEEP, 0));
    s = OK(cc_instr_extend(k, former_u0(), S_DEEP));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), RES_B));
    cc_judgement_id cube = var(s), point = var(OK(cc_instr_extend(k, var(s), RES_B)));
    for (unsigned d = 0; d < 8; ++d) {
        cc_entry_id dimension = OK(cc_instr_dimension(k, d));
        cc_judgement_id next = OK(cc_instr_path(k, dimension, cube, point, point));
        point = OK(cc_instr_path_lambda(k, dimension, point));
        cube = next;
    }
    cc_judgement_id position = cube;
    for (uint32_t a = CC_CONSTRUCTOR_ARGUMENTS; a-- > 0;)
        position = OK(cc_instr_pi(k, args[a], position));
    cc_entry_id f = OK(cc_instr_extend(k, position, RES_A));
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, f, var(s))), RES_F + 1));
    uint32_t deep = OK(cc_instr_signature_close(k, sig));
    cc_kernel_work(k, &after);
    assert(constructor(deep, 1).positions == 1);
    assert(after.instruction_steps - before.instruction_steps < 1000000);
}

/* R1: malformed declared-type nodes, built as raw syntax: a sort, a
 * constructor and an eliminator whose indices are out of range, a list cell
 * whose next cell is no list, and the eliminator applied. Inspection reads
 * them, reduction leaves them or refuses them with an error, and the term
 * checker and the instructions refuse them. */
static void malformed(void) {
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term sort = cc_kernel_term(k, CC_SORT, 9999, 0, 0, 0, 0);
    cc_term con = cc_kernel_term(k, CC_CON, 77, sort, 0, 0, 0);
    cc_term elim = cc_kernel_term(k, CC_ELIM, 9999, nat, 0, 0, 0);
    const cc_term terms[] = {sort, con, elim, cc_kernel_term(k, CC_LIST, 0, con, nat, 0, 0),
                             cc_kernel_term(k, CC_APP, 0, elim, con, 0, 0)};
    for (unsigned t = 0; t < sizeof terms / sizeof *terms; ++t) {
        assert(terms[t] && !cc_kernel_error(k)[0]);
        cc_term_kind seen;
        assert(cc_kernel_node(k, terms[t], &seen, NULL, NULL));
        if (!cc_kernel_whnf(k, terms[t]))
            cc_kernel_clear_error(k);
        if (!cc_kernel_normalize(k, terms[t]))
            cc_kernel_clear_error(k);
        cc_checked_result checked;
        assert(!cc_kernel_check(k, terms[t], 0, NULL, 0, &checked));
        assert(strstr(cc_kernel_error(k), "no rules for declared types"));
        cc_kernel_clear_error(k);
    }
    cc_signature_info info;
    assert(!cc_kernel_signature(k, 9999, &info));
    REJECTS(cc_instr_sort_begin(k, 9999), "Only an admitted signature");
}

/* T6: a commit keeps an admitted signature and relocates its syntax. */
static void commits(void) {
    cc_kernel_checkpoint(k);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, 300, 0));
    cc_entry_id s = OK(cc_instr_extend(k, former_u0(), 300));
    cc_entry_id m = OK(cc_instr_extend(k, var(s), 301));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), 302));
    sig = OK(cc_instr_signature_constructor(k, sig, OK(cc_instr_pi(k, m, var(s))), 303));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    assert(cc_kernel_commit_checkpoint(k));
    cc_constructor_info succ = constructor(index, 1);
    assert(kind(succ.type) == CC_PI && succ.symbol == 303 && succ.positions == 1);
    /* Instances formed after the commit check. */
    assert(kind(type_of(OK(cc_instr_construct(k, OK(cc_instr_sort_begin(k, index)), 1)))) == CC_PI);
    assert(kind(signature(index).former) == CC_U);
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    /* T1: without the extension, admission is refused. */
    REJECTS(cc_instr_signature_begin(k, former_u0(), CC_UNTRUNCATED, S_N, 0), "kernel extension under review");
    cc_kernel_set_extensions(k, CC_EXTENSION_H1);
    assert(cc_kernel_extensions(k) == CC_EXTENSION_H1);
    /* Formers that are not Π (xs < ω). Π (ps : Ps). U(ℓ), or not closed. */
    REJECTS(cc_instr_signature_begin(k, OK(cc_instr_nat(k)), CC_UNTRUNCATED, S_N, 0), "former type");
    REJECTS(cc_instr_signature_begin(k, former_u0(), CC_TRUNCATION_MAX + 3, S_N, 0), "truncation level");
    natural_numbers();
    lists();
    circle();
    squares();
    truncations();
    recorded_parameters();
    shapes();
    carried_types();
    generative();
    instances();
    boundaries();
    kan();
    elimination();
    elimination_capture();
    annotations();
    refusals();
    hidden_bounds();
    resources();
    malformed();
    commits();
    cc_kernel_free(k);
    printf("signature admission: ok\n");
    return 0;
}
