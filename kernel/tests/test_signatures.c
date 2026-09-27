/* Declared types (H1), families F1 and F6: signatures are admitted one
 * constructor at a time, and refused where the specification's acceptance
 * cases say (docs/roadmaps/h1-signature-specification.md, section 10). Every
 * constructor type is derived here by ordinary instructions, as the driver
 * derives it. */
#include "cubical_kernel.h"
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;
/* Signatures admitted by the sections below, for the instance tests. */
static uint32_t nat_signature, list_signature, circle_signature, trunc_signature, pointed_signature,
    tagged_signature, tree_signature, wrapped_signature, branch_signature;

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
    S_OPEN = 480, OPEN_C, TREE_N, S_GONE
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
    uint32_t torus = OK(cc_instr_signature_close(k, sig));
    assert(constructor(torus, 3).dimensions == 2);

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
    refusals();
    commits();
    cc_kernel_free(k);
    printf("signature admission: ok\n");
    return 0;
}
