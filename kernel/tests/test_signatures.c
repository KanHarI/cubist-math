/* Declared types (H1), families F1 and F6: signatures are admitted one
 * constructor at a time, and refused where the specification's acceptance
 * cases say (docs/roadmaps/hott/h1-signature-specification.md, section 10). Every
 * constructor type is derived here by ordinary instructions, as the driver
 * derives it. */
#include "cubical_kernel.h"
#include "term_internal.h"
#include "declared_nat_fixture.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static cc_kernel *k;
/* Signatures admitted by the sections below, for the instance tests. */
static uint32_t nat_signature, list_signature, circle_signature, trunc_signature, pointed_signature,
    tagged_signature, tree_signature, wrapped_signature, branch_signature, torus_signature, susp_signature,
    set_signature, groupoid_signature, quotient_signature;

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
/* A level variable: the reference to a level entry. */
static cc_term lvar(cc_entry_id level) { return cc_kernel_term(k, CC_CONTEXT, level, 0, 0, 0, 0); }
static cc_term lsucc(cc_term level) { return cc_kernel_term(k, CC_LSUCC, 1, level, 0, 0, 0); }
/* The variable of the index-th enclosing binder, as a closed type reports
 * it. */
static cc_term bound(uint32_t index) { return cc_kernel_term(k, CC_BOUND, index, 0, 0, 0, 0); }
static cc_term pi(cc_term domain, cc_term body) { return cc_kernel_term(k, CC_PI, 0, domain, body, 0, 0); }
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

/* The kernel keeps no names: every entry here is made by Extend or Level,
 * and stands for what the driver would name. A signature is opened with
 * the entries for its former's binders, the universe parameters' level
 * entries and then the term parameters', and its sort's entry, all made
 * before SignatureBegin; each constructor with an entry at its type, made
 * before SignatureConstructor, for later constructor types to mention. */
static cc_entry_id extend(cc_judgement_id type) { return OK(cc_instr_extend(k, type)); }

/* SignatureConstructor at a type, with a new entry at that type standing
 * for the constructor; the result is the instruction's, for OK or
 * REJECTS. */
static cc_judgement_id admit(cc_judgement_id signature, cc_judgement_id type) {
    return cc_instr_signature_constructor(k, signature, type, extend(type));
}

/* ⊢ U(0) : U(1), the former of a signature with no parameters in U0. */
static cc_judgement_id former_u0(void) { return universe(lconst(0)); }

/* SignatureBegin over U0 with no parameters, at the sort entry s : U0. */
static cc_judgement_id begin_u0(uint32_t modifier, cc_entry_id sort) {
    return cc_instr_signature_begin(k, former_u0(), modifier, NULL, 0, sort, 0);
}

/* ⊢ Π (x < ω). Π (A : U(x)). U(x) : U(ω), the former of List, Trunc and
 * the like, with the level entry x and the term entry A : U(x) that stand
 * for its binders. */
static cc_judgement_id former_generic(cc_entry_id *xe, cc_entry_id *ae) {
    *xe = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(*xe));
    *ae = extend(ux);
    cc_judgement_id body = OK(cc_instr_pi(k, *ae, ux));
    return OK(cc_instr_level_pi(k, *xe, body));
}

/* A1: N here, List and the circle below, Tree in shapes, and Push and Susp
 * in boundaries, each admitted in normal form. */
static void natural_numbers(void) {
    /* inductive N { zero; succ(n : N); } */
    uint32_t index;
    cc_entry_id s = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id zero = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), zero));
    cc_entry_id n = extend(var(s));
    cc_judgement_id succ_type = OK(cc_instr_pi(k, n, var(s)));
    cc_entry_id succ_entry = extend(succ_type);
    sig = OK(cc_instr_signature_constructor(k, sig, succ_type, succ_entry));
    index = OK(cc_instr_signature_close(k, sig));
    nat_signature = index;
    cc_signature_info info = signature(index);
    assert(info.admitted && !info.experimental && info.constructor_count == 2 && !info.level_count);
    assert(info.former == term_of(former_u0()) && info.level == lconst(0));
    /* The constructors carry no name: their types are reported closed over
     * the telescope [s, zero], index 0 the last: zero : s is Bound 0, and
     * succ : Π (n : s). s is Π (Bound 1). Bound 2. */
    cc_constructor_info first = constructor(index, 0), succ = constructor(index, 1);
    assert(first.type == bound(0) && !first.data && !first.positions && !first.generated);
    assert(succ.type == pi(bound(1), bound(2)));
    assert(succ.data == 0 && succ.positions == 1 && succ.dimensions == 0 && !succ.generated);
    /* A14: an admitted signature never changes. */
    REJECTS(cc_instr_signature_close(k, sig), "already admitted");
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), extend(var(s))), "already admitted");
}

static void lists(void) {
    /* inductive List(U < UU0, A : U) { nil; cons(head : A, tail : List); }: the
     * universe parameter is erased, determined by A : U(x). */
    cc_entry_id xe, ae;
    cc_judgement_id former = former_generic(&xe, &ae);
    const cc_entry_id parameters[] = {xe, ae};
    cc_entry_id s = extend(universe(lvar(xe)));
    cc_judgement_id begun = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 2, s, 0));
    /* SignatureBegin's judgement records its entries: the parameters', then
     * the sort's. */
    cc_judgement_info opened = info(begun);
    assert(opened.entry_count == 2 && opened.entries[0] == xe && opened.entries[1] == ae && opened.operand[0] == s);
    cc_judgement_id sig = OK(cc_instr_signature_constructor(k, begun, var(s), extend(var(s))));
    cc_entry_id head = extend(var(ae));
    cc_entry_id tail = extend(var(s));
    cc_judgement_id cons_type = OK(cc_instr_pi(k, head, OK(cc_instr_pi(k, tail, var(s)))));
    sig = OK(admit(sig, cons_type));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    list_signature = index;
    cc_signature_info info = signature(index);
    assert(info.level_count == 1 && info.parameter_count == 1 && info.recorded == 0);
    /* No names are reported: the former is closed, its level U(x) is index 1
     * over the prenex [x, A], and cons : Π (head : A). Π (tail : s). s is
     * closed over the telescope [x, A, s, nil]; nil : s over [x, A, s]. */
    assert(info.former == term_of(former) && info.level == bound(1));
    cc_constructor_info cons = constructor(index, 1);
    assert(cons.data == 1 && cons.positions == 1 && cons.dimensions == 0);
    assert(cons.type == pi(bound(2), pi(bound(2), bound(3))) && constructor(index, 0).type == bound(0));
}

/* The circle: base; loop : Path(i; s, base, base). */
static void circle(void) {
    cc_entry_id s = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id base = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), base));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    sig = OK(admit(sig, loop_type));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    circle_signature = index;
    cc_constructor_info loop = constructor(index, 1);
    assert(loop.dimensions == 1 && loop.data == 0 && loop.positions == 0);
    /* Path(i; s, base, base) over [s, base]: the dimension keeps its index. */
    assert(loop.type == cc_kernel_term(k, CC_PATH, 0, bound(1), bound(0), bound(0), 0));
}

/* A2: the torus, whose square's inner endpoints are p @ i, and S2, whose
 * outer endpoints are path abstractions ⟨j⟩ base. */
static void squares(void) {
    cc_entry_id s = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id b = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), b));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    /* p and q : Path(j; s, b, b), over the dimension the square's inner paths use. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, j, var(s), var(b), var(b)));
    cc_entry_id p = extend(loop_type);
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, p));
    cc_entry_id q = extend(loop_type);
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, q));
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
    sig = OK(admit(sig, surf_type));
    uint32_t torus = torus_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(torus, 3).dimensions == 2);
    /* A10: a square whose sides do not meet the inner paths at a corner.
     * Over the constant inner family Path(j; s, b, b), a side q : Path(j; s,
     * b, b) meets it at every corner, and the square's path type is formed;
     * r : Path(j; s, c, c), for another point c, does not, and it is not. */
    cc_judgement_id flat_inner = OK(cc_instr_path(k, j, var(s), var(b), var(b)));
    cc_entry_id side = extend(flat_inner);
    OK(cc_instr_path(k, i, flat_inner, var(side), var(side)));
    cc_entry_id c = extend(var(s));
    cc_entry_id r = extend(OK(cc_instr_path(k, j, var(s), var(c), var(c))));
    REJECTS(cc_instr_path(k, i, flat_inner, var(r), var(r)), "endpoint has the wrong type");

    /* S2: base; surf : Path(i; Path(j; s, base, base), ⟨j⟩ base, ⟨j⟩ base). */
    s = extend(former_u0());
    sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id base = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), base));
    cc_judgement_id flat = OK(cc_instr_path(k, j, var(s), var(base), var(base)));
    cc_judgement_id constant = OK(cc_instr_path_lambda(k, j, var(base)));
    cc_judgement_id s2_type = OK(cc_instr_path(k, i, flat, constant, constant));
    sig = OK(admit(sig, s2_type));
    uint32_t sphere = OK(cc_instr_signature_close(k, sig));
    assert(constructor(sphere, 1).dimensions == 2);
}

/* A3, A17 and the squash of 1.6: prop, set and trunc(1) add one generated
 * constructor with 1, 2 and 3 dimensions. */
static void truncations(void) {
    const uint32_t modifiers[] = {1, 2, 3};
    for (unsigned m = 0; m < 3; ++m) {
        cc_entry_id xe, ae;
        cc_judgement_id former = former_generic(&xe, &ae);
        const cc_entry_id parameters[] = {xe, ae};
        cc_entry_id s = extend(universe(lvar(xe)));
        cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, modifiers[m], parameters, 2, s, 0));
        cc_entry_id a = extend(var(ae));
        sig = OK(admit(sig, OK(cc_instr_pi(k, a, var(s)))));
        uint32_t index = OK(cc_instr_signature_close(k, sig));
        if (m == 0) trunc_signature = index;
        if (m == 1) set_signature = index;
        if (m == 2) groupoid_signature = index;
        cc_signature_info info = signature(index);
        assert(info.constructor_count == 2 && info.modifier == modifiers[m]);
        cc_constructor_info squash = constructor(index, 1);
        assert(squash.generated && squash.data == 0);
        assert(squash.dimensions == modifiers[m] && squash.positions == 2 * modifiers[m]);
        /* Its type: pairs of cells, then a path type; the carrier is the
         * sort. It took no entry, and is stored closed: it mentions none. */
        assert(kind(squash.type) == CC_PI && !k->nodes[squash.type].contexts);
        /* The prop squash, Π (y z : s). Path(s, y, z), over the telescope
         * [x, A, s, point]: the sort is index 1 at its root. */
        if (m == 0)
            assert(squash.type == pi(bound(1), pi(bound(2), cc_kernel_term(k, CC_PATH, 0, bound(3), bound(1), bound(0), 0))));
    }
}

/* Q15, V20: Pointed(U < UU0) : next(U) { pt(X : U, x : X); } has a recorded
 * universe parameter, which its constructor type mentions. V24: proposed
 * erased, a parameter a constructor type mentions is refused. */
static void recorded_parameters(void) {
    cc_entry_id ye = OK(cc_instr_level(k));
    cc_judgement_id next = universe(lsucc(lvar(ye)));
    cc_judgement_id former = OK(cc_instr_level_pi(k, ye, next));
    cc_entry_id s = extend(next);
    /* V14: with nothing to read it from, the parameter is not erasable. */
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, &ye, 1, s, 0), "determining occurrence");
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, &ye, 1, s, 1));
    cc_entry_id carrier = extend(universe(lvar(ye)));
    cc_entry_id element = extend(var(carrier));
    cc_judgement_id pt_type = OK(cc_instr_pi(k, carrier, OK(cc_instr_pi(k, element, var(s)))));
    /* pt's type lives in U(y + 1), the declared level. */
    sig = OK(admit(sig, pt_type));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    pointed_signature = index;
    assert(signature(index).recorded == 1 && constructor(index, 0).data == 2);
    /* pt : Π (X : U(y)). Π (x : X). s over [y, s]: its recorded level is
     * index 1 at the root. */
    assert(constructor(index, 0).type == pi(cc_kernel_term(k, CC_U, 0, bound(1), 0, 0, 0), pi(bound(0), bound(2))));

    /* Holder(x < ω, A : U(x)) : U(x + 1) { hold(B : U(x)); } with x proposed
     * erased: A : U(x) determines it, but hold's type mentions it. */
    cc_entry_id he = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(he));
    cc_entry_id ha = extend(ux);
    cc_judgement_id hnext = universe(lsucc(lvar(he)));
    cc_judgement_id hformer = OK(cc_instr_level_pi(k, he, OK(cc_instr_pi(k, ha, hnext))));
    const cc_entry_id hparameters[] = {he, ha};
    cc_entry_id hs = extend(hnext);
    cc_judgement_id hsig = OK(cc_instr_signature_begin(k, hformer, CC_UNTRUNCATED, hparameters, 2, hs, 0));
    cc_entry_id hb = extend(ux);
    cc_judgement_id hold_type = OK(cc_instr_pi(k, hb, var(hs)));
    cc_entry_id hold = extend(hold_type);
    REJECTS(cc_instr_signature_constructor(k, hsig, hold_type, hold), "erased universe parameter");
    /* Recorded, the same signature is admitted, over the same entries. */
    cc_judgement_id recorded = OK(cc_instr_signature_begin(k, hformer, CC_UNTRUNCATED, hparameters, 2, hs, 1));
    recorded = OK(cc_instr_signature_constructor(k, recorded, hold_type, hold));
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
    cc_judgement_id nat = OK(fixture_nat(k));
    cc_judgement_id list0 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, list_signature)), nat));
    cc_judgement_id nat1 = OK(cc_instr_lift(k, nat, universe(lconst(1))));
    cc_judgement_id list1 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, list_signature)), nat1));
    assert(term_of(list1) == term_of(list0));
    assert(type_of(list0) == term_of(universe(lconst(0))) && type_of(list1) == term_of(universe(lconst(1))));
    cc_term cons_type = type_of(OK(cc_instr_construct(k, list0, 1)));
    assert(kind(child(cons_type, 0)) == CC_SORT && child(child(cons_type, 1), 0) == term_of(list0));
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
    cc_entry_id xe = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(xe));
    cc_entry_id ae = extend(ux), be = extend(ux);
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, ae, OK(cc_instr_pi(k, be, ux))))));
    const cc_entry_id parameters[] = {xe, ae, be};
    cc_entry_id s = extend(ux);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 3, s, 0));
    cc_entry_id a = extend(var(ae)), b = extend(var(be));
    sig = OK(admit(sig, OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, b, var(s)))))));
    uint32_t both = OK(cc_instr_signature_close(k, sig));
    cc_judgement_id unit1 = OK(cc_instr_lift(k, OK(cc_instr_unit(k)), universe(lconst(1))));
    cc_judgement_id half = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, both)), nat));
    REJECTS(cc_instr_sort_parameter(k, half, unit1), "lift the lower parameter first");
    cc_judgement_id lifted = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, both)), nat1));
    assert(type_of(OK(cc_instr_sort_parameter(k, lifted, unit1))) == term_of(universe(lconst(1))));

    /* V16: λ (x < ω). Trunc(U(x)) at 0 is Trunc(U(0)) : U(1), by LevelApply and
     * a Beta step: level substitution reaches the instance's parameters. */
    cc_judgement_id trunc_ux = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), ux));
    assert(type_of(trunc_ux) == term_of(universe(lsucc(lvar(xe)))));
    cc_judgement_id at0 = OK(cc_instr_level_apply(k, OK(cc_instr_level_lambda(k, xe, trunc_ux)), lconst(0)));
    assert(type_of(at0) == term_of(universe(lconst(1))));
    cc_judgement_id reduced = OK(cc_instr_step(k, OK(cc_instr_refl(k, at0)), 1, NULL, 0, CC_STEP_BETA));
    cc_term instance = info(reduced).other;
    assert(kind(instance) == CC_SORT && child(child(instance, 0), 0) == term_of(universe(lconst(0))));
    /* A recorded level may be a level variable in the context, and no other:
     * not a bound one with no binder, nor a term entry; an instance in
     * progress has no constructors. */
    cc_judgement_id px = OK(cc_instr_sort_level(k, p, lvar(xe)));
    assert(type_of(px) == term_of(universe(lsucc(lvar(xe)))) && cc_kernel_judgement_context(k, px, 0) == xe);
    REJECTS(cc_instr_sort_level(k, p, bound(0)), "Unbound level variable");
    REJECTS(cc_instr_sort_level(k, p, lvar(ae)), "A term variable is not a level.");
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
    assert(kind(child(tag, 0)) == CC_SORT && child(child(tag, 1), 0) == term_of(universe(lconst(0))));
    assert(child(child(tag, 1), 1) == term_of(tagged_nat));

    /* Tree(Nat, λ n. Nat) : U0; sup : Π (l : Nat). Π (c : Π (b : (λ n. Nat)(l)). T). T,
     * with T the instance: the position's arity is instantiated too. */
    cc_entry_id tn = extend(nat);
    cc_judgement_id tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k,
        OK(cc_instr_sort_begin(k, tree_signature)), nat)), OK(cc_instr_lambda(k, tn, nat))));
    assert(type_of(tree) == term_of(universe(lconst(0))));
    /* An instance in progress is not rewritten: a copy would lose its count
     * of the arguments supplied, and a later argument would be dropped. */
    cc_judgement_id half_tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, tree_signature)), nat));
    REJECTS(cc_instr_step(k, half_tree, 0, NULL, 0, CC_STEP_WHNF), "not rewritten");
    REJECTS(cc_instr_replace(k, half_tree, 0, (const uint8_t[]){0, 0}, 2, OK(cc_instr_refl(k, nat)), NULL, 0),
            "not rewritten");
    cc_term sup = type_of(OK(cc_instr_construct(k, tree, 0)));
    cc_term position = child(child(sup, 1), 0);
    assert(kind(child(sup, 0)) == CC_SORT && kind(position) == CC_PI && kind(child(position, 0)) == CC_APP);
    assert(child(position, 1) == term_of(tree) && child(child(sup, 1), 1) == term_of(tree));

    /* Constructor expressions at an instance: fix : wrap(⟨i⟩ loop @ i) = base,
     * and collapse's λ, mention none of the entries the signature was
     * admitted with, nor any other, and no loose index, in the annotations
     * they carry included: the instance closes the telescope. */
    cc_term fix = type_of(OK(cc_instr_construct(k, OK(cc_instr_sort_begin(k, wrapped_signature)), 3)));
    assert(!k->nodes[fix].contexts && !k->nodes[fix].loose);
    cc_term wrap_at = child(fix, 1);
    assert(kind(wrap_at) == CC_APP && kind(child(wrap_at, 0)) == CC_CON && payload(child(wrap_at, 0)) == 2);
    cc_judgement_id branch = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, branch_signature)), nat));
    cc_term collapse = type_of(OK(cc_instr_construct(k, branch, 2)));
    assert(!k->nodes[collapse].contexts && !k->nodes[collapse].loose);

    /* Section 5.3's refusals: an open signature, and a rolled-back one. */
    cc_entry_id os = extend(former_u0());
    cc_judgement_id open = OK(begin_u0(CC_UNTRUNCATED, os));
    REJECTS(cc_instr_sort_begin(k, payload(term_of(open))), "Only an admitted signature");
    OK(cc_instr_signature_close(k, OK(admit(open, var(os)))));
    REJECTS(cc_instr_sort_begin(k, 0), "Only an admitted signature");
    cc_kernel_checkpoint(k);
    cc_entry_id gs = extend(former_u0());
    cc_judgement_id gone = OK(begin_u0(CC_UNTRUNCATED, gs));
    uint32_t forgotten = OK(cc_instr_signature_close(k, OK(admit(gone, var(gs)))));
    OK(cc_instr_sort_begin(k, forgotten));
    cc_kernel_rollback(k);
    REJECTS(cc_instr_sort_begin(k, forgotten), "Only an admitted signature");
}

/* Section 1.3's positions with arities, and boundaries that apply earlier
 * constructors to data and to positional arguments. */
static void shapes(void) {
    /* V4: Tree(x, y < ω, L : U(x), B : L → U(y)) : U(max(x, y))
     * { sup(l : L, c : Π (b : B(l)). s); }: a position of arity one. */
    cc_entry_id xe = OK(cc_instr_level(k)), ye = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(xe)), uy = universe(lvar(ye));
    cc_judgement_id top = universe(cc_kernel_term(k, CC_LMAX, 0, lvar(xe), lvar(ye), 0, 0));
    cc_entry_id le = extend(ux);
    cc_entry_id arg = extend(var(le));
    cc_entry_id be = extend(OK(cc_instr_pi(k, arg, uy)));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_level_pi(k, ye,
        OK(cc_instr_pi(k, le, OK(cc_instr_pi(k, be, top))))))));
    const cc_entry_id tree_parameters[] = {xe, ye, le, be};
    cc_entry_id s = extend(top);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, tree_parameters, 4, s, 0));
    cc_entry_id l = extend(var(le));
    cc_entry_id b = extend(OK(cc_instr_apply(k, var(be), var(l))));
    cc_entry_id c = extend(OK(cc_instr_pi(k, b, var(s))));
    sig = OK(admit(sig, OK(cc_instr_pi(k, l, OK(cc_instr_pi(k, c, var(s)))))));
    uint32_t tree = tree_signature = OK(cc_instr_signature_close(k, sig));
    assert(signature(tree).level_count == 2 && signature(tree).recorded == 0);
    cc_constructor_info sup = constructor(tree, 0);
    assert(sup.data == 1 && sup.positions == 1 && sup.dimensions == 0);
    /* sup : Π (l : L). Π (c : Π (b : B(l)). s). s over [x, y, L, B, s]: the
     * position's arity applies B, index 2 under l, to the data argument l,
     * index 0. */
    cc_term arity = pi(cc_kernel_term(k, CC_APP, 0, bound(2), bound(0), 0, 0), bound(2));
    assert(sup.type == pi(bound(2), pi(arity, bound(2))));

    /* A3: Quotient(x < ω, A : U(x), R : A → A → U(x)) : set
     * { cls(a : A); eq(a b : A, r : R a b) : Path(s, cls(a), cls(b)); }: a
     * boundary applies an earlier constructor to data. */
    cc_entry_id qa = extend(ux);
    cc_entry_id q1 = extend(var(qa)), q2 = extend(var(qa));
    cc_entry_id qr = extend(OK(cc_instr_pi(k, q1, OK(cc_instr_pi(k, q2, ux)))));
    former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, qa, OK(cc_instr_pi(k, qr, ux))))));
    const cc_entry_id quotient_parameters[] = {xe, qa, qr};
    s = extend(ux);
    sig = OK(cc_instr_signature_begin(k, former, 2, quotient_parameters, 3, s, 0));
    cc_entry_id a = extend(var(qa)), y = extend(var(qa));
    cc_judgement_id cls_type = OK(cc_instr_pi(k, a, var(s)));
    cc_entry_id cls = extend(cls_type);
    sig = OK(cc_instr_signature_constructor(k, sig, cls_type, cls));
    cc_entry_id r = extend(OK(cc_instr_apply(k, OK(cc_instr_apply(k, var(qr), var(a))), var(y))));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id related = OK(cc_instr_path(k, i, var(s), OK(cc_instr_apply(k, var(cls), var(a))),
                                               OK(cc_instr_apply(k, var(cls), var(y)))));
    cc_judgement_id eq_type = OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, y, OK(cc_instr_pi(k, r, related))))));
    sig = OK(admit(sig, eq_type));
    uint32_t quotient = quotient_signature = OK(cc_instr_signature_close(k, sig));
    cc_constructor_info eq = constructor(quotient, 1);
    assert(eq.data == 3 && eq.positions == 0 && eq.dimensions == 1);
    assert(constructor(quotient, 2).generated && constructor(quotient, 2).dimensions == 2);

    /* A15: Cantor : set { leaf; node(f : Nat → s); }, infinitary. */
    cc_judgement_id nat = OK(fixture_nat(k));
    s = extend(former_u0());
    sig = OK(begin_u0(2, s));
    sig = OK(admit(sig, var(s)));
    cc_entry_id f = extend(OK(cc_instr_pi(k, extend(nat), var(s))));
    sig = OK(admit(sig, OK(cc_instr_pi(k, f, var(s)))));
    uint32_t cantor = OK(cc_instr_signature_close(k, sig));
    assert(constructor(cantor, 1).positions == 1 && constructor(cantor, 2).generated);

    /* A16: base; loop : base = base; wrap(p : base = base);
     * fix : wrap(⟨i⟩ loop @ i) = base: a positional argument of path type
     * given as a path abstraction. */
    s = extend(former_u0());
    sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id base = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), base));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    cc_entry_id loop = extend(loop_type);
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, loop));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, extend(loop_type), var(s)));
    cc_entry_id wrap = extend(wrap_type);
    sig = OK(cc_instr_signature_constructor(k, sig, wrap_type, wrap));
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
    sig = OK(admit(sig, fix_type));
    uint32_t wrapped = wrapped_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(wrapped, 2).positions == 1 && constructor(wrapped, 3).dimensions == 1);
    /* fix's stored type is over [s, base, loop, wrap]: its family is the
     * sort, index 3, and its boundary heads are the earlier constructors'
     * indices: wrap(…) applies index 0, and base is index 2. */
    cc_term stored_fix = constructor(wrapped, 3).type;
    assert(kind(stored_fix) == CC_PATH && child(stored_fix, 0) == bound(3) && child(stored_fix, 2) == bound(2));
    assert(kind(child(stored_fix, 1)) == CC_APP && child(child(stored_fix, 1), 0) == bound(0));

    /* Branch(A : U0) { leaf; node(f : A → s); collapse(f : A → s) :
     * node(λ x. f x) = leaf; }: a λ as a positional argument. */
    cc_entry_id pa = extend(former_u0());
    s = extend(former_u0());
    sig = OK(cc_instr_signature_begin(k, OK(cc_instr_pi(k, pa, former_u0())), CC_UNTRUNCATED, &pa, 1, s, 0));
    cc_entry_id leaf = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), leaf));
    cc_entry_id x = extend(var(pa));
    cc_entry_id g = extend(OK(cc_instr_pi(k, x, var(s))));
    cc_judgement_id node_type = OK(cc_instr_pi(k, g, var(s)));
    cc_entry_id node_entry = extend(node_type);
    sig = OK(cc_instr_signature_constructor(k, sig, node_type, node_entry));
    cc_judgement_id expanded = OK(cc_instr_lambda(k, x, OK(cc_instr_apply(k, var(g), var(x)))));
    cc_judgement_id collapse = OK(cc_instr_pi(k, g, OK(cc_instr_path(k, i, var(s),
        OK(cc_instr_apply(k, var(node_entry), expanded)), var(leaf)))));
    sig = OK(admit(sig, collapse));
    uint32_t branch = branch_signature = OK(cc_instr_signature_close(k, sig));
    assert(constructor(branch, 2).positions == 1 && constructor(branch, 2).dimensions == 1);

    /* V25: Tagged(x, y < ω, A : U(x)) : U(max(x, y + 1)) { tag(a : A, B : U(y)); },
     * x erased and y recorded. */
    cc_judgement_id tagged_top = universe(cc_kernel_term(k, CC_LMAX, 0, lvar(xe), lsucc(lvar(ye)), 0, 0));
    cc_entry_id ta = extend(ux);
    former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_level_pi(k, ye, OK(cc_instr_pi(k, ta, tagged_top))))));
    const cc_entry_id tagged_parameters[] = {xe, ye, ta};
    s = extend(tagged_top);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, tagged_parameters, 3, s, 2));
    cc_entry_id tx = extend(var(ta)), tb = extend(uy);
    sig = OK(admit(sig, OK(cc_instr_pi(k, tx, OK(cc_instr_pi(k, tb, var(s)))))));
    uint32_t tagged = tagged_signature = OK(cc_instr_signature_close(k, sig));
    assert(signature(tagged).recorded == 2 && constructor(tagged, 0).data == 2);
}

/* Section 1.4: the types a boundary carries are checked as the boundary is.
 * A path application's annotation, whose endpoints the path step exposes,
 * and a path abstraction's family may hide nothing. */
static void carried_types(void) {
    cc_entry_id s = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id base = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), base));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    cc_entry_id loop = extend(loop_type);
    sig = OK(cc_instr_signature_constructor(k, sig, loop_type, loop));
    /* loop, at Path(i; s, (λ (y : s). y)(base), base): loop @ 0 steps to the redex. */
    cc_entry_id y = extend(var(s));
    cc_judgement_id redex = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, y, var(y))), var(base)));
    cc_judgement_id hidden_type = OK(cc_instr_path(k, i, var(s), redex, var(base)));
    cc_judgement_id unfolded = OK(cc_instr_step(k, OK(cc_instr_refl(k, hidden_type)), 1, (const uint8_t[]){1}, 1,
                                                CC_STEP_BETA));
    cc_judgement_id hidden = OK(cc_instr_convert(k, var(loop), OK(cc_instr_symmetry(k, unfolded))));
    cc_judgement_id at0 = OK(cc_instr_path_apply(k, hidden, 0, 0));
    REJECTS(admit(sig, OK(cc_instr_path(k, j, var(s), at0, var(base)))), "constructor expression");
    /* ⟨j⟩ base, with base at (λ (T : U0). T)(s): its family is no cube. */
    cc_entry_id t = extend(former_u0());
    cc_judgement_id ids = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, t, var(t))), var(s)));
    cc_judgement_id to_s = OK(cc_instr_step(k, OK(cc_instr_refl(k, ids)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id base_ids = OK(cc_instr_convert(k, var(base), OK(cc_instr_symmetry(k, to_s))));
    cc_judgement_id line = OK(cc_instr_path_lambda(k, j, base_ids));
    cc_judgement_id flatten = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_path(k, j, ids, base_ids, base_ids)))),
                                               1, (const uint8_t[]){0}, 1, CC_STEP_BETA));
    line = OK(cc_instr_convert(k, line, flatten));
    cc_judgement_id flat = OK(cc_instr_path(k, j, var(s), var(base), var(base)));
    cc_judgement_id constant = OK(cc_instr_path_lambda(k, j, var(base)));
    REJECTS(admit(sig, OK(cc_instr_path(k, i, flat, line, constant))), "not a cube over the sort");
    /* As written, loop @ 0 is admitted. */
    sig = OK(admit(sig, OK(cc_instr_path(k, j, var(s), OK(cc_instr_path_apply(k, var(loop), 0, 0)), var(base)))));
    OK(cc_instr_signature_close(k, sig));
}

/* Q10: each admission is a new sort, and the gate and a signature's state
 * are checked on every call: none is answered from the derivation cache.
 * Two admissions over the same entries are two sorts. */
static void generative(void) {
    cc_entry_id s = extend(former_u0());
    cc_judgement_id first = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_judgement_id second = OK(begin_u0(CC_UNTRUNCATED, s));
    assert(first != second && term_of(first) != term_of(second));
    cc_kernel_set_extensions(k, 0);
    REJECTS(begin_u0(CC_UNTRUNCATED, s), "switched off");
    cc_kernel_set_extensions(k, CC_EXTENSION_H1);
    cc_entry_id c = extend(var(s));
    cc_judgement_id next = OK(cc_instr_signature_constructor(k, first, var(s), c));
    REJECTS(cc_instr_signature_constructor(k, first, var(s), c), "latest");
    /* Rewriting would copy a signature judgement without its state. */
    REJECTS(cc_instr_step(k, first, 2, NULL, 0, CC_STEP_WHNF), "not rewritten");
    REJECTS(cc_instr_replace(k, first, 2, NULL, 0, OK(cc_instr_refl(k, former_u0())), NULL, 0), "not rewritten");
    OK(cc_instr_signature_close(k, next));
    REJECTS(cc_instr_signature_constructor(k, first, var(s), c), "already admitted");
    /* The constructor's entry stands for it in the first signature only: the
     * second takes it too. */
    OK(cc_instr_signature_close(k, OK(cc_instr_signature_constructor(k, second, var(s), c))));

    /* A prop signature: its squash takes no entry and has no name. It is
     * reported generated, at Π (y z : s). Path(s, y, z) closed over the
     * telescope [s, point], the sort index 1 at the root, and the point's
     * entry is not in it. */
    cc_entry_id own = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(1, own));
    cc_entry_id point = extend(var(own));
    sig = OK(cc_instr_signature_constructor(k, sig, var(own), point));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    cc_constructor_info squash = constructor(index, 1);
    assert(squash.generated && squash.dimensions == 1 && squash.positions == 2 && !squash.data);
    assert(squash.type == pi(bound(1), pi(bound(2), cc_kernel_term(k, CC_PATH, 0, bound(3), bound(1), bound(0), 0))));
    assert(!k->nodes[squash.type].contexts && constructor(index, 0).type == bound(0));

    /* An instance's recorded levels compare by normal form, under binders
     * too: Sort(i; ; [x]) = Sort(i; ; [max(x, x)]), and
     * λ (x < ω). Sort(i; ; [x]) = λ (y < ω). Sort(i; ; [max(y, y)]), where
     * the bound level is index 0 on both sides. */
    cc_entry_id xe = OK(cc_instr_level(k)), ye = OK(cc_instr_level(k));
    cc_term by_x = cc_kernel_term(k, CC_LIST, 0, lvar(xe), 0, 0, 0);
    cc_term by_max = cc_kernel_term(k, CC_LIST, 0, cc_kernel_term(k, CC_LMAX, 0, lvar(xe), lvar(xe), 0, 0), 0, 0, 0);
    cc_term sort_x = cc_kernel_term(k, CC_SORT, index, 0, by_x, 0, 0);
    cc_term sort_max = cc_kernel_term(k, CC_SORT, index, 0, by_max, 0, 0);
    assert(sort_x != sort_max && ck_alpha_equal(k, sort_x, sort_max));
    cc_term by_index = cc_kernel_term(k, CC_LIST, 0, bound(0), 0, 0, 0);
    cc_term by_index_max = cc_kernel_term(k, CC_LIST, 0, cc_kernel_term(k, CC_LMAX, 0, bound(0), bound(0), 0, 0), 0, 0, 0);
    cc_term omega = cc_kernel_term(k, CC_LBOUND, 1, 0, 0, 0, 0);
    cc_term over_x = cc_kernel_term(k, CC_LLAM, 0, omega, cc_kernel_term(k, CC_SORT, index, 0, by_index, 0, 0), 0, 0);
    cc_term over_y = cc_kernel_term(k, CC_LLAM, 0, omega, cc_kernel_term(k, CC_SORT, index, 0, by_index_max, 0, 0), 0, 0);
    assert(over_x != over_y && ck_alpha_equal(k, over_x, over_y));
    /* Another level, another signature, or a longer list differ; so does the
     * bound level against an entry's under the same binder. */
    cc_term by_other = cc_kernel_term(k, CC_LIST, 0, lvar(ye), 0, 0, 0);
    cc_term longer = cc_kernel_term(k, CC_LIST, 0, lvar(xe), by_x, 0, 0);
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index, 0, by_other, 0, 0)));
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index - 1, 0, by_x, 0, 0)));
    assert(!ck_alpha_equal(k, sort_x, cc_kernel_term(k, CC_SORT, index, 0, longer, 0, 0)));
    assert(!ck_alpha_equal(k, over_x, cc_kernel_term(k, CC_LLAM, 0, omega, sort_x, 0, 0)));
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
    cc_judgement_id nat = OK(fixture_nat(k)), zero = OK(fixture_zero(k));
    cc_judgement_id u0 = universe(lconst(0));
    /* N1: loop @ 0 and loop @ 1 are base. */
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
    cc_entry_id xe = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(xe));
    cc_entry_id sa = extend(ux);
    const cc_entry_id susp_parameters[] = {xe, sa};
    cc_entry_id s = extend(ux);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, sa, ux)))),
                                                      CC_UNTRUNCATED, susp_parameters, 2, s, 0));
    cc_entry_id north = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), north));
    cc_entry_id south = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), south));
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_entry_id a = extend(var(sa));
    sig = OK(admit(sig, OK(cc_instr_pi(k, a, OK(cc_instr_path(k, i, var(s), var(north), var(south)))))));
    cc_judgement_id susp = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature = OK(cc_instr_signature_close(k, sig)))),
                                                      nat));
    cc_judgement_id merid0 = OK(cc_instr_apply(k, OK(cc_instr_construct(k, susp, 2)), zero));
    cc_term south_term = term_of(OK(cc_instr_construct(k, susp, 1)));
    cc_judgement_id at1 = OK(cc_instr_path_apply(k, merid0, 0, 1));
    assert(reduct(at1, CC_STEP_PATH) == south_term && reduct(at1, CC_STEP_WHNF) == south_term);

    /* N2: Push(x < ω, C A B : U(x), f : C → A, g : C → B) { inl(a : A); inr(b : B);
     * push(c : C) : inl(f(c)) = inr(g(c)); } at Nat, Nat, Nat, λ n. n and
     * succ: push(0) @ 0 is inl((λ n. n)(0)), which normalizes to inl(0), and
     * push(0) @ 1 normalizes to inr(1). */
    cc_entry_id pc = extend(ux), pa = extend(ux);
    cc_entry_id pb = extend(ux);
    cc_entry_id arg = extend(var(pc));
    cc_entry_id pf = extend(OK(cc_instr_pi(k, arg, var(pa))));
    cc_entry_id pg = extend(OK(cc_instr_pi(k, arg, var(pb))));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, pc, OK(cc_instr_pi(k, pa,
        OK(cc_instr_pi(k, pb, OK(cc_instr_pi(k, pf, OK(cc_instr_pi(k, pg, ux))))))))))));
    const cc_entry_id push_parameters[] = {xe, pc, pa, pb, pf, pg};
    s = extend(ux);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, push_parameters, 6, s, 0));
    cc_entry_id left = extend(var(pa)), right = extend(var(pb));
    cc_judgement_id inl_type = OK(cc_instr_pi(k, left, var(s))), inr_type = OK(cc_instr_pi(k, right, var(s)));
    cc_entry_id inl = extend(inl_type);
    sig = OK(cc_instr_signature_constructor(k, sig, inl_type, inl));
    cc_entry_id inr = extend(inr_type);
    sig = OK(cc_instr_signature_constructor(k, sig, inr_type, inr));
    cc_entry_id c = extend(var(pc));
    cc_judgement_id glued = OK(cc_instr_path(k, i, var(s), OK(cc_instr_apply(k, var(inl), OK(cc_instr_apply(k, var(pf), var(c))))),
                                             OK(cc_instr_apply(k, var(inr), OK(cc_instr_apply(k, var(pg), var(c)))))));
    sig = OK(admit(sig, OK(cc_instr_pi(k, c, glued))));
    uint32_t push_signature = OK(cc_instr_signature_close(k, sig));
    cc_entry_id n = extend(nat);
    cc_judgement_id push = OK(cc_instr_sort_begin(k, push_signature));
    const cc_judgement_id parameters[] = {nat, nat, nat, OK(cc_instr_lambda(k, n, var(n))),
                                          OK(cc_instr_lambda(k, n, OK(fixture_succ(k, var(n)))))};
    for (unsigned p = 0; p < 5; ++p)
        push = OK(cc_instr_sort_parameter(k, push, parameters[p]));
    assert(type_of(push) == term_of(u0));
    cc_judgement_id push0 = OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 2)), zero));
    cc_term inl0 = term_of(OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 0)), zero)));
    cc_term inr1 = term_of(OK(cc_instr_apply(k, OK(cc_instr_construct(k, push, 1)), OK(fixture_succ(k, zero)))));
    assert(reduct(OK(cc_instr_path_apply(k, push0, 0, 0)), CC_STEP_NORMALIZE) == cc_kernel_normalize(k, inl0));
    assert(reduct(OK(cc_instr_path_apply(k, push0, 0, 1)), CC_STEP_NORMALIZE) == cc_kernel_normalize(k, inr1));
    cc_term head = reduct(OK(cc_instr_path_apply(k, push0, 0, 0)), CC_STEP_WHNF);
    assert(kind(head) == CC_APP && child(head, 0) == term_of(OK(cc_instr_construct(k, push, 0))));

    /* N3: the torus's four corners are its point, reached through the square's
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

    /* N3: the open square (surf @ i) @ j, restricted in either order: restricting
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
    cc_entry_id xt = extend(u0);
    cc_judgement_id wrapped = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, xt, var(xt))), loop_type));
    cc_judgement_id unwrap = OK(cc_instr_step(k, OK(cc_instr_refl(k, wrapped)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id at0 = OK(cc_instr_path_apply(k, loop, 0, 0));
    REJECTS(cc_instr_replace(k, at0, 0, (const uint8_t[]){1}, 1, OK(cc_instr_symmetry(k, unwrap)), NULL, 0),
            "annotation is replaced only by a path type");
    /* Inside the annotation, and by another path type, rewriting is allowed. */
    cc_judgement_id same_type = OK(cc_instr_replace(k, at0, 0, (const uint8_t[]){1}, 1, OK(cc_instr_refl(k, loop_type)),
                                                    NULL, 0));
    assert(reduct(same_type, CC_STEP_WHNF) == base);

    /* N4: loop @ (i ∧ j), restricted to j = 0, is loop @ 0, and so base. */
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
 * y_s, z_s : B_s, B_{s+1} = Path(B_s, y_s, z_s), and then at the dimensions;
 * first receives y_0's entry. */
static cc_judgement_id squash_at(cc_judgement_id instance, uint32_t steps, const cc_entry_id *dimensions,
                                 cc_entry_id *first) {
    cc_judgement_id b = instance, applied = OK(cc_instr_construct(k, instance, 1));
    for (uint32_t s = 0; s < steps; ++s) {
        cc_entry_id y = extend(b), z = extend(b);
        if (!s)
            *first = y;
        applied = OK(cc_instr_apply(k, OK(cc_instr_apply(k, applied, var(y))), var(z)));
        b = OK(cc_instr_path(k, OK(cc_instr_dimension(k, 5 + s)), b, var(y), var(z)));
    }
    for (uint32_t s = 0; s < steps; ++s)
        applied = OK(cc_instr_path_apply(k, applied, dimensions[s], 0));
    return applied;
}

/* F4: the Kan structure of declared types (sections 3.3–3.5, 5.5). */
static cc_judgement_id step_judgement(cc_judgement_id value, cc_step_rule rule) {
    return OK(cc_instr_side(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, value)), 1, NULL, 0, rule)), 1));
}

static cc_judgement_id head_judgement(cc_judgement_id value) { return step_judgement(value, CC_STEP_WHNF); }

static void kan(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_entry_id dims[3] = {OK(cc_instr_dimension(k, 1)), OK(cc_instr_dimension(k, 2)), OK(cc_instr_dimension(k, 3))};
    cc_entry_id j = dims[0];

    /* K3: a data sort has no formal composition. K1 in part, with no tubes:
     * comp^i N [] succ(zero) composes succ's argument, and normalizes to
     * succ(zero). */
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    cc_judgement_id one = OK(cc_instr_apply(k, OK(cc_instr_construct(k, n, 1)), OK(cc_instr_construct(k, n, 0))));
    cc_judgement_id at_one = OK(cc_instr_system(k, i, n, one));
    REJECTS(cc_instr_hcomp(k, at_one), "data sort has no formal");
    REJECTS(cc_instr_trans(k, at_one, nowhere()), "data sort has no formal");
    cc_judgement_id composed = OK(cc_instr_comp(k, at_one));
    cc_term head = reduct(composed, CC_STEP_WHNF);
    assert(kind(head) == CC_APP && kind(child(head, 0)) == CC_CON && payload(child(head, 0)) == 1);
    assert(ck_alpha_equal(k, reduct(composed, CC_STEP_NORMALIZE), term_of(one)));
    /* K2 in substance, in N rather than Plus: a neutral tube keeps it
     * neutral: q @ i on j = 0, for q : succ(zero) = m. */
    cc_entry_id m = extend(n);
    cc_entry_id q = extend(OK(cc_instr_path(k, i, n, one, var(m))));
    cc_judgement_id q_i = OK(cc_instr_path_apply(k, var(q), i, 0));
    cc_judgement_id starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, q_i, i, 0)))), 1, NULL, 0,
                                             CC_STEP_PATH));
    cc_judgement_id stuck = OK(cc_instr_comp(k, OK(cc_instr_system_tube(k, at_one, face_at(1, false), q_i, starts))));
    assert(kind(reduct(stuck, CC_STEP_WHNF)) == CC_COMP);
    /* K1, with a tube: comp^i N [j = 0 ↦ succ(zero)] succ(zero) pushes into
     * succ, as the native composition does: succ of the first component of a
     * composition in succ's telescope, with the tube's argument as its tube,
     * which normalizes to succ(zero). */
    cc_judgement_id pushed = OK(cc_instr_comp(k, OK(cc_instr_system_tube(k, at_one, face_at(1, false), one,
                                                                         OK(cc_instr_refl(k, one))))));
    cc_term into_succ = reduct(pushed, CC_STEP_WHNF);
    assert(kind(into_succ) == CC_APP && kind(child(into_succ, 0)) == CC_CON && payload(child(into_succ, 0)) == 1);
    cc_term argument = child(into_succ, 1);
    assert(kind(argument) == CC_FST && kind(child(argument, 0)) == CC_COMP && tubes(child(argument, 0)) == 1);
    assert(ck_alpha_equal(k, reduct(pushed, CC_STEP_NORMALIZE), term_of(one)));

    /* A line of types e : A = B, and Susp(e @ i) along it. */
    cc_judgement_id u0 = universe(lconst(0));
    cc_entry_id ta = extend(u0), tb = extend(u0);
    cc_entry_id e = extend(OK(cc_instr_path(k, i, u0, var(ta), var(tb))));
    cc_judgement_id e_i = OK(cc_instr_path_apply(k, var(e), i, 0));
    cc_judgement_id e_0 = OK(cc_instr_path_apply(k, var(e), 0, 0)), e_1 = OK(cc_instr_path_apply(k, var(e), 0, 1));
    cc_judgement_id line = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_i));
    cc_judgement_id start = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_0));
    cc_judgement_id end = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), e_1));
    cc_judgement_id north = OK(cc_instr_construct(k, start, 0));
    /* North and south at the line's end, normalized: e @ 1 is B. */
    cc_term north_end = reduct(OK(cc_instr_construct(k, end, 0)), CC_STEP_NORMALIZE);
    cc_term south_end = reduct(OK(cc_instr_construct(k, end, 1)), CC_STEP_NORMALIZE);
    /* K9 in substance: a higher sort composes formally, and comp reduces to hcomp. */
    cc_judgement_id formal = OK(cc_instr_hcomp(k, OK(cc_instr_system(k, j, start, north))));
    assert(kind(term_of(formal)) == CC_HCOMP && reduct(formal, CC_STEP_WHNF) == term_of(formal));
    assert(kind(reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, line, north)))), CC_STEP_WHNF)) == CC_HCOMP);
    /* K9 in substance, in Susp rather than S1: comp along a constant line is
     * an hcomp of the base moved along that line, which is north again. */
    cc_term along_constant = reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, start, north)))), CC_STEP_WHNF);
    assert(kind(along_constant) == CC_HCOMP);
    assert(ck_alpha_equal(k, normal(child(along_constant, 2)), reduct(north, CC_STEP_NORMALIZE)));
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
    /* K6 in part, along a line of types rather than ua: merid(a) @ j along the
     * line: an hcomp corrected on j = 0 and j = 1, whose
     * faces are the transports of north and south. */
    cc_entry_id a = extend(var(ta));
    cc_judgement_id to_a = OK(cc_instr_step(k, OK(cc_instr_refl(k, e_0)), 1, NULL, 0, CC_STEP_PATH));
    cc_judgement_id a0 = OK(cc_instr_convert(k, var(a), OK(cc_instr_symmetry(k, to_a))));
    cc_judgement_id merid = OK(cc_instr_path_apply(k, OK(cc_instr_apply(k, OK(cc_instr_construct(k, start, 2)), a0)), j, 0));
    cc_judgement_id transported = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, merid)), nowhere()));
    cc_term corrected = reduct(transported, CC_STEP_WHNF);
    assert(kind(corrected) == CC_HCOMP && tubes(corrected) == 3);
    cc_term base = child(corrected, 2);
    assert(kind(base) == CC_PAPP && kind(child(base, 0)) == CC_APP && payload(child(child(base, 0), 0)) == 2);
    /* K5 in substance: its argument is a moved along e @ i, derived independently, and each
     * wall starts on the base. */
    cc_term moved_a = reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, e_i, a0)))), CC_STEP_NORMALIZE);
    assert(ck_alpha_equal(k, normal(constructor_argument(base, 0, 1)), moved_a));
    walls_start_on_base(corrected);
    assert(ck_alpha_equal(k, commutes(transported, j, 0), north_end));
    assert(ck_alpha_equal(k, commutes(transported, j, 1), south_end));
    /* K4 in substance, in Susp rather than S1: an hcomp whose tube, on a face
     * that holds, runs from north to south is the tube's end, south, not its
     * base. */
    cc_judgement_id merid_starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, merid, j, 0)))), 1,
                                                    NULL, 0, CC_STEP_PATH));
    cc_judgement_id to_south = OK(cc_instr_hcomp(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, j, start, north)),
                                                                            always, merid, merid_starts))));
    cc_term south_start = reduct(OK(cc_instr_construct(k, start, 1)), CC_STEP_NORMALIZE);
    assert(!ck_alpha_equal(k, south_start, reduct(north, CC_STEP_NORMALIZE)));
    assert(ck_alpha_equal(k, normal(reduct(to_south, CC_STEP_FACE)), south_start));
    /* CP09: transport a formal box before its tube face becomes true, or
     * transport the tube's endpoint after restricting the box. */
    cc_judgement_id partial_box = OK(cc_instr_hcomp(k, OK(cc_instr_system_tube(k,
        OK(cc_instr_system(k, j, start, north)), face_at(2, true), merid, merid_starts))));
    cc_judgement_id moved_partial = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, partial_box)), nowhere()));
    cc_judgement_id moved_head = head_judgement(moved_partial);
    assert(kind(term_of(moved_head)) == CC_HCOMP);
    cc_judgement_id restricted_box = OK(cc_instr_endpoint(k, partial_box, dims[1], 1));
    cc_judgement_id restricted_then_moved = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, line, restricted_box)), nowhere()));
    assert(ck_alpha_equal(k, reduct(OK(cc_instr_endpoint(k, moved_head, dims[1], 1)), CC_STEP_NORMALIZE),
                          reduct(restricted_then_moved, CC_STEP_NORMALIZE)));
    assert(ck_alpha_equal(k, reduct(restricted_then_moved, CC_STEP_NORMALIZE), south_end));

    /* K7 in substance, with a set truncation's squash rather than Quotient's:
     * the squash of set (two dimensions) and of trunc(1) (three), along the
     * line: 2d walls, and each face commutes with transport. */
    const uint32_t truncated[2] = {set_signature, groupoid_signature};
    for (uint32_t t = 0; t < 2; ++t) {
        uint32_t steps = t + 2;
        cc_judgement_id from = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, truncated[t])), e_0));
        cc_judgement_id along = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, truncated[t])), e_i));
        cc_entry_id first = 0;
        cc_judgement_id squash = squash_at(from, steps, dims, &first);
        cc_judgement_id carried = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, along, squash)), nowhere()));
        cc_term box = reduct(carried, CC_STEP_WHNF);
        assert(kind(box) == CC_HCOMP && tubes(box) == 2 * steps + 1);
        walls_start_on_base(box);
        /* CP07: different correction walls meet at a corner. Each order
         * restricts one of the first two dimensions and reduces, so Face
         * selects that dimension's wall, before it restricts the other: the
         * two branches take different walls, and must join, on the 3-cube
         * too. Restricting both first would give alpha-equal peaks. */
        for (unsigned a_end = 0; a_end < 2; ++a_end)
            for (unsigned b_end = 0; b_end < 2; ++b_end) {
                ck_standalone(k);
                cc_term wall_a = normal(ck_endpoint_term(k, box, 1, a_end));
                ck_standalone(k);
                cc_term wall_b = normal(ck_endpoint_term(k, box, 2, b_end));
                assert(!ck_alpha_equal(k, wall_a, wall_b));
                ck_standalone(k);
                cc_term ab = ck_endpoint_term(k, wall_a, 2, b_end);
                ck_standalone(k);
                cc_term ba = ck_endpoint_term(k, wall_b, 1, a_end);
                assert(!ck_alpha_equal(k, ab, ba));
                assert(ck_alpha_equal(k, normal(ab), normal(ba)));
            }
        /* The first argument, y_0, is moved along the line. */
        cc_judgement_id y0 = var(first);
        cc_term moved_y0 = reduct(OK(cc_instr_comp(k, OK(cc_instr_system(k, i, along, y0)))), CC_STEP_NORMALIZE);
        assert(ck_alpha_equal(k, normal(constructor_argument(child(box, 2), 0, 2 * steps)), moved_y0));
        for (uint32_t l = 0; l < steps; ++l)
            for (unsigned end_point = 0; end_point < 2; ++end_point)
                commutes(carried, dims[l], end_point);
    }
}

/* K10 and K11, the property tests of Lemma H2 (10.4): random closed
 * constructor terms of Susp, Torus and Quotient, their path constructors at
 * random formulas over two dimensions, moved along random lines of their
 * parameters. K10: restricting the transport to a face of those dimensions
 * is transporting the restricted term, (transp u)[r = ε] ≡ transp(u[r = ε]).
 * K11: transport along a constant line, at φ = 1, is the identity. The draws
 * are from a fixed seed, so a failure is the same on every run. */
static uint64_t property_state = UINT64_C(0x9E3779B97F4A7C15);
static uint32_t pick(uint32_t bound) {
    property_state ^= property_state << 13;
    property_state ^= property_state >> 7;
    property_state ^= property_state << 17;
    return (uint32_t)(property_state % bound);
}

/* A random interval formula over the dimensions 1 and 2: an endpoint, a
 * dimension or its reversal, or a meet or join of two such. */
static void random_interval(cc_formula *out, unsigned depth) {
    cc_init(out, CC_INTERVAL);
    unsigned form = depth ? pick(6) : pick(4);
    if (form < 2)
        assert((form ? cc_one(out) : cc_zero(out)) == CC_OK);
    else if (form < 4) {
        unsigned dimension = 1 + pick(2);
        assert(cc_generator(out, dimension, form == 2) == CC_OK);
    }
    else {
        cc_formula left, right;
        random_interval(&left, depth - 1);
        random_interval(&right, depth - 1);
        assert((form == 4 ? cc_meet(out, &left, &right) : cc_join(out, &left, &right)) == CC_OK);
        cc_clear(&left);
        cc_clear(&right);
    }
}
static cc_formula_id random_formula(void) {
    cc_formula f;
    random_interval(&f, 2);
    cc_formula_id id = cc_kernel_formula(k, &f);
    cc_clear(&f);
    return id;
}

/* A line of the parameter A(i) over the dimension i, its type at 0, and an
 * element of that type. */
typedef struct { cc_judgement_id along, start, element; } property_line;

/* An instance over the line's type T: Susp(T), Torus, or Quotient(T, R) with
 * R x y = Nat, x and y bound by new entries; `relation` receives R. */
static cc_judgement_id property_instance(unsigned sort, cc_judgement_id type, cc_judgement_id *relation) {
    if (sort == 1)
        return OK(cc_instr_sort_begin(k, torus_signature));
    if (sort == 0)
        return OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, susp_signature)), type));
    cc_entry_id x = extend(type), y = extend(type);
    *relation = OK(cc_instr_lambda(k, x, OK(cc_instr_lambda(k, y, OK(fixture_nat(k))))));
    return OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, quotient_signature)), type)),
                                      *relation));
}

/* A random constructor term of an instance at the line's start: a point
 * constructor, or a path constructor at random formulas, which `path`
 * counts. */
static cc_judgement_id property_term(unsigned sort, cc_judgement_id instance, cc_judgement_id relation, cc_judgement_id element,
                                     unsigned *path) {
    if (sort == 0) {
        unsigned c = pick(3);
        if (c < 2)
            return OK(cc_instr_construct(k, instance, c));
        ++*path;
        return OK(cc_instr_path_at(k, OK(cc_instr_apply(k, OK(cc_instr_construct(k, instance, 2)), element)), random_formula()));
    }
    if (sort == 1) {
        unsigned c = pick(4);
        cc_judgement_id made = OK(cc_instr_construct(k, instance, c));
        if (!c)
            return made;
        ++*path;
        cc_judgement_id at = OK(cc_instr_path_at(k, made, random_formula()));
        return c == 3 ? OK(cc_instr_path_at(k, at, random_formula())) : at;
    }
    cc_judgement_id cls = OK(cc_instr_apply(k, OK(cc_instr_construct(k, instance, 0)), element));
    if (pick(2))
        return cls;
    ++*path;
    /* eq(a, a, 0), where R a a is Nat by its weak head. */
    cc_judgement_id eq = OK(cc_instr_apply(k, OK(cc_instr_apply(k, OK(cc_instr_construct(k, instance, 1)), element)), element));
    cc_judgement_id related = OK(cc_instr_apply(k, OK(cc_instr_apply(k, relation, element)), element));
    cc_judgement_id is_nat = OK(cc_instr_step(k, OK(cc_instr_refl(k, related)), 1, NULL, 0, CC_STEP_WHNF));
    cc_judgement_id witness = OK(cc_instr_convert(k, OK(fixture_zero(k)), OK(cc_instr_symmetry(k, is_nat))));
    return OK(cc_instr_path_at(k, OK(cc_instr_apply(k, eq, witness)), random_formula()));
}

static void transport_properties(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_entry_id dims[2] = {OK(cc_instr_dimension(k, 1)), OK(cc_instr_dimension(k, 2))};
    cc_judgement_id u0 = universe(lconst(0));
    cc_entry_id ta = extend(u0), tb = extend(u0);
    cc_entry_id e = extend(OK(cc_instr_path(k, i, u0, var(ta), var(tb))));
    cc_entry_id xa = extend(var(ta)), xb = extend(var(tb));
    /* The lines: along e, from A; along e reversed, from B; and constant at A. */
    cc_formula flipped;
    cc_init(&flipped, CC_INTERVAL);
    assert(cc_generator(&flipped, 0, false) == CC_OK);
    cc_formula_id not_i = cc_kernel_formula(k, &flipped);
    cc_clear(&flipped);
    property_line lines[3];
    for (unsigned l = 0; l < 2; ++l) {
        cc_judgement_id start = OK(cc_instr_path_apply(k, var(e), 0, l));
        cc_judgement_id is_end = OK(cc_instr_step(k, OK(cc_instr_refl(k, start)), 1, NULL, 0, CC_STEP_PATH));
        lines[l] = (property_line){l ? OK(cc_instr_path_at(k, var(e), not_i)) : OK(cc_instr_path_apply(k, var(e), i, 0)), start,
                                   OK(cc_instr_convert(k, var(l ? xb : xa), OK(cc_instr_symmetry(k, is_end))))};
    }
    lines[2] = (property_line){var(ta), var(ta), var(xa)};
    cc_formula top;
    cc_init(&top, CC_FACE);
    assert(cc_one(&top) == CC_OK);
    cc_formula_id always = cc_kernel_formula(k, &top);
    cc_clear(&top);
    enum { TERMS = 96 };
    unsigned restrictions = 0, drawn[3][3] = {{0}}, paths[3] = {0};
    for (unsigned n = 0; n < TERMS; ++n) {
        unsigned sort = pick(3), l = sort == 1 ? 2 : pick(3);
        ++drawn[sort][l];
        cc_judgement_id relation = 0, unused = 0;
        cc_judgement_id along = property_instance(sort, lines[l].along, &unused);
        cc_judgement_id start = property_instance(sort, lines[l].start, &relation);
        cc_judgement_id u = property_term(sort, start, relation, lines[l].element, &paths[sort]);
        /* K10, at each face of the two dimensions: the transport restricted,
         * as it is and as the weak head it reduces to (the hcomp of 3.5,
         * case 2, for a path constructor, whose walls then decide), is the
         * transport of the term restricted. */
        cc_judgement_id moved = OK(cc_instr_trans(k, OK(cc_instr_system(k, i, along, u)), nowhere()));
        cc_judgement_id head = OK(cc_instr_side(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, moved)), 1, NULL, 0, CC_STEP_WHNF)), 1));
        for (unsigned d = 0; d < 2; ++d)
            for (unsigned end = 0; end < 2; ++end, ++restrictions) {
                cc_judgement_id face = OK(cc_instr_endpoint(k, u, dims[d], end));
                cc_term transported =
                    reduct(OK(cc_instr_trans(k, OK(cc_instr_system(k, i, along, face)), nowhere())), CC_STEP_NORMALIZE);
                cc_term restricted = reduct(OK(cc_instr_endpoint(k, moved, dims[d], end)), CC_STEP_NORMALIZE);
                cc_term through = reduct(OK(cc_instr_endpoint(k, head, dims[d], end)), CC_STEP_NORMALIZE);
                if (!ck_alpha_equal(k, restricted, transported) || !ck_alpha_equal(k, through, transported))
                    fprintf(stderr, "K10 fails for term %u: sort %u, line %u, dimension %u at %u\n", n, sort, l, d + 1, end);
                assert(ck_alpha_equal(k, restricted, transported) && ck_alpha_equal(k, through, transported));
            }
        /* K11, along the constant line of the term's own instance: at φ = 1
         * the transport is the term (Face). Where φ is the face d = 1, the
         * weak head the generated rules give, restricted to it, is the term
         * restricted too: the rules agree with Face. */
        if (l == 2) {
            cc_judgement_id held = OK(cc_instr_trans(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, start, u)), always, u,
                                                                                OK(cc_instr_refl(k, u)))), always));
            assert(ck_alpha_equal(k, reduct(held, CC_STEP_NORMALIZE), normal(term_of(u))));
            unsigned d = pick(2);
            cc_formula_id phi = face_at(1 + d, true);
            cc_judgement_id on_face = OK(cc_instr_endpoint(k, u, dims[d], 1));
            cc_judgement_id partial = OK(cc_instr_trans(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, start, u)), phi, on_face,
                                                                                   OK(cc_instr_refl(k, on_face)))), phi));
            cc_judgement_id reduced = OK(cc_instr_side(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, partial)), 1, NULL, 0, CC_STEP_WHNF)), 1));
            cc_term there = normal(term_of(on_face));
            assert(ck_alpha_equal(k, reduct(OK(cc_instr_endpoint(k, reduced, dims[d], 1)), CC_STEP_NORMALIZE), there));
            assert(ck_alpha_equal(k, reduct(OK(cc_instr_endpoint(k, partial, dims[d], 1)), CC_STEP_NORMALIZE), there));
        }
    }
    /* The draws reach every sort along each of its lines, and every sort's
     * path constructors. */
    for (unsigned sort = 0; sort < 3; ++sort) {
        assert(paths[sort] > 0);
        for (unsigned l = 0; l < 3; ++l)
            assert(drawn[sort][l] > 0 || (sort == 1 && l != 2));
    }
    printf("transport properties (K10, K11): %u random terms, %u restrictions commute\n", (unsigned)TERMS, restrictions);
}

/* A motive P : Π (z : I). U0, as a variable. */
static cc_entry_id motive_over(cc_judgement_id instance) {
    cc_entry_id z = extend(instance);
    return extend(OK(cc_instr_pi(k, z, universe(lconst(0)))));
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

/* A point of type T as a term of `type`, where `type` reaches T by path
 * steps at the given positions, in order: an endpoint or family a driver
 * converts to state a clause type. */
static cc_judgement_id as_type(cc_judgement_id point, cc_judgement_id type, unsigned count,
                               const uint8_t positions[][3], const size_t *depths) {
    cc_judgement_id equal = OK(cc_instr_refl(k, type));
    for (unsigned n = 0; n < count; ++n)
        equal = OK(cc_instr_step(k, equal, 1, positions[n], depths[n], CC_STEP_PATH));
    return OK(cc_instr_convert(k, point, OK(cc_instr_symmetry(k, equal))));
}

/* A judgement whose type takes one path step at the given position. */
static cc_judgement_id type_step(cc_judgement_id typing, const uint8_t *position, size_t depth) {
    return OK(cc_instr_step(k, typing, 2, position, depth, CC_STEP_PATH));
}

/* The structural and explicit Face steps take different paths from each
 * peak; normalizing only their reducts does not depend on whnf's ordering.
 * CP identifiers refer to docs/roadmaps/hott/h1-critical-pairs.md. */
static void joins(cc_judgement_id left, cc_judgement_id right) {
    assert(ck_alpha_equal(k, reduct(left, CC_STEP_NORMALIZE), reduct(right, CC_STEP_NORMALIZE)));
}

static void critical_composition_pairs(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_formula_id face = face_at(1, true);
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    cc_judgement_id zero = OK(cc_instr_construct(k, n, 0)), succ = OK(cc_instr_construct(k, n, 1));
    cc_judgement_id one = OK(cc_instr_apply(k, succ, zero));
    cc_entry_id m = extend(n);
    cc_entry_id q = extend(OK(cc_instr_path(k, i, n, zero, var(m))));
    cc_judgement_id tube = OK(cc_instr_apply(k, succ, OK(cc_instr_path_apply(k, var(q), i, 0))));
    cc_judgement_id starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, tube, i, 0)))),
                                             1, (const uint8_t[]){1}, 1, CC_STEP_PATH));
    cc_judgement_id end = OK(cc_instr_apply(k, succ, var(m)));
    assert(!ck_alpha_equal(k, normal(term_of(one)), normal(term_of(end))));
    cc_judgement_id system = OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, n, one)), face, tube, starts));
    cc_judgement_id comp = OK(cc_instr_comp(k, system));
    /* CP04: push into succ first, or make the tube's face hold first. */
    cc_judgement_id pushed = head_judgement(comp);
    assert(kind(term_of(pushed)) == CC_APP);
    joins(OK(cc_instr_endpoint(k, pushed, j, 1)), step_judgement(OK(cc_instr_endpoint(k, comp, j, 1)), CC_STEP_FACE));
    joins(OK(cc_instr_endpoint(k, pushed, j, 1)), end);

    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_judgement_id base = OK(cc_instr_construct(k, s1, 0));
    cc_entry_id x = extend(s1);
    cc_entry_id p = extend(OK(cc_instr_path(k, i, s1, base, var(x))));
    tube = OK(cc_instr_path_apply(k, var(p), i, 0));
    starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, tube, i, 0)))),
                             1, NULL, 0, CC_STEP_PATH));
    assert(!ck_alpha_equal(k, normal(term_of(base)), normal(term_of(var(x)))));
    system = OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, s1, base)), face, tube, starts));
    comp = OK(cc_instr_comp(k, system));
    /* CP05: turn a higher composition into hcomp first, or take Face first. */
    cc_judgement_id formal = head_judgement(comp);
    assert(kind(term_of(formal)) == CC_HCOMP);
    joins(OK(cc_instr_endpoint(k, formal, j, 1)), step_judgement(OK(cc_instr_endpoint(k, comp, j, 1)), CC_STEP_FACE));
    joins(OK(cc_instr_endpoint(k, formal, j, 1)), var(x));
    /* CP10: deleting an empty tube and selecting a held tube commute. The
     * surviving tube is a path, so the join checks its end, too. */
    system = OK(cc_instr_system_tube(k, OK(cc_instr_system(k, i, s1, base)), nowhere(), base, 0));
    system = OK(cc_instr_system_tube(k, system, face, tube, starts));
    cc_judgement_id box = OK(cc_instr_hcomp(k, system));
    assert(tubes(term_of(box)) == 2);
    cc_judgement_id dropped = head_judgement(box);
    assert(tubes(term_of(dropped)) == 1);
    joins(OK(cc_instr_endpoint(k, dropped, j, 1)), step_judgement(OK(cc_instr_endpoint(k, box, j, 1)), CC_STEP_FACE));
    joins(OK(cc_instr_endpoint(k, dropped, j, 1)), var(x));
}

/* F5: elimination (sections 3.6, 3.7, 5.6). */
static void elimination(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id nat = OK(fixture_nat(k));

    /* N: P(zero), then Π (n : N). Π (n̄ : P(n)). P(succ(n)). */
    cc_judgement_id n = OK(cc_instr_sort_begin(k, nat_signature));
    cc_judgement_id zero = OK(cc_instr_construct(k, n, 0)), succ = OK(cc_instr_construct(k, n, 1));
    cc_entry_id p = motive_over(n);
    cc_judgement_id opened = OK(cc_instr_eliminator(k, var(p)));
    assert(info(opened).kind == 6 && type_of(opened) == term_of(at(p, zero)) && !info(opened).other);
    REJECTS(cc_instr_eliminator_close(k, opened), "lacks a clause");
    /* E6: a clause of the wrong type. */
    REJECTS(cc_instr_eliminator_clause(k, opened, OK(fixture_zero(k))), "clause type");
    cc_entry_id pz = extend(at(p, zero));
    cc_judgement_id after_zero = OK(cc_instr_eliminator_clause(k, opened, var(pz)));
    cc_entry_id m = extend(n), h = extend(at(p, var(m)));
    cc_judgement_id step_type = OK(cc_instr_pi(k, m, OK(cc_instr_pi(k, h, at(p, OK(cc_instr_apply(k, succ, var(m))))))));
    assert(ck_alpha_equal(k, term_of(step_type), type_of(after_zero)));
    cc_entry_id ps = extend(step_type);
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
    cc_entry_id plain = extend(OK(cc_instr_unit(k)));
    REJECTS(cc_instr_eliminator(k, OK(cc_instr_lambda(k, plain, nat))), "instance of a declared type");

    /* The circle: loop's clause is PathP(i. P(loop @ i), pb, pb); E7: one
     * whose ends are not the base clause is refused. */
    cc_judgement_id s1 = OK(cc_instr_sort_begin(k, circle_signature));
    cc_judgement_id base = OK(cc_instr_construct(k, s1, 0)), loop = OK(cc_instr_construct(k, s1, 1));
    cc_entry_id q = motive_over(s1);
    cc_entry_id pb = extend(at(q, base)), other = extend(at(q, base));
    cc_judgement_id circle = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(q))), var(pb)));
    cc_judgement_id loop_type = path_over(q, loop, i, var(pb));
    assert(term_of(loop_type) == type_of(circle));
    REJECTS(cc_instr_eliminator_clause(k, circle, var(extend(path_over(q, loop, i, var(other))))),
            "clause type");
    cc_entry_id pl = extend(loop_type);
    cc_judgement_id circle_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, circle, var(pl)))));
    /* CP01: elim(loop @ j) is pl @ j; at either endpoint both orders give
     * pb. Take the inner boundary explicitly, independently of Iota. */
    cc_term on_loop = iota_of(OK(cc_instr_apply(k, circle_elim, OK(cc_instr_path_apply(k, loop, j, 0)))));
    assert(kind(on_loop) == CC_PAPP && child(on_loop, 0) == term_of(var(pl)) && kind(child(on_loop, 1)) == CC_PATH);
    cc_judgement_id at_zero = OK(cc_instr_apply(k, circle_elim, OK(cc_instr_path_apply(k, loop, 0, 0))));
    assert(reduct(at_zero, CC_STEP_WHNF) == term_of(var(pb)));
    cc_judgement_id by_iota = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_zero)), 1, NULL, 0, CC_STEP_IOTA));
    assert(info(OK(cc_instr_step(k, by_iota, 1, NULL, 0, CC_STEP_PATH))).other == term_of(var(pb)));
    for (unsigned end_point = 0; end_point < 2; ++end_point) {
        cc_judgement_id peak = OK(cc_instr_apply(k, circle_elim, OK(cc_instr_path_apply(k, loop, 0, end_point))));
        cc_judgement_id outer = OK(cc_instr_side(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, peak)), 1,
                                                    NULL, 0, CC_STEP_IOTA)), 1));
        cc_judgement_id inner = OK(cc_instr_side(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, peak)), 1,
                                                    (const uint8_t[]){1}, 1, CC_STEP_PATH)), 1));
        joins(outer, inner);
        joins(outer, var(pb));
    }
    /* E5: elim(hcomp) computes by Whnf, as a composition in the motive. */
    cc_judgement_id box = OK(cc_instr_hcomp(k, OK(cc_instr_system(k, j, s1, base))));
    assert(kind(reduct(OK(cc_instr_apply(k, circle_elim, box)), CC_STEP_WHNF)) == CC_COMP);
    /* CP03: eliminate the formal box before making its tube face hold, or
     * restrict the box first. The tube is loop @ j, not a constant tube;
     * the motive and its loop clause are arbitrary dependent variables. */
    cc_entry_id r = OK(cc_instr_dimension(k, 2));
    cc_judgement_id tube = OK(cc_instr_path_apply(k, loop, j, 0));
    cc_judgement_id starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_endpoint(k, tube, j, 0)))),
                                             1, NULL, 0, CC_STEP_PATH));
    box = OK(cc_instr_hcomp(k, OK(cc_instr_system_tube(k, OK(cc_instr_system(k, j, s1, base)), face_at(2, true),
                                                      tube, starts))));
    cc_judgement_id peak = OK(cc_instr_apply(k, circle_elim, box));
    cc_judgement_id outer = head_judgement(peak);
    assert(kind(term_of(outer)) == CC_COMP);
    cc_judgement_id on_face = OK(cc_instr_apply(k, circle_elim,
        step_judgement(OK(cc_instr_endpoint(k, box, r, 1)), CC_STEP_FACE)));
    joins(OK(cc_instr_endpoint(k, outer, r, 1)), on_face);
    joins(on_face, var(pb));

    /* E3: the prop squash: Π (y z : T). Π (ȳ : P(y)) (z̄ : P(z)). PathP(i. …, ȳ, z̄):
     * its boundary shows the positions y, z by their displayed variables,
     * ȳ and z̄, indices 1 and 0 under the four binders; ȳ's type applies P
     * to y, index 1 under y and z. */
    cc_judgement_id tr = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), nat));
    cc_entry_id t = motive_over(tr);
    cc_entry_id a = extend(nat);
    cc_judgement_id point_at = OK(cc_instr_apply(k, OK(cc_instr_construct(k, tr, 0)), var(a)));
    cc_entry_id pp = extend(OK(cc_instr_pi(k, a, at(t, point_at))));
    cc_term squash = type_of(OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(t))), var(pp))));
    cc_term y_bar = child(child(squash, 1), 1), z_bar = child(y_bar, 1), inner = child(z_bar, 1);
    assert(kind(inner) == CC_PATH && child(inner, 1) == bound(1) && child(inner, 2) == bound(0));
    assert(child(y_bar, 0) == cc_kernel_term(k, CC_APP, 0, term_of(var(t)), bound(1), 0, 0));
    /* E9: Trunc(Nat)'s eliminator, with both clauses, is over its own
     * instance: a term of Trunc(Unit) is refused. The squash clause is
     * derived here as the kernel reports it. */
    cc_entry_id ty = extend(tr), tz = extend(tr);
    const cc_entry_id bars[2] = {extend(at(t, var(ty))), extend(at(t, var(tz)))};
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
        var(extend(squash_type))))));
    OK(cc_instr_apply(k, tr_elim, point_at));
    cc_judgement_id unit_tr = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, trunc_signature)), OK(cc_instr_unit(k))));
    REJECTS(cc_instr_apply(k, tr_elim, OK(cc_instr_apply(k, OK(cc_instr_construct(k, unit_tr, 0)), OK(cc_instr_point(k))))),
            "wrong type");
    /* E10: a motive into UU0 for the circle, P : Π (z : S1). U(ω), with its
     * two clauses. */
    cc_entry_id wide = extend(OK(cc_instr_pi(k, extend(s1), universe(tier1(0)))));
    cc_entry_id wide_base = extend(at(wide, base));
    cc_entry_id wide_loop = extend(path_over(wide, loop, i, var(wide_base)));
    cc_judgement_id wide_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator(k, var(wide))), var(wide_base))), var(wide_loop)))));
    assert(kind(type_of(wide_elim)) == CC_PI);

    /* Tree(Nat, λ n. Nat): sup's position has an arity, so q̄ is λ b. elim(c(b)). */
    cc_entry_id nb = extend(nat);
    cc_judgement_id family = OK(cc_instr_lambda(k, nb, nat));
    cc_judgement_id tree = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k,
        OK(cc_instr_sort_begin(k, tree_signature)), nat)), family));
    cc_entry_id w = motive_over(tree);
    cc_entry_id l = extend(nat);
    cc_entry_id b = extend(OK(cc_instr_apply(k, family, var(l))));
    cc_entry_id c = extend(OK(cc_instr_pi(k, b, tree)));
    cc_entry_id c_bar = extend(OK(cc_instr_pi(k, b, at(w, OK(cc_instr_apply(k, var(c), var(b)))))));
    cc_judgement_id sup = OK(cc_instr_construct(k, tree, 0));
    cc_judgement_id sup_type = OK(cc_instr_pi(k, l, OK(cc_instr_pi(k, c, OK(cc_instr_pi(k, c_bar,
        at(w, OK(cc_instr_apply(k, OK(cc_instr_apply(k, sup, var(l))), var(c))))))))));
    cc_judgement_id tree_open = OK(cc_instr_eliminator(k, var(w)));
    assert(ck_alpha_equal(k, type_of(tree_open), term_of(sup_type)));
    cc_entry_id ms = extend(sup_type);
    cc_judgement_id tree_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, tree_open, var(ms)))));
    cc_term on_sup = iota_of(OK(cc_instr_apply(k, tree_elim, OK(cc_instr_apply(k, OK(cc_instr_apply(k, sup, var(l))),
                                                                                  var(c))))));
    cc_term lifted = child(on_sup, 1);
    assert(kind(lifted) == CC_LAM && kind(child(lifted, 1)) == CC_APP && child(child(lifted, 1), 0) == term_of(tree_elim));
    assert(child(child(lifted, 1), 1) == cc_kernel_term(k, CC_APP, 0, term_of(var(c)), bound(0), 0, 0));

    /* A16: wrap's position is a path, displayed as a PathP between base's
     * clause; fix's boundary wrap(⟨i⟩ loop @ i) is shown as
     * m_wrap(⟨i⟩ loop @ i, ⟨i⟩ m_loop @ i). */
    cc_judgement_id wr = OK(cc_instr_sort_begin(k, wrapped_signature));
    cc_judgement_id wbase = OK(cc_instr_construct(k, wr, 0)), wloop = OK(cc_instr_construct(k, wr, 1));
    cc_entry_id v = motive_over(wr);
    cc_entry_id pv = extend(at(v, wbase));
    cc_entry_id pw = extend(path_over(v, wloop, i, var(pv)));
    cc_judgement_id wrapped = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator(k, var(v))), var(pv))), var(pw)));
    cc_term wrap_clause = type_of(wrapped);
    cc_term path_bar = child(child(wrap_clause, 1), 0);
    assert(kind(path_bar) == CC_PATH && child(path_bar, 1) == term_of(var(pv)) && child(path_bar, 2) == term_of(var(pv)));
    cc_entry_id pw_var = extend(wr);
    (void)pw_var;
    /* A clause for wrap, as a variable of the reported type's shape. */
    cc_entry_id loop_var = extend(OK(cc_instr_path(k, i, wr, wbase, wbase)));
    cc_entry_id loop_bar = extend(path_over(v, var(loop_var), i, var(pv)));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, loop_var, OK(cc_instr_pi(k, loop_bar,
        at(v, OK(cc_instr_apply(k, OK(cc_instr_construct(k, wr, 2)), var(loop_var))))))));
    assert(ck_alpha_equal(k, term_of(wrap_type), wrap_clause));
    cc_entry_id mw = extend(wrap_type);
    cc_term fix_clause = type_of(OK(cc_instr_eliminator_clause(k, wrapped, var(mw))));
    cc_term left = child(fix_clause, 1);
    assert(kind(fix_clause) == CC_PATH && kind(left) == CC_APP && child(child(left, 0), 0) == term_of(var(mw)));
    cc_term shown_line = child(left, 1);
    assert(kind(shown_line) == CC_PLAM && kind(child(shown_line, 1)) == CC_PAPP &&
           child(child(shown_line, 1), 0) == term_of(var(pw)));
    assert(child(fix_clause, 2) == term_of(var(pv)));

    /* CP01 at fix, whose boundary gives wrap a path abstraction over an
     * earlier constructor. Its clause is a variable of the type a driver
     * derives, which must be the reported one; elim(fix @ 0) then reduces
     * by Iota and the path step through the displayed annotation, or by the
     * boundary and Iota, and the two join. */
    cc_judgement_id wfix = OK(cc_instr_construct(k, wr, 3));
    cc_judgement_id wline = OK(cc_instr_path_lambda(k, i, OK(cc_instr_path_apply(k, wloop, i, 0))));
    wline = type_step(type_step(wline, (const uint8_t[]){1}, 1), (const uint8_t[]){2}, 1);
    cc_judgement_id line_ends[2];
    for (unsigned e = 0; e < 2; ++e)
        line_ends[e] = as_type(var(pv), at(v, OK(cc_instr_path_apply(k, wline, 0, e))), 2,
                               (const uint8_t[][3]){{1}, {1}}, (const size_t[]){1, 1});
    cc_judgement_id over_line = OK(cc_instr_path(k, i, at(v, OK(cc_instr_path_apply(k, wline, i, 0))), line_ends[0],
                                                 line_ends[1]));
    cc_judgement_id lifted_loop = OK(cc_instr_path_lambda(k, i, OK(cc_instr_path_apply(k, var(pw), i, 0))));
    lifted_loop = type_step(type_step(lifted_loop, (const uint8_t[]){1}, 1), (const uint8_t[]){2}, 1);
    lifted_loop = as_type(lifted_loop, over_line, 1, (const uint8_t[][3]){{0, 1}}, (const size_t[]){2});
    cc_judgement_id shown = OK(cc_instr_apply(k, OK(cc_instr_apply(k, var(mw), wline)), lifted_loop));
    cc_judgement_id fix_ends[2] = {
        as_type(shown, at(v, OK(cc_instr_path_apply(k, wfix, 0, 0))), 1, (const uint8_t[][3]){{1}}, (const size_t[]){1}),
        as_type(var(pv), at(v, OK(cc_instr_path_apply(k, wfix, 0, 1))), 1, (const uint8_t[][3]){{1}}, (const size_t[]){1})};
    cc_judgement_id fix_type = OK(cc_instr_path(k, j, at(v, OK(cc_instr_path_apply(k, wfix, j, 0))), fix_ends[0],
                                                fix_ends[1]));
    assert(ck_alpha_equal(k, term_of(fix_type), fix_clause));
    cc_entry_id mf = extend(fix_type);
    cc_judgement_id fix_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator_clause(k, wrapped, var(mw))), var(mf)))));
    cc_judgement_id fix_peak = OK(cc_instr_apply(k, fix_elim, OK(cc_instr_path_apply(k, wfix, 0, 0))));
    cc_judgement_id fix_by_iota = OK(cc_instr_step(k, OK(cc_instr_refl(k, fix_peak)), 1, NULL, 0, CC_STEP_IOTA));
    cc_judgement_id fix_by_boundary = OK(cc_instr_step(k, OK(cc_instr_refl(k, fix_peak)), 1, (const uint8_t[]){1}, 1,
                                                   CC_STEP_PATH));
    assert(!ck_alpha_equal(k, info(fix_by_iota).other, info(fix_by_boundary).other));
    cc_term iota_then_path = info(OK(cc_instr_step(k, fix_by_iota, 1, NULL, 0, CC_STEP_PATH))).other;
    cc_term boundary_then_iota = info(OK(cc_instr_step(k, fix_by_boundary, 1, NULL, 0, CC_STEP_IOTA))).other;
    assert(ck_alpha_equal(k, iota_then_path, term_of(shown)));
    assert(ck_alpha_equal(k, normal(iota_then_path), normal(boundary_then_iota)));
}

/* Review regressions of F5: Iota instantiates the constructor's own
 * arguments only, never a clause's free entries; the displayed binders avoid
 * ambient dimensions; a path-valued position is lifted to a path
 * abstraction. */
static void elimination_capture(void) {
    cc_entry_id i = OK(cc_instr_dimension(k, 0)), j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id nat = OK(fixture_nat(k)), zero = OK(fixture_zero(k));

    /* Box { box(n : Nat); }, and the clause λ x. n, whose n is the entry
     * that stood for box's argument at admission, free in the clause: box's
     * stored type binds that argument as an index, so iota's instantiation
     * of it never touches the clause, and elim(box(0)) is (λ x. n)(0). */
    cc_entry_id bs = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, bs));
    cc_entry_id bn = extend(nat);
    sig = OK(admit(sig, OK(cc_instr_pi(k, bn, var(bs)))));
    cc_judgement_id boxes = OK(cc_instr_sort_begin(k, OK(cc_instr_signature_close(k, sig))));
    cc_judgement_id box = OK(cc_instr_construct(k, boxes, 0));
    cc_judgement_id constant = OK(cc_instr_lambda(k, extend(boxes), nat));
    cc_judgement_id opened = OK(cc_instr_eliminator(k, constant));
    cc_entry_id bx = extend(nat);
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
    cc_judgement_id family = OK(cc_instr_pi(k, extend(s1), universe(lconst(0))));
    cc_entry_id pp = extend(family);
    cc_entry_id f = extend(OK(cc_instr_path(k, j, family, var(pp), var(pp))));
    cc_judgement_id motive = OK(cc_instr_path_apply(k, var(f), i, 0));
    cc_entry_id fb = extend(OK(cc_instr_apply(k, motive, base)));
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
        var(extend(loop_type))))));

    /* PW { base; loop : base = base; wrap(p : base = base) : base = base;
     *      twist(p : base = base) : Path(i; Path(j; s, base, base), wrap(p), p); }.
     * twist's faces on i give its path-valued position to an earlier
     * constructor, wrap(p) @ j, and apply it at a formula, p @ j. */
    cc_entry_id s = extend(former_u0());
    sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id pbase = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), pbase));
    cc_judgement_id around = OK(cc_instr_path(k, i, var(s), var(pbase), var(pbase)));
    sig = OK(admit(sig, around));
    cc_judgement_id wrap_on = OK(cc_instr_pi(k, extend(around), around));
    cc_entry_id pwrap = extend(wrap_on);
    sig = OK(cc_instr_signature_constructor(k, sig, wrap_on, pwrap));
    cc_entry_id tp = extend(around);
    cc_judgement_id flat = OK(cc_instr_path(k, j, var(s), var(pbase), var(pbase)));
    sig = OK(admit(sig, OK(cc_instr_pi(k, tp, OK(cc_instr_path(k, i, flat, OK(cc_instr_apply(k, var(pwrap), var(tp))),
                                                                  var(tp)))))));
    uint32_t twisted = OK(cc_instr_signature_close(k, sig));
    assert(constructor(twisted, 3).positions == 1 && constructor(twisted, 3).dimensions == 2);
    cc_judgement_id pw = OK(cc_instr_sort_begin(k, twisted));
    cc_judgement_id b0 = OK(cc_instr_construct(k, pw, 0)), l0 = OK(cc_instr_construct(k, pw, 1));
    cc_judgement_id w0 = OK(cc_instr_construct(k, pw, 2)), t0 = OK(cc_instr_construct(k, pw, 3));
    cc_entry_id v = motive_over(pw);
    cc_entry_id pv = extend(at(v, b0));
    cc_entry_id pl = extend(path_over(v, l0, i, var(pv)));
    cc_judgement_id loops = OK(cc_instr_path(k, i, pw, b0, b0));
    cc_entry_id pe = extend(loops);
    cc_entry_id pbar = extend(path_over(v, var(pe), i, var(pv)));
    cc_judgement_id wrap_type = OK(cc_instr_pi(k, pe, OK(cc_instr_pi(k, pbar,
        path_over(v, OK(cc_instr_apply(k, w0, var(pe))), i, var(pv))))));
    cc_judgement_id opened_pw = OK(cc_instr_eliminator_clause(k, OK(cc_instr_eliminator_clause(k,
        OK(cc_instr_eliminator(k, var(v))), var(pv))), var(pl)));
    assert(ck_alpha_equal(k, term_of(wrap_type), type_of(opened_pw)));
    cc_entry_id mw = extend(wrap_type);
    /* twist's clause type as a driver derives it: Π (p). Π (p̄).
     * PathP(i. PathP(j. P(twist(p) @ i @ j), pv, pv), m_wrap(p, p̄), p̄). */
    cc_entry_id te = extend(loops);
    cc_entry_id tbar = extend(path_over(v, var(te), i, var(pv)));
    cc_judgement_id twist_i = OK(cc_instr_path_apply(k, OK(cc_instr_apply(k, t0, var(te))), i, 0));
    cc_judgement_id corners[2];
    for (unsigned e = 0; e < 2; ++e)
        corners[e] = as_type(var(pv), at(v, OK(cc_instr_path_apply(k, twist_i, 0, e))), 1,
                             (const uint8_t[][3]){{1}}, (const size_t[]){1});
    cc_judgement_id square = OK(cc_instr_path(k, j, at(v, OK(cc_instr_path_apply(k, twist_i, j, 0))), corners[0],
                                              corners[1]));
    cc_judgement_id sides[2] = {
        as_type(OK(cc_instr_apply(k, OK(cc_instr_apply(k, var(mw), var(te))), var(tbar))),
                OK(cc_instr_endpoint(k, square, i, 0)), 1, (const uint8_t[][3]){{0, 1, 0}}, (const size_t[]){3}),
        as_type(var(tbar), OK(cc_instr_endpoint(k, square, i, 1)), 1, (const uint8_t[][3]){{0, 1, 0}},
                (const size_t[]){3})};
    cc_judgement_id twist_type = OK(cc_instr_pi(k, te, OK(cc_instr_pi(k, tbar,
        OK(cc_instr_path(k, i, square, sides[0], sides[1]))))));
    cc_judgement_id with_wrap = OK(cc_instr_eliminator_clause(k, opened_pw, var(mw)));
    assert(ck_alpha_equal(k, term_of(twist_type), type_of(with_wrap)));
    cc_entry_id mt = extend(twist_type);
    cc_judgement_id pw_elim = OK(cc_instr_eliminator_close(k, OK(cc_instr_eliminator_clause(k, with_wrap, var(mt)))));
    /* elim(wrap(p0) @ j) is m_wrap(p0, ⟨i⟩ elim(p0 @ i)) @ j. */
    cc_entry_id p0 = extend(loops);
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

    /* CP01 with a path-valued position in the boundary: elim(twist(p0) @ ε @ j).
     * Iota, then the path step through the displayed annotation of the face
     * ε, gives m_wrap(p0, p̄0) @ j or p̄0 @ j. The boundary first gives
     * wrap(p0) @ j, then Iota, or p0 @ j, which is neutral. They join because
     * Iota lifts p0 to p̄0 = ⟨i⟩ elim(p0 @ i). */
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id peak = OK(cc_instr_apply(k, pw_elim, OK(cc_instr_path_apply(k,
            OK(cc_instr_path_apply(k, OK(cc_instr_apply(k, t0, var(p0))), 0, e)), j, 0))));
        cc_judgement_id iota_first = OK(cc_instr_step(k, OK(cc_instr_refl(k, peak)), 1, NULL, 0, CC_STEP_IOTA));
        cc_judgement_id boundary_first = OK(cc_instr_step(k, OK(cc_instr_refl(k, peak)), 1, (const uint8_t[]){1, 0}, 2,
                                                          CC_STEP_PATH));
        assert(!ck_alpha_equal(k, info(iota_first).other, info(boundary_first).other));
        cc_term iota_then_path = info(OK(cc_instr_step(k, iota_first, 1, (const uint8_t[]){0}, 1, CC_STEP_PATH))).other;
        cc_term boundary_then = e ? info(boundary_first).other
                                  : info(OK(cc_instr_step(k, boundary_first, 1, NULL, 0, CC_STEP_IOTA))).other;
        assert(ck_alpha_equal(k, normal(iota_then_path), normal(boundary_then)));
    }
    /* The face ε = 0 shows wrap's clause at the lifted position. */
    cc_judgement_id wrapped_face = OK(cc_instr_apply(k, pw_elim, OK(cc_instr_path_apply(k,
        OK(cc_instr_path_apply(k, OK(cc_instr_apply(k, t0, var(p0))), 0, 0)), j, 0))));
    cc_term shown = info(OK(cc_instr_step(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, wrapped_face)), 1, NULL, 0,
        CC_STEP_IOTA)), 1, (const uint8_t[]){0}, 1, CC_STEP_PATH))).other;
    assert(kind(shown) == CC_PAPP && child(child(child(shown, 0), 0), 0) == term_of(var(mw)));
    assert(ck_alpha_equal(k, child(child(shown, 0), 1), term_of(lifted_p0)));
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
static cc_judgement_id open_bad(cc_entry_id *s) {
    *s = extend(former_u0());
    return OK(begin_u0(CC_UNTRUNCATED, *s));
}

static void refusals(void) {
    cc_entry_id s;
    cc_judgement_id nat = OK(fixture_nat(k));
    cc_judgement_id sig = open_bad(&s);
    cc_entry_id f = extend(OK(cc_instr_pi(k, extend(var(s)), nat)));
    /* A4: s in data, as the domain of a function argument. */
    REJECTS(admit(sig, OK(cc_instr_pi(k, f, var(s)))), "arity mentions");
    /* A5: s in an arity: f : (s → Nat) → s. */
    cc_judgement_id s_to_nat = OK(cc_instr_pi(k, extend(var(s)), nat));
    cc_entry_id h = extend(s_to_nat);
    cc_entry_id g = extend(OK(cc_instr_pi(k, h, var(s))));
    REJECTS(admit(sig, OK(cc_instr_pi(k, g, var(s)))), "arity mentions");
    /* A6: s under a function inside a position's arity: g : Nat → (s → s). */
    cc_entry_id an = extend(nat), ax = extend(var(s));
    cc_entry_id ag = extend(OK(cc_instr_pi(k, an, OK(cc_instr_pi(k, ax, var(s))))));
    REJECTS(admit(sig, OK(cc_instr_pi(k, ag, var(s)))), "arity mentions");
    /* A11: data after a position, in the kernel's order. */
    cc_entry_id x = extend(var(s));
    cc_entry_id n = extend(nat);
    cc_judgement_id late_data = OK(cc_instr_pi(k, x, OK(cc_instr_pi(k, n, var(s)))));
    REJECTS(admit(sig, late_data), "data argument follows a position");
    /* A13: a foreign entry in the constructor type's context: a type
     * variable T : U0 that is not the signature's. */
    cc_entry_id foreign = extend(former_u0());
    REJECTS(admit(sig, var(foreign)), "not the signature's");
    /* A constructor type in another universe: U0 itself lives in U1. */
    REJECTS(admit(sig, former_u0()), "signature's universe");
    /* A7: a boundary naming the constructor itself. A constructor's entry
     * is typed by its type, so no term of the type mentions it: a boundary's
     * entry given as the constructor's has another type, and a new entry
     * leaves the boundary's entry outside the telescope. */
    cc_entry_id self = extend(var(s));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_judgement_id around_self = OK(cc_instr_path(k, i, var(s), var(self), var(self)));
    REJECTS(cc_instr_signature_constructor(k, sig, around_self, self), "A constructor entry's type is not that constructor's.");
    REJECTS(admit(sig, around_self), "not the signature's");
    /* The constructor's entry can still sit in its type's context, with no
     * term mentioning it: s : U0, converted along U0 = (λ (_ : s). U0)(c) = U0. */
    cc_entry_id c = extend(var(s));
    cc_judgement_id constant = OK(cc_instr_lambda(k, extend(var(s)), former_u0()));
    cc_judgement_id beta = OK(cc_instr_step(k, OK(cc_instr_refl(k, OK(cc_instr_apply(k, constant, var(c))))), 1, NULL, 0,
                                            CC_STEP_BETA));
    cc_judgement_id weakened = OK(cc_instr_convert(k, var(s), OK(cc_instr_transitivity(k, OK(cc_instr_symmetry(k, beta)), beta))));
    assert(term_of(weakened) == term_of(var(s)) && cc_kernel_judgement_context(k, weakened, 1) == c);
    REJECTS(cc_instr_signature_constructor(k, sig, weakened, c), "names the constructor itself");
    /* A8: a boundary naming a later constructor: the entry is not yet the
     * signature's. */
    cc_entry_id later = extend(var(s));
    REJECTS(admit(sig, OK(cc_instr_path(k, i, var(s), var(later), var(later)))), "not the signature's");
    /* A boundary with a composition (A9): comp^i s [] x, with x : s a position. */
    cc_judgement_id good = OK(admit(sig, var(s)));
    cc_entry_id z = extend(var(s));
    cc_judgement_id system = OK(cc_instr_system(k, i, var(s), var(z)));
    cc_judgement_id composed = OK(cc_instr_comp(k, system));
    cc_entry_id j = OK(cc_instr_dimension(k, 1));
    cc_judgement_id with_comp = OK(cc_instr_pi(k, z, OK(cc_instr_path(k, j, var(s), composed, var(z)))));
    REJECTS(admit(good, with_comp), "composition");
    /* Only the latest judgement continues a signature. */
    REJECTS(admit(sig, var(s)), "latest");
    /* A12: a data argument that mentions a position, in a boundary. */
    cc_judgement_id nat_con = OK(cc_instr_pi(k, n, var(s)));
    cc_entry_id c2 = extend(nat_con);
    cc_judgement_id with_nat = OK(cc_instr_signature_constructor(k, good, nat_con, c2));
    cc_entry_id w = extend(var(s));
    cc_judgement_id zero_of_w = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, extend(var(s)),
                                                                           OK(fixture_zero(k)))), var(w)));
    cc_judgement_id tainted = OK(cc_instr_apply(k, var(c2), zero_of_w));
    cc_judgement_id tainted_type = OK(cc_instr_pi(k, w, OK(cc_instr_path(k, i, var(s), tainted, var(w)))));
    REJECTS(admit(with_nat, tainted_type), "data terms only");
    /* T7: a commit while a signature is open is refused; T5: rollback
     * forgets a signature opened since the checkpoint. */
    size_t before = cc_kernel_signature_count(k);
    cc_kernel_checkpoint(k);
    cc_entry_id s2;
    cc_judgement_id opened = open_bad(&s2);
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
/* ⊢ Π (x < ω). Π (A : U(x)). U0, with the entries x and A that stand for its
 * binders; parameters receives both, in order. */
static cc_judgement_id former_into_u0(cc_entry_id parameters[2]) {
    parameters[0] = OK(cc_instr_level(k));
    parameters[1] = extend(universe(lvar(parameters[0])));
    return OK(cc_instr_level_pi(k, parameters[0], OK(cc_instr_pi(k, parameters[1], universe(lconst(0))))));
}

static void hidden_bounds(void) {
    cc_judgement_id nat = OK(fixture_nat(k)), u0 = universe(lconst(0)), uu0 = universe(tier1(0));
    cc_judgement_id nat_big = OK(cc_instr_lift(k, nat, uu0)), uu0_itself = uu0;

    /* V13: Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); } lives in UU0;
     * Mixed(U2, Nat) reads x = 3, and Mixed(Nat) with Nat : UU0 reads ω. The
     * parameter entries need not be made in the former's order. */
    cc_entry_id be = extend(uu0);
    cc_entry_id xe = OK(cc_instr_level(k));
    cc_entry_id ae = extend(universe(lvar(xe)));
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, ae, OK(cc_instr_pi(k, be, uu0))))));
    const cc_entry_id mixed_parameters[] = {xe, ae, be};
    cc_entry_id s = extend(uu0);
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, mixed_parameters, 3, s, 0));
    cc_entry_id a = extend(var(ae)), b = extend(var(be));
    sig = OK(admit(sig, OK(cc_instr_pi(k, a, OK(cc_instr_pi(k, b, var(s)))))));
    uint32_t mixed = OK(cc_instr_signature_close(k, sig));
    cc_judgement_id at3 = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, mixed)), universe(lconst(2))));
    assert(type_of(OK(cc_instr_sort_parameter(k, at3, nat_big))) == term_of(uu0));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, mixed)), nat_big)), nat_big),
            "finite levels only");

    /* V17: Tag(A : UU0) : U0 { here; } and Outer(x < ω, A : U(x)) : U0
     * { wrap(t : Tag(A)); }, with A lifted into UU0; Outer(Nat) is formed,
     * Outer(UU0) and Outer(A) for A : UU0 are not. */
    cc_entry_id ta = extend(uu0);
    s = extend(u0);
    sig = OK(cc_instr_signature_begin(k, OK(cc_instr_pi(k, ta, u0)), CC_UNTRUNCATED, &ta, 1, s, 0));
    uint32_t tag = OK(cc_instr_signature_close(k, OK(admit(sig, var(s)))));
    cc_entry_id parameters[2] = {0, 0};
    former = former_into_u0(parameters);
    s = extend(u0);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 2, s, 0));
    cc_judgement_id tag_a = OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, tag)),
                                                       OK(cc_instr_lift(k, var(parameters[1]), uu0))));
    cc_entry_id held = extend(tag_a);
    uint32_t outer = OK(cc_instr_signature_close(k, OK(admit(sig, OK(cc_instr_pi(k, held, var(s)))))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), nat));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), uu0_itself), "finite levels only");
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer)), nat_big), "finite levels only");

    /* V18: the same bound through a definition F(A : UU0) : U0 := Unit, in
     * wrap(t : F(A)); refused at the instance that reads it. */
    cc_entry_id fa = extend(uu0);
    cc_judgement_id f = OK(cc_instr_define(k, OK(cc_instr_lambda(k, fa, OK(cc_instr_unit(k))))));
    former = former_into_u0(parameters);
    s = extend(u0);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 2, s, 0));
    cc_entry_id through = extend(OK(cc_instr_apply(k, f, OK(cc_instr_lift(k, var(parameters[1]), uu0)))));
    uint32_t hid = OK(cc_instr_signature_close(k, OK(admit(sig, OK(cc_instr_pi(k, through, var(s)))))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, hid)), nat));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, hid)), nat_big), "finite levels only");

    /* V19: Big : UU1 { pack(B : UU0); } and Outer2(x < ω, A : U(x),
     * F : Big → U0) : U0 { wrap(t : F(pack(A))); }: a bound in a
     * parameter-free signature's constructor type. */
    cc_judgement_id uu1 = universe(tier1(1));
    s = extend(uu1);
    sig = OK(cc_instr_signature_begin(k, uu1, CC_UNTRUNCATED, NULL, 0, s, 0));
    cc_entry_id bb = extend(uu0);
    uint32_t big = OK(cc_instr_signature_close(k, OK(admit(sig, OK(cc_instr_pi(k, bb, var(s)))))));
    cc_judgement_id big_instance = OK(cc_instr_sort_begin(k, big));
    cc_entry_id z = extend(big_instance);
    cc_entry_id x2 = OK(cc_instr_level(k));
    cc_entry_id a2 = extend(universe(lvar(x2)));
    cc_entry_id fe = extend(OK(cc_instr_pi(k, z, u0)));
    former = OK(cc_instr_level_pi(k, x2, OK(cc_instr_pi(k, a2, OK(cc_instr_pi(k, fe, u0))))));
    const cc_entry_id outer2_parameters[] = {x2, a2, fe};
    s = extend(u0);
    sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, outer2_parameters, 3, s, 0));
    cc_judgement_id packed = OK(cc_instr_apply(k, OK(cc_instr_construct(k, big_instance, 0)), OK(cc_instr_lift(k, var(a2), uu0))));
    cc_entry_id carried = extend(OK(cc_instr_apply(k, var(fe), packed)));
    uint32_t outer2 = OK(cc_instr_signature_close(k, OK(admit(sig, OK(cc_instr_pi(k, carried, var(s)))))));
    cc_judgement_id family = OK(cc_instr_lambda(k, extend(big_instance), OK(cc_instr_unit(k))));
    OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), nat)), family));
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), uu0_itself)), family),
            "finite levels only");
    REJECTS(cc_instr_sort_parameter(k, OK(cc_instr_sort_parameter(k, OK(cc_instr_sort_begin(k, outer2)), nat_big)), family),
            "finite levels only");
}

/* R2, R3: the resource bounds of 5.8, at their limits and above them. */
static void resources(void) {
    /* R2: 256 constructors are admitted, and a 257th is refused. */
    cc_entry_id s = extend(former_u0());
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    for (uint32_t c = 0; c < CC_SIGNATURE_CONSTRUCTORS; ++c)
        sig = OK(admit(sig, var(s)));
    REJECTS(admit(sig, var(s)), "too many constructors");
    assert(signature(OK(cc_instr_signature_close(k, sig))).constructor_count == CC_SIGNATURE_CONSTRUCTORS);

    /* R2: a constructor with 64 arguments is admitted, and one with 65 is
     * refused. */
    cc_judgement_id nat = OK(fixture_nat(k));
    cc_entry_id args[CC_CONSTRUCTOR_ARGUMENTS + 1];
    for (uint32_t a = 0; a <= CC_CONSTRUCTOR_ARGUMENTS; ++a)
        args[a] = extend(nat);
    s = extend(former_u0());
    sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_judgement_id at_limit = var(s);
    for (uint32_t a = CC_CONSTRUCTOR_ARGUMENTS; a-- > 0;)
        at_limit = OK(cc_instr_pi(k, args[a], at_limit));
    REJECTS(admit(sig, OK(cc_instr_pi(k, args[CC_CONSTRUCTOR_ARGUMENTS], at_limit))), "too many arguments");
    sig = OK(admit(sig, at_limit));
    assert(constructor(OK(cc_instr_signature_close(k, sig)), 0).data == CC_CONSTRUCTOR_ARGUMENTS);

    /* R3: a position of arity 64 into a cube of depth 8, ⟨i⟩ … b at each
     * level, is admitted within the budget. */
    s = extend(former_u0());
    sig = OK(begin_u0(CC_UNTRUNCATED, s));
    cc_entry_id b = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), b));
    cc_judgement_id cube = var(s), point = var(b);
    for (unsigned d = 0; d < 8; ++d) {
        cc_entry_id dimension = OK(cc_instr_dimension(k, d));
        cc_judgement_id next = OK(cc_instr_path(k, dimension, cube, point, point));
        point = OK(cc_instr_path_lambda(k, dimension, point));
        cube = next;
    }
    cc_judgement_id position = cube;
    for (uint32_t a = CC_CONSTRUCTOR_ARGUMENTS; a-- > 0;)
        position = OK(cc_instr_pi(k, args[a], position));
    cc_entry_id f = extend(position);
    cc_judgement_id deep_type = OK(cc_instr_pi(k, f, var(s)));
    cc_entry_id deep_entry = extend(deep_type);
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    sig = OK(cc_instr_signature_constructor(k, sig, deep_type, deep_entry));
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
    cc_term nat = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
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
    }
    cc_signature_info info;
    assert(!cc_kernel_signature(k, 9999, &info));
    REJECTS(cc_instr_sort_begin(k, 9999), "Only an admitted signature");
}

/* T6: a commit keeps an admitted signature and relocates its syntax. The
 * entries it was admitted with are truncated; its stored types mention
 * none of them, and read the same. */
static void commits(void) {
    size_t entries = cc_kernel_entry_count(k);
    cc_kernel_checkpoint(k);
    cc_entry_id s = extend(former_u0());
    cc_entry_id m = extend(var(s));
    cc_judgement_id sig = OK(begin_u0(CC_UNTRUNCATED, s));
    sig = OK(admit(sig, var(s)));
    sig = OK(admit(sig, OK(cc_instr_pi(k, m, var(s)))));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    assert(cc_kernel_entry_count(k) > entries);
    assert(cc_kernel_commit_checkpoint(k));
    assert(cc_kernel_entry_count(k) == entries);
    cc_constructor_info succ = constructor(index, 1);
    assert(succ.type == pi(bound(1), bound(2)) && succ.positions == 1 && !succ.generated);
    /* Instances formed after the commit check. */
    assert(kind(type_of(OK(cc_instr_construct(k, OK(cc_instr_sort_begin(k, index)), 1)))) == CC_PI);
    assert(kind(signature(index).former) == CC_U);
}

/* Section 3.6: the entries that stand for a signature's telescope. Its
 * parameter entries are one per binder of the former, of the binder's
 * kind, at its domain opened with the entries before them, and pairwise
 * distinct; the sort's is a term entry at the universe opened with them all,
 * apart from them; a constructor's is a term entry at its type, new to the
 * telescope; and a constructor type's context holds the telescope's entries
 * only. Each is refused with its own message. */
static void admission_entries(void) {
    /* Both(x < ω, A B : U(x)) : U(x), with x, A and B, and the sort s. */
    cc_entry_id xe = OK(cc_instr_level(k));
    cc_judgement_id ux = universe(lvar(xe));
    cc_entry_id ae = extend(ux), be = extend(ux);
    cc_judgement_id former = OK(cc_instr_level_pi(k, xe, OK(cc_instr_pi(k, ae, OK(cc_instr_pi(k, be, ux))))));
    cc_entry_id s = extend(ux);
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){xe, ae}, 2, s, 0),
            "A signature takes one entry for each of its former's parameters.");
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, NULL, 3, s, 0),
            "A signature takes one entry for each of its former's parameters.");
    /* A term entry for the universe parameter, a level entry for a term
     * parameter. */
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){ae, ae, be}, 3, s, 0),
            "A signature's universe parameter takes a level entry.");
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){xe, xe, be}, 3, s, 0),
            "A signature's term parameter takes a term entry.");
    /* A repeated parameter entry, of the right kind and type: A and B have
     * one type. */
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){xe, ae, ae}, 3, s, 0),
            "A signature's entries are pairwise distinct, the sort's apart from its parameters'.");
    /* The sort's entry equal to a parameter's, at the sort's type U(x), and a
     * level entry for the sort. */
    const cc_entry_id parameters[] = {xe, ae, be};
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 3, be, 0),
            "A signature's entries are pairwise distinct, the sort's apart from its parameters'.");
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 3, xe, 0),
            "A signature's sort takes a term entry.");
    /* Types are read with the entries given: A at U(y) for another level
     * entry y is no parameter of the signature opened at x, nor is s : U(x)
     * its sort when it is opened at y, nor is a sort in U0. */
    cc_entry_id ye = OK(cc_instr_level(k));
    cc_judgement_id uy = universe(lvar(ye));
    cc_entry_id ay = extend(uy), by = extend(uy), sy = extend(uy);
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){xe, ay, be}, 3, s, 0),
            "A parameter entry's type is not the signature's.");
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){ye, ay, by}, 3, s, 0),
            "The sort entry's type is not the signature's universe.");
    REJECTS(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 3, extend(former_u0()), 0),
            "The sort entry's type is not the signature's universe.");
    /* Opened at y throughout, the same former is admitted. */
    OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, (const cc_entry_id[]){ye, ay, by}, 3, sy, 0));

    /* Constructor entries. */
    cc_judgement_id sig = OK(cc_instr_signature_begin(k, former, CC_UNTRUNCATED, parameters, 3, s, 0));
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), ye), "A constructor takes a term entry.");
    /* The sort's, a parameter's and an earlier constructor's entry are
     * already in the telescope. */
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), s), "A constructor's entry is already in its signature's telescope.");
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), ae), "A constructor's entry is already in its signature's telescope.");
    cc_entry_id first = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), first));
    REJECTS(cc_instr_signature_constructor(k, sig, var(s), first),
            "A constructor's entry is already in its signature's telescope.");
    /* An entry at another type than the constructor's. */
    cc_judgement_id pair_type = OK(cc_instr_pi(k, extend(var(ae)), OK(cc_instr_pi(k, extend(var(be)), var(s)))));
    REJECTS(cc_instr_signature_constructor(k, sig, pair_type, extend(var(s))), "A constructor entry's type is not that constructor's.");
    /* A constructor type whose context holds an entry outside the telescope:
     * a type T : U(x) that is no parameter. */
    cc_entry_id outside = extend(ux);
    REJECTS(admit(sig, OK(cc_instr_pi(k, extend(var(outside)), var(s)))), "not the signature's");
    /* The telescope's entries only, the parameters' included: mk(a : A, b : B)
     * is admitted, its type closed over [x, A, B, s, first]. */
    sig = OK(admit(sig, pair_type));
    uint32_t index = OK(cc_instr_signature_close(k, sig));
    assert(constructor(index, 1).type == pi(bound(3), pi(bound(3), bound(3))));
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    /* H1 is on by default since its release. T1: switched off, admission is
     * refused. */
    assert(cc_kernel_extensions(k) == CC_EXTENSION_H1);
    cc_kernel_set_extensions(k, 0);
    cc_entry_id sort = extend(former_u0());
    REJECTS(begin_u0(CC_UNTRUNCATED, sort), "switched off");
    cc_kernel_set_extensions(k, CC_EXTENSION_H1);
    assert(cc_kernel_extensions(k) == CC_EXTENSION_H1);
    /* Formers that are not Π (xs < ω). Π (ps : Ps). U(ℓ), or not closed. */
    REJECTS(cc_instr_signature_begin(k, OK(fixture_nat(k)), CC_UNTRUNCATED, NULL, 0, sort, 0), "former type");
    cc_entry_id level = OK(cc_instr_level(k));
    REJECTS(cc_instr_signature_begin(k, universe(lvar(level)), CC_UNTRUNCATED, NULL, 0, extend(universe(lvar(level))), 0),
            "A signature's former type must be closed.");
    REJECTS(begin_u0(CC_TRUNCATION_MAX + 3, sort), "truncation level");
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
    critical_composition_pairs();
    transport_properties();
    elimination();
    elimination_capture();
    annotations();
    refusals();
    hidden_bounds();
    resources();
    malformed();
    commits();
    admission_entries();
    cc_kernel_free(k);
    printf("signature admission: ok\n");
    return 0;
}
