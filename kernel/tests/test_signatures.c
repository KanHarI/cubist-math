/* Declared types (H1), families F1 and F6: signatures are admitted one
 * constructor at a time, and refused where the specification's acceptance
 * cases say (docs/roadmaps/h1-signature-specification.md, section 10). Every
 * constructor type is derived here by ordinary instructions, as the driver
 * derives it. */
#include "cubical_kernel.h"
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
    S_G = 120, GPOINT, GA
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
    refusals();
    commits();
    cc_kernel_free(k);
    printf("signature admission: ok\n");
    return 0;
}
