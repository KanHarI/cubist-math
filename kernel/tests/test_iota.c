/* Iota and clause types on the locally nameless kernel (sections 3.1, 3.3
 * and 7.1 of docs/roadmaps/kernel/locally-nameless-kernel.md): a clause
 * type's arguments opened at levels apart, so two arguments of one type stay
 * two; one Iota step lifting a path-valued position to a path abstraction,
 * with or without arity binders, and instantiating an arity binder's domain
 * at a data argument; and the equivalence types and Glue side conditions
 * built where an operand holds the placeholder of a binder opened outside.
 * tests/locally-nameless.test.mjs checks the normal forms of the same
 * shapes, and others, against main's ABI 3. */
#include "cubical_kernel.h"
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;
static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) { fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k)); assert(0); }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)

static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info r; assert(cc_kernel_judgement(k, j, &r)); return r; }
static cc_term term_of(cc_judgement_id j) { return info(j).term; }
static cc_term type_of(cc_judgement_id j) { return info(j).type; }
static cc_term child(cc_term t, unsigned i) { cc_term c[4]; assert(cc_kernel_node(k, t, NULL, NULL, c)); return c[i]; }
static cc_term_kind kind(cc_term t) { cc_term_kind r; assert(cc_kernel_node(k, t, &r, NULL, NULL)); return r; }
/* Equal up to bound dimension names; bound variables are indices. */
static bool same(cc_term a, cc_term b) { bool answer = false; assert(cc_kernel_alpha_equal(k, a, b, &answer)); return answer; }

/* Raw syntax, for the types built by hand. */
static cc_term make(cc_term_kind kind, uint32_t payload, cc_term a, cc_term b) {
    return OK(cc_kernel_term(k, kind, payload, a, b, 0, 0));
}
static cc_term bound(uint32_t index) { return make(CC_BOUND, index, 0, 0); }
static cc_term app(cc_term f, cc_term x) { return make(CC_APP, 0, f, x); }
static cc_term pi(cc_term domain, cc_term body) { return make(CC_PI, 0, domain, body); }

/* Instructions. */
static cc_judgement_id var(cc_entry_id e) { return OK(cc_instr_variable(k, e)); }
static cc_entry_id extend(cc_judgement_id type) { return OK(cc_instr_extend(k, type)); }
static cc_judgement_id universe(unsigned n) { return OK(cc_instr_universe(k, make(CC_LCONST, n, 0, 0))); }
static cc_judgement_id apply(cc_judgement_id f, cc_judgement_id x) { return OK(cc_instr_apply(k, f, x)); }
static cc_judgement_id pi_over(cc_entry_id e, cc_judgement_id body) { return OK(cc_instr_pi(k, e, body)); }
static cc_judgement_id lambda(cc_entry_id e, cc_judgement_id body) { return OK(cc_instr_lambda(k, e, body)); }
static cc_judgement_id construct(cc_judgement_id instance, uint32_t c) { return OK(cc_instr_construct(k, instance, c)); }
static cc_judgement_id path_at(cc_judgement_id path, cc_entry_id dimension, unsigned endpoint) {
    return OK(cc_instr_path_apply(k, path, dimension, endpoint));
}

/* A signature with no parameters over U(level), at a new sort entry. */
static cc_judgement_id begin(unsigned level, cc_entry_id *sort) {
    *sort = extend(universe(level));
    return OK(cc_instr_signature_begin(k, universe(level), CC_UNTRUNCATED, NULL, 0, *sort, 0));
}
/* SignatureConstructor at a type, with a new entry standing for the
 * constructor. */
static cc_judgement_id admit(cc_judgement_id signature, cc_judgement_id type) {
    return OK(cc_instr_signature_constructor(k, signature, type, extend(type)));
}
static cc_judgement_id instance_of(cc_judgement_id signature) {
    return OK(cc_instr_sort_begin(k, OK(cc_instr_signature_close(k, signature))));
}

/* A motive M : Π (z : I). U0 over an instance, as an entry; M(t). */
static cc_entry_id motive_over(cc_judgement_id instance) {
    return extend(pi_over(extend(instance), universe(0)));
}
static cc_judgement_id at(cc_entry_id motive, cc_judgement_id t) { return apply(var(motive), t); }
static cc_judgement_id clause(cc_judgement_id eliminator, cc_judgement_id given) {
    return OK(cc_instr_eliminator_clause(k, eliminator, given));
}

/* PathP(i. M(p @ i), point, point) for p : Path(I, b, b), with point : M(b)
 * moved to M(p @ ε) at each end by the path step. */
static cc_judgement_id path_over(cc_entry_id motive, cc_judgement_id p, cc_entry_id i, cc_judgement_id point) {
    cc_judgement_id ends[2];
    for (unsigned e = 0; e < 2; ++e) {
        cc_judgement_id at_end = at(motive, path_at(p, 0, e));
        cc_judgement_id to_point = OK(cc_instr_step(k, OK(cc_instr_refl(k, at_end)), 1, (const uint8_t[]){1}, 1,
                                                    CC_STEP_PATH));
        ends[e] = OK(cc_instr_convert(k, point, OK(cc_instr_symmetry(k, to_point))));
    }
    return OK(cc_instr_path(k, i, at(motive, path_at(p, i, 0)), ends[0], ends[1]));
}

/* The other side of a reflexivity after one Iota step at its root. */
static cc_term iota_of(cc_judgement_id j) {
    return info(OK(cc_instr_step(k, OK(cc_instr_refl(k, j)), 1, NULL, 0, CC_STEP_IOTA))).other;
}

/* Opened levels across operands (section 3.1): S { leaf; fork(x, y : S);
 * pair(a, b : Unit); }. The clause type of fork is
 *   Π (x : I). Π (y : I). Π (x̄ : M(x)). Π (ȳ : M(y)). M(fork(x, y)),
 * the two arguments apart, as is pair's, Π (a b : Unit). M(pair(a, b)), and
 * Iota puts each argument in its own place. */
static void apart(void) {
    cc_judgement_id unit = OK(cc_instr_unit(k));
    cc_entry_id s;
    cc_judgement_id sig = begin(0, &s);
    sig = admit(sig, var(s));
    cc_entry_id x = extend(var(s)), y = extend(var(s));
    sig = admit(sig, pi_over(x, pi_over(y, var(s))));
    cc_entry_id a = extend(unit), b = extend(unit);
    sig = admit(sig, pi_over(a, pi_over(b, var(s))));
    cc_judgement_id instance = instance_of(sig);
    cc_judgement_id leaf = construct(instance, 0), forks = construct(instance, 1), pairs = construct(instance, 2);
    cc_entry_id m = motive_over(instance);
    cc_entry_id on_leaf = extend(at(m, leaf));
    cc_judgement_id after_leaf = clause(OK(cc_instr_eliminator(k, var(m))), var(on_leaf));
    /* By hand: under x, y, x̄, ȳ, x is index 3 and y index 2. */
    cc_term I = term_of(instance), M = term_of(var(m)), F = term_of(forks), P = term_of(pairs);
    cc_term fork_type = pi(I, pi(I, pi(app(M, bound(1)), pi(app(M, bound(1)), app(M, app(app(F, bound(3)), bound(2)))))));
    assert(same(type_of(after_leaf), fork_type));
    /* One level for both arguments would make either of these. */
    assert(!same(type_of(after_leaf), pi(I, pi(I, pi(app(M, bound(1)), pi(app(M, bound(1)),
        app(M, app(app(F, bound(2)), bound(2)))))))));
    assert(!same(type_of(after_leaf), pi(I, pi(I, pi(app(M, bound(0)), pi(app(M, bound(1)),
        app(M, app(app(F, bound(3)), bound(2)))))))));
    /* The same type, derived as a driver derives a clause's. */
    cc_entry_id fx = extend(instance), fy = extend(instance);
    cc_entry_id fx_bar = extend(at(m, var(fx))), fy_bar = extend(at(m, var(fy)));
    cc_judgement_id derived = pi_over(fx, pi_over(fy, pi_over(fx_bar, pi_over(fy_bar,
        at(m, apply(apply(forks, var(fx)), var(fy)))))));
    assert(term_of(derived) == type_of(after_leaf));
    cc_entry_id on_fork = extend(derived);
    cc_judgement_id after_fork = clause(after_leaf, var(on_fork));
    cc_term unit_type = term_of(unit);
    assert(same(type_of(after_fork), pi(unit_type, pi(unit_type, app(M, app(app(P, bound(1)), bound(0)))))));
    assert(!same(type_of(after_fork), pi(unit_type, pi(unit_type, app(M, app(app(P, bound(0)), bound(0)))))));
    cc_entry_id pa = extend(unit), pb = extend(unit);
    cc_judgement_id pair_type = pi_over(pa, pi_over(pb, at(m, apply(apply(pairs, var(pa)), var(pb)))));
    cc_entry_id on_pair = extend(pair_type);
    cc_judgement_id elim = OK(cc_instr_eliminator_close(k, clause(after_fork, var(on_pair))));
    cc_term E = term_of(elim);
    /* elim(fork(u, leaf)) is m_fork(u, leaf, elim(u), elim(leaf)), and
     * elim(pair(p, q)) is m_pair(p, q). */
    cc_entry_id u = extend(instance), p = extend(unit), q = extend(unit);
    cc_term U = term_of(var(u)), L = term_of(leaf);
    cc_term on_fork_term = term_of(var(on_fork)), on_pair_term = term_of(var(on_pair));
    assert(same(iota_of(apply(elim, apply(apply(forks, var(u)), leaf))),
                app(app(app(app(on_fork_term, U), L), app(E, U)), app(E, L))));
    assert(same(iota_of(apply(elim, apply(apply(pairs, var(p)), var(q)))),
                app(app(on_pair_term, term_of(var(p))), term_of(var(q)))));
    puts("Clause types and Iota keep two arguments of one type apart.");
}

/* Iota's cube lifting (section 3.3): W { base; wrap(p : Path(W, base, base));
 * spin(q : Π (y : Unit). Path(W, base, base)); }. One Iota step on wrap(p)
 * gives m_wrap(p, ⟨i⟩ elim(p @ i)), a path abstraction with its displayed
 * family, never elim applied to p; on spin(q) it gives
 * m_spin(q, λ (y : Unit). ⟨i⟩ elim(q(y) @ i)). */
static void lifting(void) {
    cc_judgement_id unit = OK(cc_instr_unit(k));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_entry_id s;
    cc_judgement_id sig = begin(0, &s);
    cc_entry_id base = extend(var(s));
    sig = OK(cc_instr_signature_constructor(k, sig, var(s), base));
    cc_judgement_id loops = OK(cc_instr_path(k, i, var(s), var(base), var(base)));
    sig = admit(sig, pi_over(extend(loops), var(s)));
    sig = admit(sig, pi_over(extend(pi_over(extend(unit), loops)), var(s)));
    cc_judgement_id w = instance_of(sig);
    cc_judgement_id wbase = construct(w, 0), wrap = construct(w, 1), spin = construct(w, 2);
    cc_entry_id v = motive_over(w);
    cc_entry_id on_base = extend(at(v, wbase));
    cc_judgement_id opened = clause(OK(cc_instr_eliminator(k, var(v))), var(on_base));
    /* wrap's clause: Π (p : Path(W, base, base)). Π (p̄ : PathP(i. M(p @ i),
     * m_base, m_base)). M(wrap(p)). */
    cc_judgement_id w_loops = OK(cc_instr_path(k, i, w, wbase, wbase));
    cc_entry_id p = extend(w_loops);
    cc_entry_id p_bar = extend(path_over(v, var(p), i, var(on_base)));
    cc_judgement_id wrap_type = pi_over(p, pi_over(p_bar, at(v, apply(wrap, var(p)))));
    assert(same(type_of(opened), term_of(wrap_type)));
    cc_entry_id on_wrap = extend(wrap_type);
    opened = clause(opened, var(on_wrap));
    /* spin's: Π (q : Π (y : Unit). Path(W, base, base)).
     * Π (q̄ : Π (y : Unit). PathP(i. M(q(y) @ i), m_base, m_base)). M(spin(q)). */
    cc_entry_id q = extend(pi_over(extend(unit), w_loops)), y = extend(unit);
    cc_entry_id q_bar = extend(pi_over(y, path_over(v, apply(var(q), var(y)), i, var(on_base))));
    cc_judgement_id spin_type = pi_over(q, pi_over(q_bar, at(v, apply(spin, var(q)))));
    assert(same(type_of(opened), term_of(spin_type)));
    cc_entry_id on_spin = extend(spin_type);
    cc_judgement_id elim = OK(cc_instr_eliminator_close(k, clause(opened, var(on_spin))));

    cc_entry_id p0 = extend(w_loops);
    cc_term reduced = iota_of(apply(elim, apply(wrap, var(p0))));
    assert(kind(reduced) == CC_APP && kind(child(reduced, 0)) == CC_APP);
    assert(child(child(reduced, 0), 0) == term_of(var(on_wrap)) && child(child(reduced, 0), 1) == term_of(var(p0)));
    cc_judgement_id lifted = OK(cc_instr_path_lambda(k, i, apply(elim, path_at(var(p0), i, 0))));
    cc_term shown = child(reduced, 1);
    /* The path abstraction a driver derives, family M(p0 @ i) included. */
    assert(kind(shown) == CC_PLAM && same(shown, term_of(lifted)));
    assert(kind(child(shown, 1)) == CC_APP && child(child(shown, 1), 0) == term_of(elim) &&
           kind(child(child(shown, 1), 1)) == CC_PAPP);

    cc_entry_id q0 = extend(pi_over(extend(unit), w_loops)), y0 = extend(unit);
    reduced = iota_of(apply(elim, apply(spin, var(q0))));
    assert(child(child(reduced, 0), 0) == term_of(var(on_spin)) && child(child(reduced, 0), 1) == term_of(var(q0)));
    cc_judgement_id lifted_q0 = lambda(y0, OK(cc_instr_path_lambda(k, i,
        apply(elim, path_at(apply(var(q0), var(y0)), i, 0)))));
    shown = child(reduced, 1);
    assert(kind(shown) == CC_LAM && kind(child(shown, 1)) == CC_PLAM && same(shown, term_of(lifted_q0)));
    puts("Iota lifts a path-valued position to ⟨i⟩ elim(p @ i), under its arity binders too.");
}

/* Dependent arity (section 3.3): Tree : U1 { leaf; node(A : U0, q : A → s); }.
 * Iota at node(Unit, q) gives m_node(Unit, q, λ (a : Unit). elim(q(a))): the
 * arity binder's domain is the data argument. */
static void arities(void) {
    cc_judgement_id unit = OK(cc_instr_unit(k));
    cc_entry_id s;
    cc_judgement_id sig = begin(1, &s);
    sig = admit(sig, var(s));
    cc_entry_id carrier = extend(universe(0));
    sig = admit(sig, pi_over(carrier, pi_over(extend(pi_over(extend(var(carrier)), var(s))), var(s))));
    cc_judgement_id tree = instance_of(sig);
    cc_judgement_id leaf = construct(tree, 0), node = construct(tree, 1);
    cc_entry_id v = motive_over(tree);
    cc_entry_id on_leaf = extend(at(v, leaf));
    cc_judgement_id opened = clause(OK(cc_instr_eliminator(k, var(v))), var(on_leaf));
    /* node's clause: Π (A : U0). Π (q : A → Tree). Π (q̄ : Π (a : A).
     * M(q(a))). M(node(A, q)). */
    cc_entry_id A = extend(universe(0));
    cc_entry_id q = extend(pi_over(extend(var(A)), tree)), a = extend(var(A));
    cc_entry_id q_bar = extend(pi_over(a, at(v, apply(var(q), var(a)))));
    cc_judgement_id node_type = pi_over(A, pi_over(q, pi_over(q_bar, at(v, apply(apply(node, var(A)), var(q))))));
    assert(same(type_of(opened), term_of(node_type)));
    cc_entry_id on_node = extend(node_type);
    cc_judgement_id elim = OK(cc_instr_eliminator_close(k, clause(opened, var(on_node))));
    cc_entry_id q0 = extend(pi_over(extend(unit), tree)), a0 = extend(unit);
    cc_term reduced = iota_of(apply(elim, apply(apply(node, unit), var(q0))));
    cc_term head = child(reduced, 0);
    assert(child(child(head, 0), 0) == term_of(var(on_node)) && child(child(head, 0), 1) == term_of(unit) &&
           child(head, 1) == term_of(var(q0)));
    cc_term shown = child(reduced, 1);
    assert(kind(shown) == CC_LAM && child(shown, 0) == term_of(unit));
    assert(same(shown, term_of(lambda(a0, apply(elim, apply(var(q0), var(a0)))))));
    puts("Iota instantiates an arity binder's domain at the data argument.");
}

/* Equivalence types where an operand holds a binder opened outside
 * (section 3.1). Built directly: Equiv(A, B)'s binders f and y take levels
 * above the operand's placeholder x = OPENED(0), so they never bind it:
 *   Σ (f : A → B). Π (y : B). IsContr(Σ (x' : A). Path(B, y, f x')). */
static cc_term fiber(cc_term a, cc_term b, uint32_t depth) {
    cc_term image = ck_make(k, CC_APP, 0, ck_make(k, CC_BOUND, 2 + depth, 0, 0, 0, 0), ck_make(k, CC_BOUND, 0, 0, 0, 0, 0), 0, 0);
    cc_term equality = ck_make(k, CC_PATH, 0, b, ck_make(k, CC_BOUND, 1 + depth, 0, 0, 0, 0), image, 0);
    return ck_make(k, CC_SIGMA, 0, a, equality, 0, 0);
}
static cc_term equivalence(cc_term a, cc_term b) {
    cc_term contraction = ck_make(k, CC_PATH, 0, fiber(a, b, 2), ck_make(k, CC_BOUND, 1, 0, 0, 0, 0),
                                  ck_make(k, CC_BOUND, 0, 0, 0, 0, 0), 0);
    cc_term contractible = ck_make(k, CC_SIGMA, 0, fiber(a, b, 0), ck_make(k, CC_PI, 0, fiber(a, b, 1), contraction, 0, 0), 0, 0);
    return ck_make(k, CC_SIGMA, 0, ck_make(k, CC_PI, 0, a, b, 0, 0), ck_make(k, CC_PI, 0, b, contractible, 0, 0), 0, 0);
}

static void equivalences(void) {
    cc_judgement_id unit = OK(cc_instr_unit(k));
    cc_entry_id family = extend(pi_over(extend(unit), universe(0)));
    ck_operation(k, CC_WORK_QUERY);
    cc_term x = ck_make(k, CC_OPENED, 0, 0, 0, 0, 0);
    cc_term held = ck_make(k, CC_APP, 0, term_of(var(family)), x, 0, 0), plain = term_of(unit);
    /* The placeholder on either side. */
    const cc_term operands[][2] = {{held, plain}, {plain, held}};
    for (unsigned n = 0; n < 2; ++n) {
        cc_term built = ck_equiv_type(k, operands[n][0], operands[n][1]);
        assert(built && !k->error[0] && k->nodes[built].opened == 1);
        assert(same(built, equivalence(operands[n][0], operands[n][1])));
        assert(ck_equiv_type(k, operands[n][0], operands[n][1]) == built);
    }
    /* Through the public API: λ (X : U0). comp^i U0 [j = 0 ↦ X] X computes to
     * a Glue type whose equivalence type is built while normalization has X
     * opened. Its normal form opened with an entry E is the normal form of
     * the body at E, where nothing is opened. */
    cc_term u0 = term_of(universe(0));
    cc_formula_id face = ck_endpoint_face(k, 1, 0);
    assert(face);
    cc_term composed = ck_make(k, CC_COMP, 0, u0, ck_make(k, CC_TUBE, face, bound(0), 0, 0, 0), bound(0), 0);
    cc_term over = OK(cc_kernel_normalize(k, make(CC_LAM, 0, u0, composed)));
    assert(kind(over) == CC_LAM && kind(child(over, 1)) == CC_GLUE);
    cc_entry_id e = extend(universe(0));
    cc_term at_entry = ck_make(k, CC_COMP, 0, u0, ck_make(k, CC_TUBE, face, term_of(var(e)), 0, 0, 0),
                               term_of(var(e)), 0);
    cc_term direct = OK(cc_kernel_normalize(k, at_entry));
    assert(same(OK(cc_kernel_instantiate(k, child(over, 1), e)), direct));
    puts("Equivalence types take their own binders above an operand's opened one.");
}

/* parts_agree, the Glue step's side condition (section 3.1), opens a common
 * binder of its two sides above the levels of both: of the Glue types
 * Glue(Π (y : Unit). F(y)) and Glue(Π (y : Unit). F(x)), x = OPENED(0) a
 * binder opened outside, only one side holds x; opened at a level of its
 * own, y is not x, the types do not agree, and glue [] (unglue b) stays. */
static void glue_sides(void) {
    cc_judgement_id unit = OK(cc_instr_unit(k));
    cc_entry_id family = extend(pi_over(extend(unit), universe(0)));
    cc_term b = term_of(var(extend(unit)));
    ck_operation(k, CC_WORK_QUERY);
    cc_term F = term_of(var(family)), unit_type = term_of(unit);
    cc_term x = ck_make(k, CC_OPENED, 0, 0, 0, 0, 0);
    cc_term own = ck_make(k, CC_PI, 0, unit_type, ck_make(k, CC_APP, 0, F, ck_make(k, CC_BOUND, 0, 0, 0, 0, 0), 0, 0), 0, 0);
    cc_term outer = ck_make(k, CC_PI, 0, unit_type, ck_make(k, CC_APP, 0, F, x, 0, 0), 0, 0);
    cc_term glue_own = ck_make(k, CC_GLUE, 0, own, 0, 0, 0), glue_outer = ck_make(k, CC_GLUE, 0, outer, 0, 0, 0);
    const cc_term sides[][2] = {{glue_own, glue_outer}, {glue_outer, glue_own}};
    for (unsigned n = 0; n < 2; ++n) {
        cc_term term = ck_make(k, CC_GLUE_TERM, 0, sides[n][0], ck_make(k, CC_UNGLUE, 0, sides[n][1], b, 0, 0), 0, 0);
        assert(term && ck_glue_step(k, term) == term && !k->error[0]);
        /* The control: one Glue type on both sides, and the step is b. */
        cc_term agreeing = ck_make(k, CC_GLUE_TERM, 0, sides[n][0], ck_make(k, CC_UNGLUE, 0, sides[n][0], b, 0, 0), 0, 0);
        assert(ck_glue_step(k, agreeing) == b && !k->error[0]);
    }
    puts("The Glue step's sides open a common binder above both.");
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    apart();
    lifting();
    arities();
    equivalences();
    glue_sides();
    assert(!cc_kernel_error(k)[0]);
    cc_kernel_free(k);
    return 0;
}
