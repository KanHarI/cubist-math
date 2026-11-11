/* Replace's entries and the boundary of loose terms (sections 3.6, 3.7 and
 * 5.1 of docs/roadmaps/kernel/locally-nameless-kernel.md): one refusal per
 * freshness condition, each with its own message, the accepted case, the
 * derivation memo keyed by the entry vector, cc_kernel_instantiate's
 * refusal, and the queries' answers on loose terms. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;
static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) { fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k)); assert(0); }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)
/* A refusal, with the message it gives, cleared. */
static void refused(uint32_t id, const char *message, int line) {
    if (id || !strstr(cc_kernel_error(k), message)) {
        fprintf(stderr, "line %d: expected \"%s\", got %u: %s\n", line, message, id, cc_kernel_error(k));
        assert(0);
    }
    cc_kernel_clear_error(k);
}
#define REFUSED(x, message) refused((x), (message), __LINE__)

static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info r; assert(cc_kernel_judgement(k, j, &r)); return r; }
static cc_term child(cc_term t, unsigned i) { cc_term c[4]; assert(cc_kernel_node(k, t, NULL, NULL, c)); return c[i]; }
static cc_term_kind kind(cc_term t) { cc_term_kind r; assert(cc_kernel_node(k, t, &r, NULL, NULL)); return r; }
static uint32_t payload(cc_term t) { uint32_t r; assert(cc_kernel_node(k, t, NULL, &r, NULL)); return r; }
static size_t context_size(cc_judgement_id j) { size_t n = 0; while (cc_kernel_judgement_context(k, j, n)) ++n; return n; }
static cc_judgement_id var(cc_entry_id e) { return OK(cc_instr_variable(k, e)); }
static cc_term make(cc_term_kind kind, uint32_t payload, cc_term a, cc_term b) {
    return OK(cc_kernel_term(k, kind, payload, a, b, 0, 0));
}
static cc_term leaf(cc_term_kind kind, uint32_t payload) { return make(kind, payload, 0, 0); }

static cc_judgement_id unit, point, universe;
static cc_entry_id ambient;
/* tt ≡ (λ (z : Unit). tt)(x): its right side uses x, its left side not. */
static cc_judgement_id unfolding(cc_entry_id x) {
    cc_entry_id z = OK(cc_instr_extend(k, unit));
    cc_judgement_id redex = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, z, point)), var(x)));
    return OK(cc_instr_symmetry(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, redex)), 1, NULL, 0, CC_STEP_BETA))));
}

/* Each condition of section 3.6 refused with its own message, and the
 * accepted replacement whose right side uses the binder's variable. */
static void conditions(void) {
    static const uint8_t body[] = {1}, inner[] = {1, 1};
    cc_entry_id y = OK(cc_instr_extend(k, unit));
    cc_judgement_id pairs = OK(cc_instr_sigma(k, y, unit));
    /* 1. λ (x : Unit). (x, e) rewritten by reflexivity at (e, e) with e, an
     * ambient entry, for x: opened with e, the body is (e, e), and the
     * result would bind e. */
    cc_entry_id x = OK(cc_instr_extend(k, unit));
    cc_judgement_id lambda = OK(cc_instr_lambda(k, x, OK(cc_instr_pair(k, pairs, var(x), var(ambient)))));
    cc_judgement_id with_ambient = OK(cc_instr_refl(k, OK(cc_instr_pair(k, pairs, var(ambient), var(ambient)))));
    cc_judgement_id over = OK(cc_instr_refl(k, lambda));
    /* The rewritten judgement holds e: λ … (x, e) mentions it. */
    REFUSED(cc_instr_replace(k, over, 1, body, 1, with_ambient, &ambient, 1),
            "A replacement's entry for a binder is already in the rewritten judgement's context.");
    /* 2. One entry for two binders. */
    cc_entry_id a = OK(cc_instr_extend(k, unit)), b = OK(cc_instr_extend(k, unit)), f = OK(cc_instr_extend(k, unit));
    cc_judgement_id nested = OK(cc_instr_lambda(k, a, OK(cc_instr_lambda(k, b, OK(cc_instr_pair(k, pairs, var(a), var(b)))))));
    cc_entry_id same[] = {f, f};
    REFUSED(cc_instr_replace(k, OK(cc_instr_refl(k, nested)), 1, inner, 2,
                             OK(cc_instr_refl(k, OK(cc_instr_pair(k, pairs, var(f), var(f))))), same, 2),
            "A replacement gives one entry to two of its binders.");
    /* 3. An entry of the wrong type, of the wrong kind, or whose binder's
     * type needs an outer binder that got none. */
    cc_entry_id empty = OK(cc_instr_extend(k, OK(cc_instr_void(k))));
    REFUSED(cc_instr_replace(k, over, 1, body, 1, with_ambient, &empty, 1),
            "A replacement's entry for a binder is not at the binder's domain.");
    cc_entry_id level = OK(cc_instr_level(k));
    REFUSED(cc_instr_replace(k, over, 1, body, 1, with_ambient, &level, 1),
            "A replacement takes a level entry for a level binder, and a term entry for a term binder.");
    cc_entry_id A = OK(cc_instr_extend(k, universe)), member = OK(cc_instr_extend(k, var(A)));
    cc_judgement_id dependent = OK(cc_instr_lambda(k, A, OK(cc_instr_lambda(k, member, var(member)))));
    cc_entry_id B = OK(cc_instr_extend(k, universe)), element = OK(cc_instr_extend(k, var(B)));
    cc_entry_id outer_none[] = {0, element};
    REFUSED(cc_instr_replace(k, OK(cc_instr_refl(k, dependent)), 1, inner, 2, OK(cc_instr_refl(k, var(element))), outer_none, 2),
            "A replacement's entry for a binder has a type that needs an outer binder given no entry.");
    /* 4. No entry for a binder the occurrence uses. */
    cc_entry_id none = 0;
    REFUSED(cc_instr_replace(k, over, 1, body, 1, with_ambient, &none, 1),
            "A replacement gives no entry to a binder its occurrence uses.");
    /* 5. The equality keeps an entry that depends on a given one: for
     * λ (A : U0). λ (m : A). m, at λ (m : A). m opened with B, the equality
     * λ (m : B). m ≡ (λ (z : B). λ (m : B). m)(b) holds b : B. */
    cc_entry_id held = OK(cc_instr_extend(k, var(B))), z = OK(cc_instr_extend(k, var(B))), m = OK(cc_instr_extend(k, var(B)));
    cc_judgement_id identity = OK(cc_instr_lambda(k, m, var(m)));
    cc_judgement_id redex = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, z, identity)), var(held)));
    cc_judgement_id keeps = OK(cc_instr_symmetry(k, OK(cc_instr_step(k, OK(cc_instr_refl(k, redex)), 1, NULL, 0, CC_STEP_BETA))));
    REFUSED(cc_instr_replace(k, OK(cc_instr_refl(k, dependent)), 1, body, 1, keeps, &B, 1),
            "A replacement's equality keeps an entry that depends on a binder's entry.");
    /* 6. Accepted: λ (x : Unit). tt with tt ≡ (λ z. tt)(x) for x, whose
     * right side uses x and whose left side does not: the result binds it. */
    cc_entry_id u = OK(cc_instr_extend(k, unit));
    cc_judgement_id constant = OK(cc_instr_refl(k, OK(cc_instr_lambda(k, u, point))));
    cc_judgement_id result = OK(cc_instr_replace(k, constant, 1, body, 1, unfolding(u), &u, 1));
    cc_term replaced = info(result).other;
    assert(kind(replaced) == CC_LAM && kind(child(replaced, 1)) == CC_APP);
    cc_term argument = child(child(replaced, 1), 1);
    assert(kind(argument) == CC_BOUND && payload(argument) == 0);
    assert(context_size(result) == 0);
    /* Entries for nested binders may depend on each other, B and b : B for
     * λ (A : U0). λ (m : A). m at m, and are discharged together. */
    cc_entry_id both[] = {B, element};
    cc_judgement_id together = OK(cc_instr_replace(k, OK(cc_instr_refl(k, dependent)), 1, inner, 2,
                                                   OK(cc_instr_refl(k, var(element))), both, 2));
    assert(info(together).other == info(dependent).term && context_size(together) == 0);
    puts("Replace: each freshness condition refused with its own message; a right side's binder use accepted.");
}

/* The derivation memo keys a replacement by its entries (section 3.7). */
static void replay(void) {
    static const uint8_t body[] = {1};
    cc_entry_id x = OK(cc_instr_extend(k, unit));
    cc_judgement_id constant = OK(cc_instr_refl(k, OK(cc_instr_lambda(k, x, point)))), by = unfolding(x);
    cc_entry_id given[] = {x}, none[] = {0};
    cc_judgement_id bound = OK(cc_instr_replace(k, constant, 1, body, 1, by, given, 1));
    cc_judgement_id free_ = OK(cc_instr_replace(k, constant, 1, body, 1, by, none, 1));
    /* Different terms and contexts: with x the result binds it, with 0 it
     * keeps x free, in its context. */
    assert(bound != free_ && info(bound).other != info(free_).other);
    assert(context_size(bound) == 0 && context_size(free_) == 1);
    cc_term argument = child(child(info(free_).other, 1), 1);
    assert(kind(argument) == CC_CONTEXT && payload(argument) == x);
    /* The same vector again is the same judgement. */
    assert(OK(cc_instr_replace(k, constant, 1, body, 1, by, given, 1)) == bound);
    assert(OK(cc_instr_replace(k, constant, 1, body, 1, by, none, 1)) == free_);
    /* A vector refused after an accepted one with the same premises and
     * position is still refused. */
    cc_entry_id level = OK(cc_instr_level(k));
    REFUSED(cc_instr_replace(k, constant, 1, body, 1, by, &level, 1),
            "A replacement takes a level entry for a level binder, and a term entry for a term binder.");
    REFUSED(cc_instr_replace(k, constant, 1, body, 1, by, &level, 1),
            "A replacement takes a level entry for a level binder, and a term entry for a term binder.");
    assert(OK(cc_instr_replace(k, constant, 1, body, 1, by, given, 1)) == bound);
    puts("Replace's derivation memo tells entry vectors apart.");
}

/* cc_kernel_instantiate refuses an entry the body already mentions, as the
 * reused entry of λ (x : A). λ (x : A). b would be, and the queries take
 * loose terms as section 5.1 says. */
static void boundary(void) {
    cc_term unit_type = info(unit).term, ambient_term = leaf(CC_CONTEXT, ambient);
    cc_term mentions = make(CC_LAM, 0, unit_type, ambient_term);
    REFUSED(cc_kernel_instantiate(k, mentions, ambient), "A binder's body already mentions the entry it would be opened with.");
    /* (λ (y : Unit). y)(#0): its weak head is #0, the same loose index, and
     * no placeholder; opened with x first, it is x. */
    cc_term loose = leaf(CC_BOUND, 0);
    cc_term redex = make(CC_APP, 0, make(CC_LAM, 0, unit_type, leaf(CC_BOUND, 0)), loose);
    assert(OK(cc_kernel_whnf(k, redex)) == loose);
    cc_entry_id x = OK(cc_instr_extend(k, unit));
    cc_term opened = OK(cc_kernel_instantiate(k, redex, x));
    cc_term head = OK(cc_kernel_whnf(k, opened));
    assert(kind(head) == CC_CONTEXT && payload(head) == x);
    /* A loose term deeper inside: (λ (y : Unit). (y, #1))(tt) opens and
     * closes around its weak head, which keeps #0 where #1 was. */
    cc_term pair_type = make(CC_SIGMA, 0, unit_type, unit_type), tt = info(point).term;
    cc_term deep = make(CC_APP, 0, make(CC_LAM, 0, unit_type,
        OK(cc_kernel_term(k, CC_PAIR, 0, pair_type, leaf(CC_BOUND, 0), leaf(CC_BOUND, 1), 0))), tt);
    cc_term deep_head = OK(cc_kernel_whnf(k, deep));
    assert(kind(deep_head) == CC_PAIR && child(deep_head, 1) == tt && child(deep_head, 2) == loose);
    REFUSED(cc_kernel_normalize(k, redex), "Normalization reached a term with a loose bound variable.");
    REFUSED(cc_kernel_normalize_folded(k, redex), "Normalization reached a term with a loose bound variable.");
    REFUSED(cc_kernel_equiv_type(k, loose, unit_type), "An equivalence type's operands must be locally closed.");
    REFUSED(cc_kernel_equiv_type(k, unit_type, loose), "An equivalence type's operands must be locally closed.");
    /* A level instruction refuses a loose level. */
    REFUSED(cc_instr_universe(k, loose), "Unbound level variable.");
    puts("Loose terms: weak heads keep their indices; normal forms, equivalence types and levels refuse them.");
}

int main(void) {
    k = cc_kernel_new(); assert(k);
    unit = OK(cc_instr_unit(k));
    point = OK(cc_instr_point(k));
    universe = OK(cc_instr_universe(k, leaf(CC_LCONST, 0)));
    ambient = OK(cc_instr_extend(k, unit));
    conditions();
    replay();
    boundary();
    cc_kernel_free(k);
    return 0;
}
