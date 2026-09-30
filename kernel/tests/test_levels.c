/* Universe levels (G0 §2.4): normal forms, equality and order, against the
 * specification's acceptance cases and against brute-force evaluation over
 * assignments of the variables. Raw syntax is used deliberately: these are
 * the arithmetic's own tests, not typing judgements. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static cc_kernel *k;

enum { X = 1, Y, Z };
static cc_term lconst(uint32_t tier, uint32_t n) { return ck_make(k, CC_LCONST, tier << 16 | n, 0, 0, 0, 0); }
static cc_term var(uint32_t symbol) { return ck_var(k, symbol); }
static cc_term succ(cc_term level, uint32_t n) { return ck_make(k, CC_LSUCC, n, level, 0, 0, 0); }
static cc_term lmax(cc_term a, cc_term b) { return ck_make(k, CC_LMAX, 0, a, b, 0, 0); }
static cc_term canonical(cc_term level) { cc_term c = ck_level_canonical(k, level); assert(c); return c; }

static void expect_error(bool ok, const char *fragment) {
    assert(!ok);
    if (!strstr(k->error, fragment)) {
        fprintf(stderr, "expected \"%s\", got \"%s\"\n", fragment, k->error);
        assert(0);
    }
    cc_kernel_clear_error(k);
}

/* The acceptance cases of §5.1, as arithmetic. */
static void specification_cases(void) {
    cc_term x = var(X), y = var(Y), z = var(Z), omega = lconst(1, 0);
    assert(ck_level_equal(k, lmax(x, x), x));                                        /* L1 */
    assert(ck_level_equal(k, lmax(succ(x, 1), x), succ(x, 1)));                      /* L2 */
    assert(ck_level_equal(k, lmax(lconst(0, 0), x), x));                             /* L3 */
    assert(ck_level_equal(k, lmax(lconst(0, 1), succ(x, 1)), succ(x, 1)));           /* L4 */
    assert(ck_level_equal(k, lmax(x, y), lmax(y, x)));                               /* L5 */
    assert(ck_level_equal(k, lmax(x, lmax(y, z)), lmax(lmax(x, y), z)));             /* L6 */
    assert(ck_level_equal(k, succ(lmax(x, y), 1), lmax(succ(x, 1), succ(y, 1))));    /* L7 */
    assert(!ck_level_equal(k, lmax(lconst(0, 1), x), succ(x, 1)));                   /* L8 */
    assert(!ck_level_equal(k, lmax(lconst(0, 1), x), x));                            /* L9 */
    assert(ck_level_leq(k, lconst(0, 0), x) && !ck_level_leq(k, x, lconst(0, 0)));  /* L10 */
    assert(!ck_level_leq(k, lconst(0, 1), x) && ck_level_leq(k, lconst(0, 1), succ(x, 1))); /* L11 */
    assert(ck_level_leq(k, x, lmax(x, y)) && !ck_level_leq(k, lmax(x, y), x));       /* L12 */
    assert(!ck_level_leq(k, succ(x, 1), lmax(x, succ(y, 1))));                       /* L13 */
    assert(!ck_level_leq(k, x, y) && !ck_level_leq(k, y, x));                        /* L14 */
    assert(!ck_level_equal(k, x, y));                                                /* L15 */
    assert(ck_level_equal(k, lmax(x, omega), omega));                                /* L20 */
    assert(ck_level_equal(k, succ(lmax(succ(x, 3), omega), 1), lconst(1, 1)));       /* L21 */
    assert(ck_level_leq(k, x, omega) && !ck_level_leq(k, omega, x));                 /* L22 */
    assert(ck_level_leq(k, lconst(1, 5), lconst(2, 0)) && !ck_level_leq(k, lconst(2, 0), lconst(1, 1000))); /* L23 */
    assert(ck_level_equal(k, lmax(lconst(1, 7), lconst(2, 0)), lconst(2, 0)));      /* L24 */
    assert(!ck_level_equal(k, omega, succ(x, 1)) && !ck_level_equal(k, omega, lmax(x, y))); /* L25 */
    assert(!k->error[0]);
}

/* Canonical nodes: one handle per normal form, idempotent, and in the
 * printed shapes of §2.4's table. */
static void canonical_forms(void) {
    cc_term x = var(X), y = var(Y);
    assert(canonical(lmax(x, x)) == x);
    assert(canonical(lmax(succ(x, 1), x)) == succ(x, 1));
    assert(canonical(lmax(lconst(0, 0), x)) == x);
    assert(canonical(lmax(lconst(0, 1), succ(x, 1))) == succ(x, 1));
    assert(canonical(lmax(lconst(0, 1), x)) == lmax(x, lconst(0, 1)));
    assert(canonical(succ(lmax(x, y), 1)) == lmax(succ(x, 1), succ(y, 1)));
    assert(canonical(lmax(y, x)) == canonical(lmax(x, y)));
    assert(canonical(succ(succ(x, 2), 3)) == succ(x, 5));
    assert(canonical(lmax(lconst(1, 7), lconst(2, 0))) == lconst(2, 0));
    assert(canonical(canonical(lmax(lconst(0, 4), succ(y, 2)))) == canonical(lmax(lconst(0, 4), succ(y, 2))));
    assert(ck_level_max(k, lconst(0, 3), lconst(0, 5)) == lconst(0, 5));
    assert(ck_level_max(k, x, lconst(1, 0)) == lconst(1, 0));
    assert(ck_level_succ(k, lmax(x, lconst(0, 2))) == lmax(succ(x, 1), lconst(0, 3)));
    assert(ck_level_finite(k, lmax(x, lconst(0, 9))) && !ck_level_finite(k, lconst(1, 0)));
    /* The limit of §2.7: ω when the variable occurs in the normal form. */
    assert(ck_level_limit(k, X, succ(x, 1)) == lconst(1, 0));
    assert(ck_level_limit(k, X, succ(y, 1)) == succ(y, 1));
    assert(ck_level_limit(k, X, lmax(x, lconst(1, 2))) == lconst(1, 2));
    assert(ck_level_limit(k, X, lconst(0, 0)) == lconst(0, 0));
    /* The term checker's universes: closed finite levels only. */
    uint32_t n = 0;
    assert(ck_universe_number(k, ck_universe(k, lmax(lconst(0, 1), lconst(0, 0))), &n) && n == 1);
    expect_error(ck_universe_number(k, ck_universe(k, x), &n), "closed finite");
    expect_error(ck_universe_number(k, ck_universe(k, lconst(1, 0)), &n), "closed finite");
    /* Universes compare by level (U-Eq) and by order (U-Cum), across tiers. */
    assert(ck_alpha_equal(k, ck_universe(k, lmax(lconst(0, 1), lconst(0, 0))), ck_universe_at(k, 1)));
    assert(!ck_alpha_equal(k, ck_universe_at(k, 1), ck_universe_at(k, 2)));
    assert(ck_syntactic_cumulative(k, ck_universe_at(k, 7), ck_universe(k, lconst(1, 0))));
    assert(!ck_syntactic_cumulative(k, ck_universe(k, lconst(1, 0)), ck_universe_at(k, 7)));
    /* Under level binders, levels compare through the renaming (G0 §2.9). */
    cc_term bound = ck_make(k, CC_LBOUND, 1, 0, 0, 0, 0);
    cc_term by_x = ck_make(k, CC_LLAM, X, bound, ck_universe(k, succ(x, 1)), 0, 0);
    cc_term by_y = ck_make(k, CC_LLAM, Y, bound, ck_universe(k, succ(y, 1)), 0, 0);
    cc_term free_x = ck_make(k, CC_LLAM, Y, bound, ck_universe(k, succ(x, 1)), 0, 0);
    assert(ck_alpha_equal(k, by_x, by_y) && !ck_alpha_equal(k, by_x, free_x));
    cc_term wide_bound = ck_make(k, CC_LLAM, X, ck_make(k, CC_LBOUND, 2, 0, 0, 0, 0), ck_universe(k, succ(x, 1)), 0, 0);
    assert(!ck_alpha_equal(k, by_x, wide_bound));
    assert(!ck_alpha_equal(k, lconst(0, 1), lconst(0, 2)) && ck_alpha_equal(k, lmax(x, y), lmax(y, x)));
    cc_term pair_xy = ck_make(k, CC_LLAM, X, bound, ck_make(k, CC_LLAM, Y, bound, ck_universe(k, lmax(x, y)), 0, 0), 0, 0);
    cc_term pair_yx = ck_make(k, CC_LLAM, Y, bound, ck_make(k, CC_LLAM, X, bound, ck_universe(k, lmax(y, x)), 0, 0), 0, 0);
    cc_term swapped = ck_make(k, CC_LLAM, Y, bound, ck_make(k, CC_LLAM, X, bound, ck_universe(k, lmax(x, succ(y, 1))), 0, 0), 0, 0);
    assert(ck_alpha_equal(k, pair_xy, pair_yx) && !ck_alpha_equal(k, pair_xy, swapped));
    cc_term f = var(20);
    assert(ck_alpha_equal(k, ck_make(k, CC_LAPP, 0, f, lmax(lconst(0, 0), lconst(0, 0)), 0, 0),
                          ck_make(k, CC_LAPP, 0, f, lconst(0, 0), 0, 0)));                 /* Inst, S11 */
    /* ∀-β substitutes, avoiding capture, and leaves levels in normal form;
     * ∀-η contracts. */
    cc_term instance = ck_whnf(k, ck_make(k, CC_LAPP, 0, pair_xy, y, 0, 0));
    assert(k->nodes[instance].kind == CC_LLAM && k->nodes[instance].payload != Y);
    cc_term at_zero = ck_whnf(k, ck_make(k, CC_LAPP, 0, instance, lconst(0, 0), 0, 0));
    assert(at_zero == ck_universe(k, y));                                                  /* S5 */
    assert(ck_canonical_levels(k, ck_universe(k, lmax(lconst(0, 1), lconst(0, 0)))) == ck_universe_at(k, 1));
    cc_term eta = ck_make(k, CC_LLAM, 21, bound, ck_make(k, CC_LAPP, 0, f, var(21), 0, 0), 0, 0);
    assert(ck_whnf(k, eta) == f);
    assert(!k->error[0]);
}

/* Malformed levels and resource bounds reject, and never crash (R1, R2). */
static void bounds_and_malformed(void) {
    cc_term x = var(X);
    assert(ck_level_constant(k, 0, CC_LEVEL_MAX));
    expect_error(ck_level_succ(k, lconst(0, CC_LEVEL_MAX)) != 0, "bound");
    expect_error(ck_level_succ(k, succ(x, CC_LEVEL_MAX)) != 0, "bound");
    expect_error(ck_level_equal(k, lconst(CC_TIER_MAX + 1, 0), lconst(0, 0)), "bound");
    expect_error(ck_level_constant(k, CC_TIER_MAX + 1, 0) != 0, "bound");
    expect_error(ck_level_equal(k, ck_make(k, CC_LSUCC, 0, x, 0, 0, 0), x), "at least one");
    expect_error(ck_level_equal(k, ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0), x), "Expected a level");
    expect_error(ck_level_equal(k, ck_make(k, CC_LBOUND, 1, 0, 0, 0, 0), x), "A bound is not a level");
    expect_error(ck_make(k, CC_U, 1, 0, 0, 0, 0) != 0, "payload must be zero");
    /* A level shared as a DAG but exponential as a tree exhausts the budget. */
    cc_term wide = lconst(0, 1);
    for (unsigned i = 0; i < 60; ++i)
        wide = lmax(wide, wide);
    uint64_t budget = k->budget;
    k->budget = 100000;
    assert(!ck_level_equal(k, wide, lconst(0, 1)));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    k->budget = budget;
}

/* Brute force. A value is an ordinal below ω², (tier, n); a raw level is
 * evaluated under an assignment of natural numbers to X, Y and Z. */
typedef struct { uint32_t tier, n; } ordinal;
static ordinal evaluate(cc_term level, const uint32_t *rho) {
    cc_node node = k->nodes[level];
    switch (node.kind) {
    case CC_LCONST: return (ordinal){node.payload >> 16, node.payload & 0xffffu};
    case CC_VAR: return (ordinal){0, rho[node.payload - X]};
    case CC_LSUCC: { ordinal v = evaluate(node.child[0], rho); v.n += node.payload; return v; }
    case CC_LMAX: {
        ordinal a = evaluate(node.child[0], rho), b = evaluate(node.child[1], rho);
        return a.tier > b.tier || (a.tier == b.tier && a.n >= b.n) ? a : b;
    }
    default: assert(0); return (ordinal){0, 0};
    }
}
static bool below(ordinal a, ordinal b) { return a.tier < b.tier || (a.tier == b.tier && a.n <= b.n); }

static uint64_t seed = 0x2545F4914F6CDD1DULL;
static uint32_t roll(uint32_t bound) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    return (uint32_t)(seed % bound);
}
/* Constants below 4 in tiers 0 to 2, successors of 1 or 2, depth at most 3:
 * every finite part is at most 9, so assignments up to 2·9 + 2 decide
 * Lemma 2's order (its proof takes a variable above the other side's c). */
static cc_term random_level(unsigned depth) {
    switch (depth ? roll(5) : roll(2)) {
    case 0: return roll(4) ? lconst(0, roll(4)) : lconst(1 + roll(2), roll(4));
    case 1: return var(X + roll(3));
    case 2: return succ(random_level(depth - 1), 1 + roll(2));
    default: return lmax(random_level(depth - 1), random_level(depth - 1));
    }
}

static void property(void) {
    enum { PAIRS = 1500, RANGE = 20 };
    unsigned equal = 0, ordered = 0;
    for (unsigned i = 0; i < PAIRS; ++i) {
        cc_term a = random_level(3), b = i % 3 ? random_level(3) : canonical(a);
        bool leq = true, geq = true;
        uint32_t rho[3];
        for (rho[0] = 0; rho[0] <= RANGE; ++rho[0])
            for (rho[1] = 0; rho[1] <= RANGE; ++rho[1])
                for (rho[2] = 0; rho[2] <= RANGE; ++rho[2]) {
                    ordinal va = evaluate(a, rho), vb = evaluate(b, rho);
                    leq &= below(va, vb);
                    geq &= below(vb, va);
                }
        assert(ck_level_leq(k, a, b) == leq);
        assert(ck_level_leq(k, b, a) == geq);
        assert(ck_level_equal(k, a, b) == (leq && geq));
        /* Canonical nodes are one handle exactly for equal levels. */
        assert((canonical(a) == canonical(b)) == (leq && geq));
        /* Lemma 1: the canonical node denotes the same ordinal. */
        for (unsigned trial = 0; trial < 8; ++trial) {
            uint32_t sample[3] = {roll(RANGE), roll(RANGE), roll(RANGE)};
            ordinal va = evaluate(a, sample), vc = evaluate(canonical(a), sample);
            assert(va.tier == vc.tier && va.n == vc.n);
        }
        equal += leq && geq;
        ordered += leq || geq;
    }
    assert(!k->error[0]);
    printf("levels: %u random pairs, %u equal and %u ordered, agree with evaluation\n", (unsigned)PAIRS, equal, ordered);
}

int main(void) {
    k = cc_kernel_new();
    assert(k);
    specification_cases();
    canonical_forms();
    bounds_and_malformed();
    property();
    cc_kernel_free(k);
    return 0;
}
