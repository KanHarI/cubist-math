/* Universe levels (G0 specification, §2.3–2.4), decided by arithmetic.
 *
 * A level is an ordinal below ω²: a constant ω·tier + n (LConst), a
 * successor ℓ + n (LSucc), a maximum (LMax), or a variable (Var) that ranges
 * over the natural numbers. Its normal form is either finite, (c, m): a
 * tier-0 constant c and an offset m(x) ≤ c for finitely many variables x,
 * denoting max(c, max over x of x + m(x)); or a constant of tier 1 or above,
 * which absorbs every variable, since every finite value lies below it.
 *
 * Two levels agree for every assignment of their variables exactly when their
 * normal forms are identical (Corollary 3), and one lies below the other for
 * every assignment exactly when Lemma 2's condition holds. So equality and
 * order are computed, never searched for. The canonical level node of a
 * normal form is unique, so with shared syntax two canonical levels are equal
 * exactly when they are one handle.
 *
 * The bounds CC_LEVEL_MAX, on the finite part within a tier, and CC_TIER_MAX
 * are resource limits: exceeding one rejects, and never accepts. */
#include "term_internal.h"

static const char bound_exceeded[] = "A universe level exceeds the kernel's bound.";

void ck_level_nf_free(cc_level_nf *nf) {
    free(nf->terms);
    *nf = (cc_level_nf){0};
}

static bool reserve_terms(cc_kernel *k, cc_level_nf *nf, uint32_t count) {
    if (count <= nf->capacity)
        return true;
    uint32_t capacity = nf->capacity ? nf->capacity : 4;
    while (capacity < count) {
        if (capacity > UINT32_MAX / 2 || (size_t)capacity * 2 > SIZE_MAX / sizeof *nf->terms)
            return ck_fail(k, "Level normal form too large.");
        capacity *= 2;
    }
    cc_level_term *terms = realloc(nf->terms, (size_t)capacity * sizeof *terms);
    if (!terms)
        return ck_fail(k, "Level normal form allocation failed.");
    nf->terms = terms;
    nf->capacity = capacity;
    return true;
}

/* nf(ℓ + n): successor stays within the tier, and every offset rises. */
static bool add(cc_kernel *k, cc_level_nf *nf, uint64_t successors) {
    if (!successors)
        return true;
    if (nf->constant + successors > CC_LEVEL_MAX)
        return ck_fail(k, bound_exceeded);
    nf->constant += (uint32_t)successors;
    for (uint32_t i = 0; i < nf->count; ++i)
        nf->terms[i].offset += (uint32_t)successors;
    return true;
}

/* nf(max(ℓ, ℓ')) into a: a constant of tier 1 or above absorbs a finite form,
 * two constants take the ordinal maximum, and two finite forms the larger
 * constant and the larger offset of each variable. */
static bool join(cc_kernel *k, cc_level_nf *a, const cc_level_nf *b) {
    if (a->tier || b->tier) {
        if (!a->tier || (b->tier && (b->tier > a->tier || (b->tier == a->tier && b->constant > a->constant)))) {
            a->tier = b->tier;
            a->constant = b->constant;
        }
        a->count = 0;
        return true;
    }
    if (b->count) {
        size_t total = (size_t)a->count + b->count;
        cc_level_term *merged = malloc(total * sizeof *merged);
        if (!merged)
            return ck_fail(k, "Level normal form allocation failed.");
        uint32_t i = 0, j = 0, n = 0;
        while (i < a->count || j < b->count) {
            if (j == b->count || (i < a->count && a->terms[i].key < b->terms[j].key))
                merged[n++] = a->terms[i++];
            else if (i == a->count || b->terms[j].key < a->terms[i].key)
                merged[n++] = b->terms[j++];
            else {
                cc_level_term term = a->terms[i++];
                if (b->terms[j].offset > term.offset)
                    term.offset = b->terms[j].offset;
                ++j;
                merged[n++] = term;
            }
        }
        free(a->terms);
        a->terms = merged;
        a->capacity = (uint32_t)total;
        a->count = n;
    }
    if (b->constant > a->constant)
        a->constant = b->constant;
    return true;
}

/* The normal form by structural recursion. Each node visited costs a step of
 * the budget, so a level shared as a DAG but huge as a tree is rejected
 * rather than expanded without bound; recursion is bounded by the syntax
 * depth, and successor chains are walked iteratively. */
static bool normal(cc_kernel *k, cc_term level, cc_level_nf *out) {
    uint64_t successors = 0;
    for (;;) {
        if (!level || level >= k->count)
            return ck_fail(k, "Expected a level.");
        if (!ck_tick(k, true))
            return false;
        if (k->nodes[level].kind != CC_LSUCC)
            break;
        if (!k->nodes[level].payload)
            return ck_fail(k, "A level successor counts at least one.");
        successors += k->nodes[level].payload;
        if (successors > CC_LEVEL_MAX)
            return ck_fail(k, bound_exceeded);
        level = k->nodes[level].child[0];
    }
    cc_node n = k->nodes[level];
    switch (n.kind) {
    case CC_LCONST:
        if ((n.payload >> 16) > CC_TIER_MAX)
            return ck_fail(k, bound_exceeded);
        out->tier = n.payload >> 16;
        out->constant = n.payload & 0xffffu;
        out->count = 0;
        break;
    case CC_VAR:
        if (!reserve_terms(k, out, 1))
            return false;
        out->tier = out->constant = 0;
        out->count = 1;
        out->terms[0] = (cc_level_term){n.payload, 0};
        break;
    case CC_LMAX: {
        cc_level_nf right = {0};
        bool joined = normal(k, n.child[0], out) && normal(k, n.child[1], &right) && join(k, out, &right);
        ck_level_nf_free(&right);
        if (!joined)
            return false;
        break;
    }
    case CC_LBOUND:
        return ck_fail(k, "A bound is not a level.");
    default:
        return ck_fail(k, "Expected a level.");
    }
    return add(k, out, successors);
}

bool ck_level_normal(cc_kernel *k, cc_term level, cc_level_nf *out) {
    *out = (cc_level_nf){0};
    if (!normal(k, level, out)) {
        ck_level_nf_free(out);
        return false;
    }
    return true;
}

cc_term ck_level_constant(cc_kernel *k, uint32_t tier, uint32_t value) {
    if (tier > CC_TIER_MAX || value > CC_LEVEL_MAX)
        return ck_fail(k, bound_exceeded), 0;
    return ck_make(k, CC_LCONST, tier << 16 | value, 0, 0, 0, 0);
}

/* The canonical node of a normal form: a constant; or the maximum, nested to
 * the right in key order, of each x + m(x), followed by the constant c when
 * it is larger than every offset or there are no variables. */
cc_term ck_level_build(cc_kernel *k, const cc_level_nf *nf) {
    if (nf->tier)
        return ck_level_constant(k, nf->tier, nf->constant);
    uint32_t top = 0;
    for (uint32_t i = 0; i < nf->count; ++i)
        if (nf->terms[i].offset > top)
            top = nf->terms[i].offset;
    cc_term result = !nf->count || nf->constant > top ? ck_level_constant(k, 0, nf->constant) : 0;
    for (uint32_t i = nf->count; i-- > 0;) {
        if (nf->terms[i].key > UINT32_MAX)
            return ck_fail(k, "A level variable's key is not a symbol."), 0;
        cc_term part = ck_var(k, (uint32_t)nf->terms[i].key);
        if (part && nf->terms[i].offset)
            part = ck_make(k, CC_LSUCC, nf->terms[i].offset, part, 0, 0, 0);
        result = result ? ck_make(k, CC_LMAX, 0, part, result, 0, 0) : part;
        if (!result)
            return 0;
    }
    return result;
}

static bool nf_equal(const cc_level_nf *a, const cc_level_nf *b) {
    if (a->tier != b->tier || a->constant != b->constant || a->count != b->count)
        return false;
    for (uint32_t i = 0; i < a->count; ++i)
        if (a->terms[i].key != b->terms[i].key || a->terms[i].offset != b->terms[i].offset)
            return false;
    return true;
}

/* Lemma 2. Finite below finite: the constant, and each variable with no
 * larger an offset. Finite below a constant always; a constant below a finite
 * form never; constants as ordinals. */
static bool nf_leq(const cc_level_nf *a, const cc_level_nf *b) {
    if (!a->tier && !b->tier) {
        if (a->constant > b->constant)
            return false;
        uint32_t j = 0;
        for (uint32_t i = 0; i < a->count; ++i) {
            while (j < b->count && b->terms[j].key < a->terms[i].key)
                ++j;
            if (j == b->count || b->terms[j].key != a->terms[i].key || b->terms[j].offset < a->terms[i].offset)
                return false;
        }
        return true;
    }
    if (!a->tier)
        return true;
    if (!b->tier)
        return false;
    return a->tier < b->tier || (a->tier == b->tier && a->constant <= b->constant);
}

/* Two closed tier-0 constants, the common case, need no normal form. */
static bool small_constant(const cc_kernel *k, cc_term level, uint32_t *value) {
    if (!level || level >= k->count || k->nodes[level].kind != CC_LCONST || k->nodes[level].payload > CC_LEVEL_MAX)
        return false;
    *value = k->nodes[level].payload;
    return true;
}

bool ck_level_equal(cc_kernel *k, cc_term a, cc_term b) {
    uint32_t x, y;
    if (a && a == b && a < k->count && k->nodes[a].kind == CC_LCONST)
        return true;
    if (small_constant(k, a, &x) && small_constant(k, b, &y))
        return x == y;
    cc_level_nf left, right;
    if (!ck_level_normal(k, a, &left))
        return false;
    bool equal = ck_level_normal(k, b, &right) && nf_equal(&left, &right);
    ck_level_nf_free(&left);
    ck_level_nf_free(&right);
    return equal && !k->error[0];
}

bool ck_level_leq(cc_kernel *k, cc_term a, cc_term b) {
    uint32_t x, y;
    if (small_constant(k, a, &x) && small_constant(k, b, &y))
        return x <= y;
    cc_level_nf left, right;
    if (!ck_level_normal(k, a, &left))
        return false;
    bool below = ck_level_normal(k, b, &right) && nf_leq(&left, &right);
    ck_level_nf_free(&left);
    ck_level_nf_free(&right);
    return below && !k->error[0];
}

/* Finite: below ω, so a natural number for every assignment. */
bool ck_level_finite(cc_kernel *k, cc_term level) {
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return false;
    bool finite = !nf.tier;
    ck_level_nf_free(&nf);
    return finite;
}

cc_term ck_level_canonical(cc_kernel *k, cc_term level) {
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return 0;
    cc_term canonical = ck_level_build(k, &nf);
    ck_level_nf_free(&nf);
    return canonical;
}

cc_term ck_level_max(cc_kernel *k, cc_term a, cc_term b) {
    uint32_t x, y;
    if (small_constant(k, a, &x) && small_constant(k, b, &y))
        return x >= y ? a : b;
    cc_level_nf left, right;
    if (!ck_level_normal(k, a, &left))
        return 0;
    cc_term result = 0;
    if (ck_level_normal(k, b, &right)) {
        if (join(k, &left, &right))
            result = ck_level_build(k, &left);
        ck_level_nf_free(&right);
    }
    ck_level_nf_free(&left);
    return result;
}

cc_term ck_level_succ(cc_kernel *k, cc_term level) {
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return 0;
    cc_term result = add(k, &nf, 1) ? ck_level_build(k, &nf) : 0;
    ck_level_nf_free(&nf);
    return result;
}

/* lim_x(ℓ) (§2.7): ω when x occurs in nf(ℓ), and nf(ℓ) otherwise. It is the
 * level of Π (x < ω). B when B's level is ℓ. */
cc_term ck_level_limit(cc_kernel *k, uint32_t symbol, cc_term level) {
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return 0;
    bool occurs = false;
    for (uint32_t i = 0; i < nf.count; ++i)
        occurs |= nf.terms[i].key == symbol;
    cc_term result = occurs ? ck_level_constant(k, 1, 0) : ck_level_build(k, &nf);
    ck_level_nf_free(&nf);
    return result;
}

/* nf(ℓ + 1), in place. */
bool ck_level_nf_succ(cc_kernel *k, cc_level_nf *nf) {
    return add(k, nf, 1);
}

void ck_level_nf_sort(cc_level_nf *nf) {
    for (uint32_t i = 1; i < nf->count; ++i)
        for (uint32_t j = i; j && nf->terms[j - 1].key > nf->terms[j].key; --j) {
            cc_level_term swap = nf->terms[j];
            nf->terms[j] = nf->terms[j - 1];
            nf->terms[j - 1] = swap;
        }
}

bool ck_level_nf_equal(const cc_level_nf *a, const cc_level_nf *b) {
    return nf_equal(a, b);
}

/* Every level of a term in normal form: each universe's level and each
 * instantiation's. Shared subterms are visited once. */
cc_term ck_canonical_levels(cc_kernel *k, cc_term term) {
    if (!term || k->error[0])
        return 0;
    uint64_t cached;
    if (ck_memo_get(k, 4, term, 0, 0, &cached))
        return (cc_term)cached;
    if (!ck_tick(k, false))
        return 0;
    cc_node n = k->nodes[term];
    cc_term result = term;
    if (n.kind == CC_U) {
        result = ck_universe(k, ck_level_canonical(k, n.child[0]));
    } else if (n.kind != CC_LCONST && n.kind != CC_LSUCC && n.kind != CC_LMAX && n.kind != CC_LBOUND) {
        if (++k->recursion > 1024) {
            --k->recursion;
            return ck_fail(k, "Level normalization depth exceeded."), 0;
        }
        cc_term child[4] = {n.child[0], n.child[1], n.child[2], n.child[3]};
        for (unsigned i = 0; i < ck_arity(n.kind) && result; ++i)
            if (child[i])
                result = child[i] = n.kind == CC_LAPP && i == 1 ? ck_level_canonical(k, child[i])
                                                                : ck_canonical_levels(k, child[i]);
        --k->recursion;
        if (result && memcmp(child, n.child, sizeof child))
            result = ck_make(k, n.kind, n.payload, child[0], child[1], child[2], child[3]);
        else if (result)
            result = term;
    }
    if (result)
        ck_memo_put(k, 4, term, 0, 0, result);
    return result;
}

/* Level substitution (§2.8): capture-avoiding, since level and term
 * variables share one name supply, then every level taken to normal form, so
 * that an instance is the term a direct derivation would give. */
cc_term ck_level_instantiate(cc_kernel *k, cc_term body, uint32_t symbol, cc_term level) {
    return ck_canonical_levels(k, ck_substitute(k, body, symbol, level));
}

cc_term ck_universe(cc_kernel *k, cc_term level) {
    return level ? ck_make(k, CC_U, 0, level, 0, 0, 0) : 0;
}

/* The term checker is not extended to levels: its universes are those at a
 * closed finite level, as before G0, and any other level is an error. */
bool ck_universe_number(cc_kernel *k, cc_term universe, uint32_t *level) {
    if (!universe || universe >= k->count || k->nodes[universe].kind != CC_U)
        return ck_fail(k, "Expected a universe.");
    cc_term child = k->nodes[universe].child[0];
    if (small_constant(k, child, level))
        return true;
    cc_level_nf nf;
    if (!ck_level_normal(k, child, &nf))
        return false;
    bool closed = !nf.tier && !nf.count;
    *level = nf.constant;
    ck_level_nf_free(&nf);
    return closed || ck_fail(k, "The term checker takes universes at closed finite levels only.");
}

cc_term ck_universe_at(cc_kernel *k, uint32_t level) {
    return ck_universe(k, ck_level_constant(k, 0, level));
}

uint32_t cc_kernel_abi_version(void) {
    return CC_KERNEL_ABI_VERSION;
}
