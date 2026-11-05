/* The locally nameless primitives on raw syntax (section 3.3 of
 * docs/roadmaps/kernel/locally-nameless-kernel.md, tests of section 7.1):
 * the node's loose and opened counters and their bounds, and the laws of
 * instantiate, abstract, open and close, their pruning, worklists, steps and
 * failures. Allocation injection applies to the substitution worklist and
 * the syntax memo. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static unsigned allocations, fail_on;
static bool fail_memo;
void *cc_test_substitution_malloc(size_t size) {
    if (fail_on && ++allocations == fail_on) { fail_on = 0; return NULL; }
    return malloc(size);
}
void *cc_test_substitution_realloc(void *pointer, size_t size) {
    if (fail_on && ++allocations == fail_on) { fail_on = 0; return NULL; }
    return realloc(pointer, size);
}
void *cc_test_traversal_malloc(size_t size) { return malloc(size); }
void *cc_test_traversal_realloc(void *pointer, size_t size) { return realloc(pointer, size); }
void *cc_test_traversal_calloc(size_t count, size_t size) {
    if (fail_memo) { fail_memo = false; return NULL; }
    return calloc(count, size);
}

static cc_kernel *k;
static cc_term unit, entries[66];

static cc_term node4(cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c, cc_term d) {
    cc_term term = ck_make(k, kind, payload, a, b, c, d);
    assert(term && !k->error[0]);
    return term;
}
static cc_term node(cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c) {
    return node4(kind, payload, a, b, c, 0);
}
static cc_term bound(uint32_t index) { return node(CC_BOUND, index, 0, 0, 0); }
static cc_term opened(uint32_t level) { return node(CC_OPENED, level, 0, 0, 0); }
static cc_term context(unsigned entry) { return node(CC_CONTEXT, (uint32_t)entries[entry], 0, 0, 0); }
static cc_term lam(cc_term domain, cc_term body) { return node(CC_LAM, 0, domain, body, 0); }
static cc_term sum(cc_term a, cc_term b) { return node(CC_SUM, 0, a, b, 0); }
static cc_term app(cc_term f, cc_term x) { return node(CC_APP, 0, f, x, 0); }
/* A closed leaf told apart by its payload, which no primitive touches: a
 * definition's reference, never looked up here. */
static cc_term atom(uint32_t payload) { return node(CC_DEFREF, payload, 0, 0, 0); }

/* Equal syntax, compared by structure: with sharing off, equal terms are
 * distinct handles. */
static bool same(cc_term a, cc_term b) {
    if (a == b) return true;
    if (!a || !b) return false;
    cc_node x = k->nodes[a], y = k->nodes[b];
    if (x.kind != y.kind || x.payload != y.payload) return false;
    for (unsigned i = 0; i < 4; ++i)
        if (!same(x.child[i], y.child[i])) return false;
    return true;
}

/* The term and level binders, listed here rather than read from the
 * kernel's ck_term_binder, so that the references below share nothing with
 * the code they check. Each binds index 0 in its child 1. */
static bool binds(unsigned kind) {
    return kind == CC_PI || kind == CC_LAM || kind == CC_SIGMA || kind == CC_LPI || kind == CC_LLAM;
}

/* The counters' definitions by recursion (section 3.2), over 64 bits so
 * that no wrap can agree with a wrapped field. */
static uint64_t loose_of(cc_term t) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == CC_BOUND) return (uint64_t)n.payload + 1;
    uint64_t result = 0;
    for (unsigned i = 0; i < ck_arity(n.kind); ++i) {
        uint64_t reach = loose_of(n.child[i]);
        if (i == 1 && binds(n.kind) && reach) --reach;
        if (reach > result) result = reach;
    }
    return result;
}
static uint64_t opened_of(cc_term t) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == CC_OPENED) return (uint64_t)n.payload + 1;
    uint64_t result = 0;
    for (unsigned i = 0; i < ck_arity(n.kind); ++i)
        if (opened_of(n.child[i]) > result) result = opened_of(n.child[i]);
    return result;
}

/* CC_OPENED(level) replaced by a locally closed value, by recursion: the
 * substitution of the opened variable, against which instantiation is
 * checked. The values drawn mention no dimension, so no binder renames. */
static cc_term replace_opened(cc_term t, uint32_t level, cc_term value) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == CC_OPENED && n.payload == level) return value;
    cc_term child[4] = {0};
    bool changed = false;
    for (unsigned i = 0; i < 4; ++i) {
        child[i] = replace_opened(n.child[i], level, value);
        changed |= child[i] != n.child[i];
    }
    return changed ? node4(n.kind, n.payload, child[0], child[1], child[2], child[3]) : t;
}

/* Instantiation and abstraction by recursion, apart from the kernel's
 * worklist and its pruning, so that a subtree the kernel skips by mistake
 * cannot pass: CC_BOUND(depth + i) replaced by values[i], and the reference
 * (kind, payload) replaced by CC_BOUND(depth), where depth counts the term
 * and level binders crossed. No index is shifted. The values drawn mention
 * no dimension, so no binder renames. */
static cc_term instantiated(cc_term t, uint32_t depth, const cc_term *values, uint32_t count) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == CC_BOUND)
        return n.payload >= depth && n.payload - depth < count ? values[n.payload - depth] : t;
    cc_term child[4] = {0};
    bool changed = false;
    for (unsigned i = 0; i < 4; ++i) {
        child[i] = instantiated(n.child[i], depth + (i == 1 && binds(n.kind)), values, count);
        changed |= child[i] != n.child[i];
    }
    return changed ? node4(n.kind, n.payload, child[0], child[1], child[2], child[3]) : t;
}
static cc_term abstracted(cc_term t, uint32_t depth, unsigned kind, uint32_t payload) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == kind && n.payload == payload) return node(CC_BOUND, depth, 0, 0, 0);
    cc_term child[4] = {0};
    bool changed = false;
    for (unsigned i = 0; i < 4; ++i) {
        child[i] = abstracted(n.child[i], depth + (i == 1 && binds(n.kind)), kind, payload);
        changed |= child[i] != n.child[i];
    }
    return changed ? node4(n.kind, n.payload, child[0], child[1], child[2], child[3]) : t;
}

static uint64_t seed = 0x2545F4914F6CDD1DULL;
static uint32_t roll(uint32_t bound) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    return (uint32_t)(seed % bound);
}
/* An index or level near 0, or with `ends`, as often near UINT32_MAX - 1,
 * the largest a leaf may carry. */
static uint32_t drawn(bool ends) {
    return ends && roll(2) ? UINT32_MAX - 1 - roll(3) : roll(4);
}
/* Every syntax kind but the retired ones and the variables, as ck_arity
 * lists them; tubes appear only in a composition's tube list. */
static const cc_term_kind syntax_kinds[] = {
    CC_DEFREF, CC_UNIT, CC_POINT, CC_VOID, CC_LBOUND, CC_LCONST,
    CC_U, CC_FST, CC_SND, CC_LSUCC, CC_CON,
    CC_PI, CC_LAM, CC_APP, CC_SIGMA, CC_PLAM, CC_PAPP, CC_ABORT, CC_SUM, CC_INL, CC_INR,
    CC_GLUE, CC_UNGLUE, CC_LMAX, CC_LPI, CC_LLAM, CC_LAPP, CC_SORT, CC_ELIM, CC_LIST,
    CC_PAIR, CC_PATH, CC_COMP, CC_UNITREC, CC_GLUE_SYSTEM, CC_GLUE_TERM, CC_HCOMP, CC_TRANS,
    CC_SUMREC,
};
/* The children ck_make lets be absent. */
static bool optional_child(cc_term_kind kind, unsigned i) {
    return (kind == CC_PAPP && i == 1) || ((kind == CC_COMP || kind == CC_HCOMP) && i == 1) ||
           (kind == CC_GLUE && i == 1) || (kind == CC_GLUE_SYSTEM && i == 2) ||
           (kind == CC_GLUE_TERM && i == 2) || kind == CC_SORT || (kind == CC_LIST && i == 1) ||
           (kind == CC_ELIM && i == 1);
}
static bool dimension_binder(unsigned kind) {
    return kind == CC_PATH || kind == CC_PLAM || kind == CC_COMP || kind == CC_HCOMP || kind == CC_TRANS;
}
static cc_term random_term(unsigned depth, bool ends);
/* A composition's tube list: none, or faces with bodies. */
static cc_term random_tubes(unsigned depth, bool ends) {
    if (!depth || !roll(3)) return 0;
    return node(CC_TUBE, ck_endpoint_face(k, roll(3), roll(2)), random_term(depth - 1, ends),
                random_tubes(depth - 1, ends), 0);
}
/* Random syntax over every kind of syntax_kinds, each child present or,
 * where ck_make allows, absent; compositions with tube lists; formulas over
 * dimensions 0 to 2, binders over 0 and 1; and the leaves the counters read. */
static cc_term random_term(unsigned depth, bool ends) {
    switch (depth ? roll(8) : roll(5)) {
    case 0: return bound(drawn(ends));
    case 1: return opened(drawn(ends));
    case 2: return context(roll(3));
    case 3: if (!depth) return atom(1 + roll(3)); break;
    case 4: if (!depth) return unit; break;
    default: break;
    }
    /* Half the nodes are dimension binders or path applications, so that
     * values with dimensions meet binders they could be captured by. */
    static const cc_term_kind dimensional[] = {CC_PATH, CC_PLAM, CC_COMP, CC_HCOMP, CC_TRANS, CC_PAPP};
    cc_term_kind kind;
    do kind = depth && roll(2) ? dimensional[roll(6)] : syntax_kinds[roll(sizeof syntax_kinds / sizeof *syntax_kinds)];
    while (!depth && ck_arity(kind));
    uint32_t payload = kind == CC_PAPP ? ck_interval_variable(k, roll(3))
        : kind == CC_GLUE_SYSTEM ? ck_endpoint_face(k, roll(3), roll(2))
        : dimension_binder(kind) ? roll(2)
        : binds(kind) || kind == CC_U ? 0 : roll(3);
    cc_term child[4] = {0};
    for (unsigned i = 0; i < ck_arity(kind); ++i)
        child[i] = i == 1 && (kind == CC_COMP || kind == CC_HCOMP) ? random_tubes(depth - 1, ends)
                 : optional_child(kind, i) && !roll(3) ? 0 : random_term(depth - 1, ends);
    return node4(kind, payload, child[0], child[1], child[2], child[3]);
}
/* A random locally closed term that mentions no dimension. */
static cc_term random_value(void) {
    for (;;) {
        cc_term v = random_term(3, false);
        if (!k->nodes[v].loose && !ck_free_dims(k, v)) return v;
    }
}

enum { TERMS = 3000 };

static void metadata(void) {
    unsigned closed = 0, ends = 0;
    for (unsigned i = 0; i < TERMS; ++i) {
        cc_term t = random_term(4, true);
        assert(k->nodes[t].loose == loose_of(t) && k->nodes[t].opened == opened_of(t));
        closed += !k->nodes[t].loose;
        ends += k->nodes[t].loose > UINT32_MAX / 2 || k->nodes[t].opened > UINT32_MAX / 2;
    }
    assert(closed > TERMS / 10 && ends > TERMS / 10);
    printf("loose and opened: %u random terms agree with their definitions (%u locally closed, %u near the bound)\n",
           (unsigned)TERMS, closed, ends);
}

/* The bounds of section 3.2: a leaf's counter never wraps to 0. */
static void bounds(void) {
    cc_term largest = bound(UINT32_MAX - 1);
    assert(k->nodes[largest].loose == UINT32_MAX);
    assert(k->nodes[lam(unit, largest)].loose == UINT32_MAX - 1);
    assert(k->nodes[lam(largest, unit)].loose == UINT32_MAX);
    assert(k->nodes[opened(UINT32_MAX - 1)].opened == UINT32_MAX);
    /* Refused at UINT32_MAX, as a resource bound (section 3.2). */
    const char *bound_exceeded = "A variable's index exceeds the kernel's bound.";
    assert(!ck_make(k, CC_BOUND, UINT32_MAX, 0, 0, 0, 0) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, bound_exceeded));
    cc_kernel_clear_error(k);
    assert(!ck_make(k, CC_OPENED, UINT32_MAX, 0, 0, 0, 0) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, bound_exceeded));
    cc_kernel_clear_error(k);
    /* CC_BOUND and CC_CONTEXT are part of ABI 4, under the same bounds;
     * CC_OPENED, the kernel's own, is not. */
    cc_term public_largest = cc_kernel_term(k, CC_BOUND, UINT32_MAX - 1, 0, 0, 0, 0);
    assert(public_largest && k->nodes[public_largest].loose == UINT32_MAX);
    /* Not closed to the queries either, alone or under a binder, which
     * lowers its counter by one. */
    const cc_term open_ends[] = {public_largest, lam(unit, public_largest)};
    for (unsigned j = 0; j < 2; ++j) {
        assert(!cc_kernel_normalize(k, open_ends[j]));
        assert(!strcmp(cc_kernel_error(k), "Normalization reached a term with a loose bound variable."));
        cc_kernel_clear_error(k);
    }
    assert(!cc_kernel_term(k, CC_BOUND, UINT32_MAX, 0, 0, 0, 0) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(cc_kernel_error(k), bound_exceeded));
    cc_kernel_clear_error(k);
    assert(same(cc_kernel_term(k, CC_CONTEXT, (uint32_t)entries[0], 0, 0, 0, 0), context(0)) && !k->error[0]);
    const uint32_t payloads[] = {0, UINT32_MAX - 1, UINT32_MAX};
    for (unsigned j = 0; j < 3; ++j) {
        assert(!cc_kernel_term(k, CC_OPENED, payloads[j], 0, 0, 0, 0));
        assert(!strcmp(cc_kernel_error(k), "Unknown term constructor."));
        cc_kernel_clear_error(k);
    }
    /* A context reference names a live term or level entry. */
    cc_entry_id dimension = cc_instr_dimension(k, 0);
    assert(dimension);
    const uint32_t dead[] = {0, (uint32_t)dimension, (uint32_t)cc_kernel_entry_count(k)};
    for (unsigned i = 0; i < 3; ++i) {
        assert(!ck_make(k, CC_CONTEXT, dead[i], 0, 0, 0, 0));
        assert(!strcmp(k->error, "A context reference names no live term or level entry."));
        cc_kernel_clear_error(k);
    }
    /* An opener's counter fails rather than hand out UINT32_MAX. */
    cc_opener opener = {0};
    uint32_t level;
    ck_opener_above(k, &opener, sum(opened(3), lam(opened(5), unit)));
    assert(ck_opener_take(k, &opener, &level) && level == 6);
    assert(ck_opener_take(k, &opener, &level) && level == 7);
    ck_opener_above(k, &opener, opened(2));
    assert(ck_opener_take(k, &opener, &level) && level == 8);
    ck_opener_above(k, &opener, opened(UINT32_MAX - 2));
    assert(ck_opener_take(k, &opener, &level) && level == UINT32_MAX - 1);
    assert(!ck_opener_take(k, &opener, &level) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "An operation opened more binders than the kernel's bound."));
    cc_kernel_clear_error(k);
    opener = (cc_opener){0};
    ck_opener_above(k, &opener, opened(UINT32_MAX - 1));
    assert(!ck_opener_take(k, &opener, &level) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    cc_kernel_clear_error(k);
    /* Instantiating no index is the identity. */
    cc_term loose = bound(0);
    assert(ck_instantiate_all(k, loose, NULL, 0) == loose && !k->error[0]);
}

/* The laws of section 7.1 on random terms. */
static void laws(void) {
    unsigned changed = 0;
    for (unsigned i = 0; i < TERMS; ++i) {
        cc_term t = random_term(4, false), v = random_value();
        cc_opener opener = {0};
        uint32_t m;
        ck_opener_above(k, &opener, t);
        ck_opener_above(k, &opener, v);
        assert(ck_opener_take(k, &opener, &m));
        /* Open then close is the identity. */
        cc_term body = ck_open(k, t, m);
        assert(body && k->nodes[body].opened <= m + 1);
        assert(same(ck_close(k, body, m), t) && !k->error[0]);
        /* Instantiating is opening, then substituting the opened variable. */
        cc_term instance = ck_instantiate(k, t, v);
        assert(instance && same(instance, replace_opened(body, m, v)));
        changed += instance != t;
        /* Each operation against its reference by recursion. */
        cc_term at = opened(m), three[] = {v, random_value(), random_value()};
        uint32_t level = roll(4);
        cc_entry_id e = entries[roll(3)];
        assert(same(instance, instantiated(t, 0, &v, 1)) && same(body, instantiated(t, 0, &at, 1)));
        assert(same(ck_instantiate_all(k, t, three, 3), instantiated(t, 0, three, 3)));
        assert(same(ck_close(k, t, level), abstracted(t, 0, CC_OPENED, level)));
        assert(same(ck_abstract(k, t, e), abstracted(t, 0, CC_CONTEXT, (uint32_t)e)) && !k->error[0]);
        /* Close then open is the identity on locally closed terms, and so
         * are abstracting an entry and instantiating by its reference. */
        if (!k->nodes[t].loose) {
            uint32_t level = roll(4);
            assert(same(ck_open(k, ck_close(k, t, level), level), t));
            cc_entry_id e = entries[roll(3)];
            cc_term abstracted = ck_abstract(k, t, e);
            assert(abstracted && ck_abstract(k, abstracted, e) == abstracted);
            assert(same(ck_instantiate(k, abstracted, node(CC_CONTEXT, (uint32_t)e, 0, 0, 0)), t));
        }
        /* A telescope instantiated at once is its binders instantiated one
         * by one, outermost first: index 0 is the innermost. */
        cc_term inner = lam(random_term(2, false), t), w = random_value();
        cc_term once = ck_instantiate(k, inner, v);
        cc_term values[] = {w, v};
        assert(same(ck_instantiate(k, k->nodes[once].child[1], w), ck_instantiate_all(k, t, values, 2)));
        assert(!k->error[0]);
    }
    assert(changed > TERMS / 10);
    printf("open, close, abstract and instantiate: laws hold on %u random terms (%u changed)\n", (unsigned)TERMS, changed);
}

/* A comparison up to dimension binder names that shares no code with the
 * kernel's: `r`, the kernel's instantiation, against `t` with its indices
 * depth to depth + count - 1 standing for values. Every node, payload,
 * annotation and formula is compared. The scope holds a pair per dimension
 * binder crossed, the left's dimension and the right's; a dimension names
 * the same thing on both sides when both are bound by one pair or both are
 * free and equal. A value is compared behind a barrier: its own binders
 * pair as usual, but no binder of `t` above it binds any of its
 * dimensions, so a dimension the kernel let a binder capture shows. */
enum { SCOPES = 1024 };
static struct { unsigned left[SCOPES], right[SCOPES], count, barrier; } scope;

/* The binder pair binding a dimension on one side, or -1 if it is free. */
static int dimension_pair(bool right, unsigned name) {
    for (unsigned p = scope.count; p-- > (right ? scope.barrier : 0);)
        if ((right ? scope.right[p] : scope.left[p]) == name) return (int)p;
    return -1;
}
/* Whether a dimension binder binds its dimension in child i, as the
 * calculus says: a path type and transport in their family, a path
 * abstraction in both children, a composition in its family and its tubes'
 * bodies, hcomp only in its tubes' bodies. A tube's face is outside. */
static bool binds_dimension(unsigned kind, unsigned i) {
    return kind == CC_PATH || kind == CC_TRANS ? i == 0 : kind == CC_PLAM || kind == CC_COMP ? i <= 1
         : kind == CC_HCOMP && i == 1;
}
/* A clause's generators, each named by the pair binding it (above every
 * dimension) or, when free, by its dimension, sorted. */
static unsigned clause_key(bool right, cc_clause c, unsigned *key) {
    unsigned n = 0;
    for (unsigned d = 0; d < CC_DIMENSIONS; ++d) {
        if (!(((c.positive | c.negative) >> d) & 1)) continue;
        int pair = dimension_pair(right, d);
        unsigned name = pair >= 0 ? CC_DIMENSIONS + (unsigned)pair : d;
        if ((c.positive >> d) & 1) key[n++] = 2 * name + 1;
        if ((c.negative >> d) & 1) key[n++] = 2 * name;
    }
    for (unsigned i = 1; i < n; ++i)
        for (unsigned j = i; j > 0 && key[j - 1] > key[j]; --j) {
            unsigned swap = key[j]; key[j] = key[j - 1]; key[j - 1] = swap;
        }
    return n;
}
static bool formulas_agree(cc_formula_id left, cc_formula_id right) {
    const cc_formula *x = cc_kernel_get_formula(k, left), *y = cc_kernel_get_formula(k, right);
    if (!x || !y || x->sort != y->sort || x->length != y->length) return false;
    for (size_t i = 0; i < x->length; ++i) {
        unsigned a[2 * CC_DIMENSIONS], b[2 * CC_DIMENSIONS], n = clause_key(false, x->clauses[i], a);
        bool found = false;
        for (size_t j = 0; j < y->length && !found; ++j)
            found = clause_key(true, y->clauses[j], b) == n && !memcmp(a, b, n * sizeof *a);
        if (!found) return false;
    }
    return true;
}
static bool agrees(cc_term r, cc_term t, uint32_t depth, const cc_term *values, uint32_t count);
/* A composition's tubes, its binder's pair innermost: each face compared
 * outside it, each body under it. */
static bool tubes_agree(cc_term r, cc_term t, uint32_t depth, const cc_term *values, uint32_t count) {
    for (; r || t; r = k->nodes[r].child[1], t = k->nodes[t].child[1]) {
        if (!r || !t || k->nodes[r].kind != CC_TUBE || k->nodes[t].kind != CC_TUBE) return false;
        --scope.count;
        bool face = formulas_agree(k->nodes[r].payload, k->nodes[t].payload);
        ++scope.count;
        if (!face || !agrees(k->nodes[r].child[0], k->nodes[t].child[0], depth, values, count)) return false;
    }
    return true;
}
static bool agrees(cc_term r, cc_term t, uint32_t depth, const cc_term *values, uint32_t count) {
    if (!t) return !r;
    cc_node tn = k->nodes[t];
    if (tn.kind == CC_BOUND && tn.payload >= depth && tn.payload - depth < count) {
        unsigned barrier = scope.barrier;
        scope.barrier = scope.count;
        bool equal = agrees(r, values[tn.payload - depth], 0, NULL, 0);
        scope.barrier = barrier;
        return equal;
    }
    if (!r) return false;
    cc_node rn = k->nodes[r];
    if (rn.kind != tn.kind) return false;
    if (tn.kind == CC_PAPP || tn.kind == CC_GLUE_SYSTEM || tn.kind == CC_TUBE
            ? !formulas_agree(rn.payload, tn.payload)
            : !dimension_binder(tn.kind) && rn.payload != tn.payload)
        return false;
    for (unsigned i = 0; i < 4; ++i) {
        bool bound = dimension_binder(tn.kind) && binds_dimension(tn.kind, i);
        if (bound) {
            assert(scope.count < SCOPES);
            scope.left[scope.count] = rn.payload;
            scope.right[scope.count++] = tn.payload;
        }
        bool equal = i == 1 && (tn.kind == CC_COMP || tn.kind == CC_HCOMP)
            ? tubes_agree(rn.child[1], tn.child[1], depth, values, count)
            : agrees(rn.child[i], tn.child[i], depth + (i == 1 && binds(tn.kind)), values, count);
        if (bound) --scope.count;
        if (!equal) return false;
    }
    return true;
}

/* Instantiation by values that mention dimensions, on random terms of every
 * kind, so that the capture scan and the renaming read every child
 * position, against the comparison above: the result must be the term with
 * the values put in, no dimension of theirs captured and every binder's
 * own dimension still bound by it, renamed or not. */
static void capture_laws(void) {
    unsigned renamed = 0;
    for (unsigned i = 0; i < TERMS; ++i) {
        /* Half the terms carry indices near UINT32_MAX - 1, for the scan's
         * index arithmetic. */
        cc_term t = random_term(4, roll(2)), values[3];
        /* Half the values are path applications at dimension 0 or 1, free in
         * them, which the binders over 0 and 1 could capture. */
        for (unsigned j = 0; j < 3; ++j) {
            do values[j] = random_term(3, false); while (k->nodes[values[j]].loose);
            if (roll(2)) values[j] = node(CC_PAPP, ck_interval_variable(k, roll(2)), values[j], 0, 0);
        }
        for (uint32_t count = 1; count <= 3; count += 2) {
            cc_term direct = ck_instantiate_all(k, t, values, count);
            assert(direct && !k->error[0]);
            assert(scope.count == 0);
            bool agreed = agrees(direct, t, 0, values, count);
            assert(agreed);
            renamed += !same(direct, instantiated(t, 0, values, count));
        }
    }
    assert(renamed > TERMS / 20);
    printf("capture: instantiation by values with dimensions on %u random terms of every kind (%u renamed)\n",
           (unsigned)TERMS, renamed);
}

/* The comparison itself: it tells a capture, a binder renamed without its
 * occurrences, and a differing annotation from the expected term. */
static void comparison_cases(void) {
    cc_term p = atom(50), at0 = node(CC_PAPP, ck_interval_variable(k, 0), p, 0, 0);
    cc_term at1 = node(CC_PAPP, ck_interval_variable(k, 1), p, 0, 0);
    cc_term t = node(CC_PLAM, 0, at0, bound(0), 0);
    bool renamed = agrees(node(CC_PLAM, 1, at1, at0, 0), t, 0, &at0, 1);
    bool captured = agrees(node(CC_PLAM, 0, at0, at0, 0), t, 0, &at0, 1);
    bool unrenamed = agrees(node(CC_PLAM, 1, at0, at0, 0), t, 0, &at0, 1);
    assert(renamed && !captured && !unrenamed);
    cc_term annotated = node(CC_PLAM, 0, unit, node(CC_PAPP, ck_interval_variable(k, 2), p, bound(0), 0), 0);
    cc_term good = node(CC_PLAM, 1, unit, node(CC_PAPP, ck_interval_variable(k, 2), p, at0, 0), 0);
    cc_term bad = node(CC_PLAM, 0, unit, node(CC_PAPP, ck_interval_variable(k, 2), p, at0, 0), 0);
    bool kept = agrees(good, annotated, 0, &at0, 1), lost = agrees(bad, annotated, 0, &at0, 1);
    assert(kept && !lost);
    assert(scope.count == 0 && scope.barrier == 0);
}

/* Each term and level binder binds index 0 in its body only, and a path
 * abstraction binds none: the expected results written out. */
static void binder_cases(void) {
    const cc_term_kind kinds[] = {CC_PI, CC_LAM, CC_SIGMA, CC_LPI, CC_LLAM};
    cc_term v = atom(7);
    for (unsigned i = 0; i < 5; ++i) {
        cc_term t = node(kinds[i], 0, bound(0), sum(bound(0), bound(1)), 0);
        assert(same(ck_instantiate(k, t, v), node(kinds[i], 0, v, sum(bound(0), v), 0)));
        cc_term open = node(kinds[i], 0, opened(2), sum(bound(0), opened(2)), 0);
        assert(same(ck_open(k, t, 2), open) && same(ck_close(k, open, 2), t));
        cc_term reference = node(kinds[i], 0, context(0), sum(bound(0), context(0)), 0);
        assert(same(ck_abstract(k, reference, entries[0]), t) && !k->error[0]);
    }
    cc_term path = node(CC_PLAM, 0, bound(0), sum(bound(0), bound(1)), 0);
    assert(same(ck_instantiate(k, path, v), node(CC_PLAM, 0, v, sum(v, bound(1)), 0)) && !k->error[0]);
}

/* A dimension binder is renamed only for a value put where it binds: a
 * value whose index does not occur there forces no renaming, though it
 * mentions every dimension (review round 2's case), nor does an index the
 * instantiation leaves, or a value put only into a child the binder does
 * not bind. A value whose index occurs under a term binder there does. */
static void capture_scan(void) {
    cc_term every = unit;
    for (unsigned d = 0; d < CC_DIMENSIONS; ++d)
        every = sum(every, node(CC_PAPP, ck_interval_variable(k, d), atom(30), 0, 0));
    assert(ck_free_dims(k, every) == UINT64_MAX && !k->nodes[every].loose);
    cc_term point = node(CC_POINT, 0, 0, 0, 0), values[] = {point, every};
    cc_term t = node(CC_PLAM, 0, unit, bound(0), 0);
    assert(same(ck_instantiate_all(k, t, values, 2), node(CC_PLAM, 0, unit, point, 0)) && !k->error[0]);
    cc_term outer = node(CC_PLAM, 0, unit, bound(1), 0);
    assert(same(ck_instantiate(k, outer, every), outer) && !k->error[0]);
    cc_term at = node(CC_PAPP, ck_interval_variable(k, 0), atom(31), 0, 0);
    assert(same(ck_instantiate(k, node(CC_HCOMP, 0, bound(0), 0, unit), at), node(CC_HCOMP, 0, at, 0, unit)));
    assert(!k->error[0]);
    cc_term renamed = ck_instantiate(k, node(CC_COMP, 0, bound(0), 0, unit), at);
    assert(renamed && k->nodes[renamed].payload != 0 && !k->error[0]);
    renamed = ck_instantiate(k, node(CC_PLAM, 0, unit, lam(unit, bound(1)), 0), at);
    assert(renamed && k->nodes[renamed].payload != 0 && ck_free_dims(k, renamed) == 1 && !k->error[0]);
    /* Dimensions across the 64-bit masks, the highest included (review round
     * 5): a binder over each, given a value mentioning it, is renamed. */
    const unsigned high[] = {31, 32, 63};
    for (unsigned i = 0; i < 3; ++i) {
        cc_term value = node(CC_PAPP, ck_interval_variable(k, high[i]), atom(32), 0, 0);
        cc_term over = node(CC_PLAM, high[i], unit, bound(0), 0), out = ck_instantiate(k, over, value);
        bool agreed = out && agrees(out, over, 0, &value, 1);
        assert(agreed && ck_free_dims(k, out) == UINT64_C(1) << high[i]);
        assert(!k->error[0]);
    }
    /* Beneath 256 term binders: the scan seeks index 256, and its frames
     * move to the heap, whose allocation failing fails the instantiation
     * with no result. */
    cc_term deep = bound(256);
    for (unsigned i = 0; i < 256; ++i) deep = lam(unit, deep);
    deep = node(CC_PLAM, 0, unit, deep, 0);
    allocations = 0;
    fail_on = 1;
    assert(!ck_instantiate(k, deep, at) && !fail_on && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Variable scan allocation failed."));
    cc_kernel_clear_error(k);
    cc_term out = ck_instantiate(k, deep, at);
    bool agreed = out && agrees(out, deep, 0, &at, 1);
    assert(agreed && ck_free_dims(k, out) == 1 && !k->error[0]);
}

/* Every width in the primitives at its boundaries (review round 6):
 * binder depths across 255/256 up to 511, levels, entries and indices
 * across 255/256 and 65535/65536, filter bits 0, 31, 32 and 63, memo keys
 * whose operands agree in their low bits, kinds that agree with an ABI kind
 * in their low byte, the entries a context reference may name, and the new
 * leaves compared. Each result is checked against the references. */
static cc_term binders_over(unsigned count, cc_term body) {
    for (unsigned i = 0; i < count; ++i) body = lam(unit, body);
    return body;
}
static cc_term reference(uint32_t entry) { return node(CC_CONTEXT, entry, 0, 0, 0); }
enum { WIDE = 65537 };
static cc_term wide[WIDE];
static void boundaries(void) {
    /* Abstraction and close beneath 255, 256 and 511 binders. */
    const unsigned depths[] = {255, 256, 511};
    for (unsigned i = 0; i < 3; ++i) {
        cc_term t = binders_over(depths[i], context(0)), o = binders_over(depths[i], opened(300));
        assert(same(ck_abstract(k, t, entries[0]), abstracted(t, 0, CC_CONTEXT, (uint32_t)entries[0])));
        assert(same(ck_close(k, o, 300), abstracted(o, 0, CC_OPENED, 300)) && !k->error[0]);
    }
    /* Levels: open puts the level in, and close takes out exactly it, not a
     * level agreeing with it in the low 8 or 16 bits; both closes of one
     * term are memoized apart. */
    const uint32_t levels[] = {255, 256, 65535, 65536, 65792, UINT32_MAX - 1};
    for (unsigned i = 0; i < 6; ++i) {
        uint32_t m = levels[i], low = m & 0xff, mid = m & 0xffff;
        cc_term at = opened(m), body = sum(bound(0), unit);
        assert(same(ck_open(k, body, m), instantiated(body, 0, &at, 1)));
        cc_term t = sum(sum(opened(m), opened(low)), lam(unit, opened(mid)));
        assert(same(ck_close(k, t, m), abstracted(t, 0, CC_OPENED, m)));
        assert(same(ck_close(k, t, low), abstracted(t, 0, CC_OPENED, low)));
        assert(same(ck_close(k, t, mid), abstracted(t, 0, CC_OPENED, mid)) && !k->error[0]);
    }
    /* Entries across 255/256 and 65535/65536, at filter bits 0, 31, 32 and
     * 63, each beside the entries 256 and 65,536 above it; the abstractions
     * of one term are memoized apart. */
    cc_judgement_id type = cc_instr_unit(k);
    while (k->entry_count <= 65536 + 320) {
        cc_entry_id entry = cc_instr_extend(k, type);
        assert(entry);
    }
    const uint32_t ids[] = {256, 287, 288, 319};
    for (unsigned i = 0; i < 4; ++i) {
        uint32_t e = ids[i], near = e + 256, far = e + 65536;
        assert(!k->entries[e].dimension && !k->entries[near].dimension && !k->entries[far].dimension);
        cc_term t = sum(lam(unit, reference(e)), sum(lam(unit, reference(near)), reference(far)));
        assert(same(ck_abstract(k, t, e), abstracted(t, 0, CC_CONTEXT, e)));
        assert(same(ck_abstract(k, t, near), abstracted(t, 0, CC_CONTEXT, near)));
        assert(same(ck_abstract(k, t, far), abstracted(t, 0, CC_CONTEXT, far)) && !k->error[0]);
        assert(k->nodes[reference(far)].payload == far);
    }
    /* Vectors of 257 and 65,537 values, indices across 255/256 and
     * 65535/65536, at the root and under a binder. */
    for (uint32_t i = 0; i < WIDE; ++i) wide[i] = atom(2000000 + i);
    cc_term t = sum(sum(bound(0), bound(255)), sum(sum(bound(256), bound(65535)), bound(65536)));
    cc_term under = lam(unit, sum(sum(bound(256), bound(257)), sum(bound(65536), bound(65537))));
    const uint32_t counts[] = {257, WIDE};
    for (unsigned i = 0; i < 2; ++i) {
        assert(same(ck_instantiate_all(k, t, wide, counts[i]), instantiated(t, 0, wide, counts[i])));
        assert(same(ck_instantiate_all(k, under, wide, counts[i]), instantiated(under, 0, wide, counts[i])));
        assert(!k->error[0]);
    }
    /* The scan's answers for one subterm at indices 65536 and 0, asked one
     * right after the other, are memoized apart: the instantiation by 65,537
     * values ends seeking index 65536 in `low_absent`, absent, and the next one first
     * seeks index 0 there, present, whose value must rename the binder. */
    cc_term low_absent = sum(bound(0), bound(65537)), over_y = node(CC_PLAM, 0, unit, low_absent, 0);
    cc_term captured = node(CC_PAPP, ck_interval_variable(k, 0), atom(800010), 0, 0);
    cc_term kept = wide[65536];
    wide[65536] = captured;
    cc_term out_y = ck_instantiate_all(k, over_y, wide, WIDE);
    bool agreed_y = out_y && agrees(out_y, over_y, 0, wide, WIDE);
    wide[65536] = kept;
    assert(agreed_y && !k->error[0]);
    out_y = ck_instantiate(k, over_y, captured);
    agreed_y = out_y && agrees(out_y, over_y, 0, &captured, 1);
    assert(agreed_y && ck_free_dims(k, out_y) == 1 && !k->error[0]);
    /* A value at index 65536 or 256 that a binder would capture: the scan
     * seeks it there. */
    const uint32_t far[] = {256, 65536};
    for (unsigned i = 0; i < 2; ++i) {
        cc_term saved = wide[far[i]], p = atom(800000);
        wide[far[i]] = node(CC_PAPP, ck_interval_variable(k, 0), p, 0, 0);
        cc_term over = node(CC_PLAM, 0, unit, sum(bound(far[i]), bound(1)), 0);
        cc_term out = ck_instantiate_all(k, over, wide, WIDE);
        bool agreed = out && agrees(out, over, 0, wide, WIDE);
        assert(agreed && ck_free_dims(k, out) == 1 && !k->error[0]);
        wide[far[i]] = saved;
    }
    /* Memo keys agreeing in their low bits. A subterm met at depth 1 and at
     * depth 257 within one instantiation, holding an index each replaces: */
    cc_term x = sum(bound(1), bound(257)), twice = sum(lam(unit, x), binders_over(257, x));
    cc_term one = atom(800001);
    assert(same(ck_instantiate(k, twice, one), instantiated(twice, 0, &one, 1)));
    /* two values whose handles differ by 65,536: */
    cc_term y = sum(bound(0), atom(800002)), first = atom(800003);
    for (uint32_t filler = 0; k->count < (size_t)first + 65536; ++filler) atom(3000000 + filler);
    cc_term second = atom(800004);
    assert(second == first + 65536);
    assert(same(ck_instantiate(k, y, first), sum(first, atom(800002))));
    assert(same(ck_instantiate(k, y, second), sum(second, atom(800002))));
    /* and two serials 65,536 apart. */
    cc_term pair[] = {first, second}, swapped[] = {second, first}, z = sum(bound(0), bound(1));
    k->instantiation_serial = 0;
    assert(same(ck_instantiate_all(k, z, pair, 2), sum(first, second)));
    k->instantiation_serial = 65536;
    assert(same(ck_instantiate_all(k, z, swapped, 2), sum(second, first)) && !k->error[0]);
    /* A kind beyond the ABI's is refused whole, though its low byte or
     * bits are an ABI kind. */
    const unsigned beyond[] = {CC_UNIT + 256, CC_VAR + 256, CC_LAM + 65536, CC_OPENED + 256};
    for (unsigned i = 0; i < 4; ++i) {
        assert(!cc_kernel_term(k, (cc_term_kind)beyond[i], 0, 0, 0, 0, 0));
        assert(!strcmp(cc_kernel_error(k), "Unknown term constructor."));
        cc_kernel_clear_error(k);
    }
    /* A context reference names a level entry, never a face entry. */
    cc_entry_id level = cc_instr_level(k);
    assert(level && ck_make(k, CC_CONTEXT, level, 0, 0, 0, 0) && !k->error[0]);
    cc_entry_id face = ck_instr_face_entry(k, (cc_clause){.positive = 1});
    assert(face && !ck_make(k, CC_CONTEXT, face, 0, 0, 0, 0));
    assert(!strcmp(k->error, "A context reference names no live term or level entry."));
    cc_kernel_clear_error(k);
    /* Comparison reads the new leaves' payloads: equal leaves are equal
     * whatever their handles, unequal ones are not. */
    assert(ck_alpha_equal(k, bound(3), bound(3)) && !ck_alpha_equal(k, bound(3), bound(4)));
    assert(!ck_alpha_equal(k, bound(3), bound(259)) && !ck_alpha_equal(k, bound(3), bound(65539)));
    assert(ck_alpha_equal(k, opened(3), opened(3)) && !ck_alpha_equal(k, opened(3), opened(259)));
    assert(!ck_alpha_equal(k, opened(3), opened(65539)));
    assert(ck_alpha_equal(k, context(1), context(1)) && !ck_alpha_equal(k, context(1), context(2)));
    assert(!ck_alpha_equal(k, reference(256), reference(512)) && !ck_alpha_equal(k, reference(256), reference(65792)));
    assert(!k->error[0]);
}

/* Instantiation renames a dimension binder its value would be captured by,
 * as term substitution does (SUBSTITUTE_RENAME_DIMENSION). */
static void dimension_capture(void) {
    cc_term value = node(CC_PAPP, ck_interval_variable(k, 0), atom(10), 0, 0);
    cc_term at = node(CC_PAPP, ck_interval_variable(k, 0), atom(11), 0, 0);
    cc_term t = node(CC_PLAM, 0, unit, sum(bound(0), at), 0);
    cc_term out = ck_instantiate(k, t, value);
    assert(out && k->nodes[out].kind == CC_PLAM && k->nodes[out].payload != 0);
    cc_node body = k->nodes[k->nodes[out].child[1]];
    assert(body.child[0] == value || same(body.child[0], value));
    assert(ck_free_dims(k, body.child[1]) == UINT64_C(1) << k->nodes[out].payload);
    assert(ck_free_dims(k, out) == 1 && !k->error[0]);
}

/* A filter bit shared by two entries makes abstraction search, never err. */
static void filter_collision(void) {
    assert(entries[65] % 64 == entries[1] % 64);
    cc_term t = lam(unit, app(context(65), bound(0)));
    assert(ck_abstract(k, t, entries[1]) == t && !k->error[0]);
    assert(same(ck_abstract(k, t, entries[65]), lam(unit, app(bound(1), bound(0)))));
    /* So does the query whether a term mentions an entry. */
    bool other = ck_mentions(k, t, entries[1]), own = ck_mentions(k, t, entries[65]);
    assert(!other && own && !k->error[0]);
}

/* The primitives of operations on a loose term (cc_kernel_whnf, Step and
 * Replace under binders): abstraction and closing at a base, a term's loose
 * indices opened and closed back, and the occurrence queries. Their
 * references, by recursion: whether CC_CONTEXT(entry) occurs; whether
 * CC_BOUND(index) does, the index raised under each term or level binder,
 * over 64 bits so that no wrap can agree with a wrapped index; and the
 * levels first .. first + count - 1 closed, level first + j becoming the
 * index count - 1 - j beneath the binders crossed. */
static bool mentions_of(cc_term t, uint32_t entry) {
    if (!t) return false;
    cc_node n = k->nodes[t];
    if (n.kind == CC_CONTEXT) return n.payload == entry;
    for (unsigned i = 0; i < 4; ++i)
        if (mentions_of(n.child[i], entry)) return true;
    return false;
}
static bool occurs_of(cc_term t, uint64_t index) {
    if (!t) return false;
    cc_node n = k->nodes[t];
    if (n.kind == CC_BOUND) return n.payload == index;
    for (unsigned i = 0; i < 4; ++i)
        if (occurs_of(n.child[i], index + (i == 1 && binds(n.kind)))) return true;
    return false;
}
static cc_term closed_loose(cc_term t, uint32_t depth, uint32_t first, uint32_t count) {
    if (!t) return 0;
    cc_node n = k->nodes[t];
    if (n.kind == CC_OPENED && n.payload >= first && n.payload - first < count)
        return bound(depth + count - 1 - (n.payload - first));
    cc_term child[4] = {0};
    bool changed = false;
    for (unsigned i = 0; i < 4; ++i) {
        child[i] = closed_loose(n.child[i], depth + (i == 1 && binds(n.kind)), first, count);
        changed |= child[i] != n.child[i];
    }
    return changed ? node4(n.kind, n.payload, child[0], child[1], child[2], child[3]) : t;
}

static void loose_laws(void) {
    unsigned mentioned = 0, occurring = 0, loose_terms = 0;
    for (unsigned i = 0; i < TERMS; ++i) {
        cc_term t = random_term(4, false);
        /* A base of a few binders, or across 255/256 and 65535/65536. */
        uint32_t base = roll(2) ? 1 + roll(3) : roll(2) ? 256 : 65536, level = roll(4);
        cc_entry_id e = entries[roll(4) ? roll(3) : 65];
        assert(same(ck_abstract_at(k, t, e, base), abstracted(t, base, CC_CONTEXT, (uint32_t)e)));
        assert(same(ck_close_at(k, t, level, base), abstracted(t, base, CC_OPENED, level)));
        bool found = ck_mentions(k, t, e);
        assert(found == mentions_of(t, (uint32_t)e));
        mentioned += found;
        uint32_t index = roll(5);
        found = ck_index_occurs(k, t, index);
        assert(found == occurs_of(t, index));
        occurring += found;
        /* On a term with indices near the bound, at an index near it too. */
        cc_term far = random_term(4, true);
        index = drawn(true);
        found = ck_index_occurs(k, far, index);
        assert(found == occurs_of(far, index));
        /* Opening the loose indices above every level the term holds, the
         * innermost at the highest, and closing them back is the identity. */
        uint32_t loose = k->nodes[t].loose, first = k->nodes[t].opened + roll(3);
        cc_term levels[8] = {0};
        assert(loose <= 8);
        for (uint32_t j = 0; j < loose; ++j) levels[j] = opened(first + loose - 1 - j);
        cc_term open = ck_open_loose(k, t, first);
        assert(open && !k->nodes[open].loose && same(open, instantiated(t, 0, levels, loose)));
        assert(same(ck_close_loose(k, open, first, loose), t));
        loose_terms += loose != 0;
        /* Closing levels the term holds, whatever opened them. */
        uint32_t count = 1 + roll(3);
        assert(same(ck_close_loose(k, t, level, count), closed_loose(t, 0, level, count)) && !k->error[0]);
    }
    assert(mentioned > TERMS / 10 && occurring > TERMS / 10 && loose_terms > TERMS / 10);
    printf("abstract and close at a base, open and close loose indices, mentions and occurrences: "
           "%u random terms agree with their references\n", (unsigned)TERMS);
}

/* The same primitives written out, and their bounds. */
static void loose_cases(void) {
    /* λ y. e y abstracted two binders out: e under λ y is index 3. */
    cc_term t = lam(unit, app(context(0), bound(0)));
    assert(same(ck_abstract_at(k, t, entries[0], 2), lam(unit, app(bound(3), bound(0)))));
    assert(same(ck_close_at(k, lam(unit, app(opened(5), bound(0))), 5, 2), lam(unit, app(bound(3), bound(0)))));
    /* (index 0, λ y. index 2): index 0 opens at the higher level, 8, and
     * index 1 at 7. */
    cc_term loose = sum(bound(0), lam(unit, bound(2)));
    assert(k->nodes[loose].loose == 2);
    cc_term open = ck_open_loose(k, loose, 7);
    assert(same(open, sum(opened(8), lam(unit, opened(7)))));
    assert(same(ck_close_loose(k, open, 7, 2), loose) && !k->error[0]);
    assert(ck_open_loose(k, unit, 7) == unit && ck_close_loose(k, unit, 7, 2) == unit);
    /* The levels reach UINT32_MAX - 1, the largest; beyond it, the opening
     * fails as a resource error, with no result. */
    open = ck_open_loose(k, loose, UINT32_MAX - 2);
    assert(same(open, sum(opened(UINT32_MAX - 1), lam(unit, opened(UINT32_MAX - 2)))) && !k->error[0]);
    assert(!ck_open_loose(k, loose, UINT32_MAX - 1) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "An operation opened more binders than the kernel's bound."));
    cc_kernel_clear_error(k);
    /* Mentions and occurrences, under binders: index 1 beneath λ is index 0
     * outside it. */
    bool mentioned = ck_mentions(k, t, entries[0]), absent = ck_mentions(k, t, entries[2]);
    assert(mentioned && !absent);
    bool outer = ck_index_occurs(k, lam(unit, bound(1)), 0), own = ck_index_occurs(k, lam(unit, bound(0)), 0);
    assert(outer && !own && !k->error[0]);
}

/* Instantiation needs locally closed values: a value's loose index would
 * be captured by the binders it is put under. A value with one, alone or
 * among closed values, is refused, with no result, though the term has no
 * index to replace; an opened level is locally closed. */
static void loose_values(void) {
    const char *refusal = "Instantiation needs locally closed values.";
    cc_term t = lam(unit, sum(bound(1), bound(0))), values[] = {unit, bound(0)};
    const cc_term refused[] = {bound(0), lam(unit, bound(1)), sum(unit, bound(UINT32_MAX - 1))};
    for (unsigned i = 0; i < 3; ++i) {
        assert(!ck_instantiate(k, t, refused[i]) && !strcmp(k->error, refusal));
        cc_kernel_clear_error(k);
        assert(!ck_instantiate(k, unit, refused[i]) && !strcmp(k->error, refusal));
        cc_kernel_clear_error(k);
    }
    assert(!ck_instantiate_all(k, t, values, 2) && !strcmp(k->error, refusal));
    cc_kernel_clear_error(k);
    assert(same(ck_instantiate(k, t, opened(0)), lam(unit, sum(opened(0), bound(0)))) && !k->error[0]);
}

/* A closed graph of 2^40 paths costs no step; one with a loose index costs a
 * step per node, through the memo. */
static void dag(void) {
    cc_term closed = unit, open = bound(0), reference = context(0), level = opened(0);
    for (unsigned i = 0; i < 40; ++i) {
        closed = i % 2 ? sum(closed, closed) : lam(closed, closed);
        open = sum(open, open);
        reference = sum(reference, reference);
        level = sum(level, level);
    }
    uint64_t budget = k->budget;
    k->budget = 0;
    assert(ck_instantiate(k, closed, unit) == closed && ck_abstract(k, closed, entries[0]) == closed);
    assert(ck_open(k, closed, 0) == closed && ck_close(k, closed, 0) == closed && !k->error[0]);
    /* A step for each of the 41 nodes, and one for each second child, which
     * the memo answers. */
    k->budget = 1000;
    cc_term out = ck_instantiate(k, open, unit);
    assert(out && !k->nodes[out].loose && k->nodes[out].depth == 41 && !k->error[0]);
    assert(1000 - k->budget == 41 + 40);
    k->budget = 1000;
    out = ck_abstract(k, reference, entries[0]);
    assert(out && k->nodes[out].loose == 1 && !k->error[0]);
    k->budget = 1000;
    out = ck_close(k, level, 0);
    assert(out && k->nodes[out].loose == 1 && !k->nodes[out].opened && !k->error[0]);
    k->budget = budget;
}

/* A chain at the depth limit: the variable at its bottom is bound by its
 * root, under 255 binders. */
static cc_term chain(cc_term leaf) {
    cc_term t = leaf;
    for (unsigned i = 0; i < 255; ++i) t = lam(unit, sum(t, unit));
    assert(k->nodes[t].depth == 510 + k->nodes[leaf].depth);
    return t;
}
static void deep_and_wide(void) {
    cc_term t = chain(bound(255)), closed = chain(unit);
    assert(k->nodes[t].loose == 1);
    assert(same(ck_instantiate(k, t, unit), closed));
    cc_opener opener = {0};
    uint32_t m;
    ck_opener_above(k, &opener, t);
    assert(ck_opener_take(k, &opener, &m) && m == 0);
    assert(same(ck_open(k, t, m), chain(opened(m))));
    assert(same(ck_close(k, chain(opened(m)), m), t));
    assert(same(ck_abstract(k, chain(context(0)), entries[0]), t));
    /* A value one node deeper than the leaf fits; two deeper exceed 512. */
    assert(same(ck_instantiate(k, t, sum(unit, unit)), chain(sum(unit, unit))));
    assert(!ck_instantiate(k, t, sum(sum(unit, unit), unit)) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Native prototype syntax depth exceeds 512."));
    cc_kernel_clear_error(k);
    /* Several values whose result reaches the depth limit: the memo key adds
     * no depth to theirs. */
    cc_term deepest = chain(unit), pair[] = {unit, deepest};
    assert(k->nodes[deepest].depth == 511 && !k->nodes[deepest].loose);
    assert(same(ck_instantiate_all(k, sum(bound(0), bound(1)), pair, 2), sum(unit, deepest)) && !k->error[0]);
    /* 4,096 distinct leaves, each using the index. */
    cc_term level[4096];
    for (unsigned i = 0; i < 4096; ++i) level[i] = app(bound(0), atom(1000 + i));
    for (unsigned width = 4096; width > 1; width /= 2)
        for (unsigned i = 0; i < width / 2; ++i) level[i] = sum(level[2 * i], level[2 * i + 1]);
    cc_term out = ck_instantiate(k, lam(unit, level[0]), unit);
    assert(out && !k->nodes[out].loose && !k->error[0]);
    cc_term leftmost = k->nodes[out].child[1];
    while (k->nodes[leftmost].kind == CC_SUM) leftmost = k->nodes[leftmost].child[0];
    assert(k->nodes[leftmost].kind == CC_APP && k->nodes[k->nodes[leftmost].child[0]].kind == CC_BOUND);
    out = ck_instantiate(k, level[0], unit);
    cc_term rightmost = out;
    while (k->nodes[rightmost].kind == CC_SUM) rightmost = k->nodes[rightmost].child[1];
    assert(same(rightmost, app(unit, atom(1000 + 4095))));
}

/* An allocation fault or an exhausted budget gives no result and memoizes
 * nothing: the operation repeated gives the whole answer. */
static void failures(void) {
    cc_term t = chain(bound(255));
    /* The first allocation of frames on the heap, its growth, and the budget.
     * Each run has operands of its own, so no memo entry answers it. */
    for (unsigned operation = 0; operation < 3; ++operation)
        for (unsigned fault = 1; fault <= 3; ++fault) {
            cc_term value = atom(500 + fault);
            cc_term input = operation == 0 ? t : chain(operation == 1 ? context(fault) : opened(fault));
            uint64_t budget = k->budget;
            if (fault < 3) {
                allocations = 0;
                fail_on = fault;
            } else k->budget = 100;
            cc_term out = operation == 0 ? ck_instantiate(k, input, value)
                        : operation == 1 ? ck_abstract(k, input, entries[fault]) : ck_close(k, input, fault);
            assert(!out && !fail_on);
            assert(cc_kernel_error_kind(k) == (fault < 3 ? CC_ERROR_RESOURCE : CC_ERROR_BUDGET));
            if (fault < 3) assert(!strcmp(k->error, "Substitution stack allocation failed."));
            cc_kernel_clear_error(k);
            k->budget = budget;
            out = operation == 0 ? ck_instantiate(k, input, value)
                : operation == 1 ? ck_abstract(k, input, entries[fault]) : ck_close(k, input, fault);
            assert(same(out, operation ? t : chain(value)) && !k->error[0]);
        }
}

/* A simultaneous instantiation's memo key is its call's serial. When the
 * serial wraps, the memo is cleared, so an entry an earlier call left under
 * the same key answers nothing. */
static void serial_wrap(void) {
    cc_term t = sum(bound(0), bound(1)), a = atom(20), b = atom(21);
    cc_term first[] = {a, b}, second[] = {b, a};
    k->instantiation_serial = 0;
    assert(same(ck_instantiate_all(k, t, first, 2), sum(a, b)) && k->instantiation_serial == 1);
    k->instantiation_serial = UINT32_MAX;
    assert(same(ck_instantiate_all(k, t, second, 2), sum(b, a)) && k->instantiation_serial == 1);
    assert(!k->error[0]);
}

/* The memo's first allocation failing fails the operation that needed it. */
static void memo_failure(unsigned optimizations) {
    cc_kernel *fresh = cc_kernel_new();
    assert(fresh);
    cc_kernel_set_optimizations(fresh, optimizations);
    cc_term leaf = ck_make(fresh, CC_BOUND, 0, 0, 0, 0, 0), u = ck_make(fresh, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term t = ck_make(fresh, CC_SUM, 0, leaf, u, 0, 0);
    fail_memo = true;
    assert(!ck_instantiate(fresh, t, u) && !fail_memo && cc_kernel_error_kind(fresh) == CC_ERROR_RESOURCE);
    assert(!strcmp(fresh->error, "Syntax memo allocation failed."));
    cc_kernel_clear_error(fresh);
    cc_term out = ck_instantiate(fresh, t, u);
    assert(out && fresh->nodes[out].child[0] == u && !fresh->error[0]);
    cc_kernel_free(fresh);
}

int main(void) {
    for (unsigned sharing = 0; sharing < 2; ++sharing) {
        k = cc_kernel_new();
        assert(k);
        cc_kernel_set_optimizations(k, sharing ? CC_SHARE_SYNTAX : 0);
        cc_kernel_set_step_budget(k, UINT64_C(1) << 40);
        k->budget = UINT64_C(1) << 40;
        unit = node(CC_UNIT, 0, 0, 0, 0);
        /* Term entries, the last sharing the second's filter bit. */
        cc_judgement_id type = cc_instr_unit(k);
        for (unsigned i = 0; i < 66; ++i) {
            entries[i] = cc_instr_extend(k, type);
            assert(entries[i]);
        }
        metadata();
        bounds();
        laws();
        binder_cases();
        serial_wrap();
        capture_scan();
        comparison_cases();
        capture_laws();
        boundaries();
        dimension_capture();
        filter_collision();
        loose_laws();
        loose_cases();
        loose_values();
        dag();
        deep_and_wide();
        failures();
        cc_kernel_free(k);
        memo_failure(sharing ? CC_SHARE_SYNTAX : 0);
    }
    puts("Locally nameless primitives: ok");
    return 0;
}
