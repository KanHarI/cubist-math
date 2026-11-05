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
static cc_term random_term(unsigned depth, bool ends);
/* A composition's tube list: none, or faces with bodies. */
static cc_term random_tubes(unsigned depth, bool ends) {
    if (!depth || !roll(3)) return 0;
    return node(CC_TUBE, ck_endpoint_face(k, roll(2), roll(2)), random_term(depth - 1, ends),
                random_tubes(depth - 1, ends), 0);
}
/* Random syntax over every term and level binder, every dimension binder
 * (path types and abstractions, compositions with their tube lists,
 * transport), path applications, a node of four children, and the leaves
 * the counters read. */
static cc_term random_term(unsigned depth, bool ends) {
    static const cc_term_kind binders[] = {CC_PI, CC_LAM, CC_SIGMA, CC_LPI, CC_LLAM};
    switch (depth ? roll(17) : roll(5)) {
    case 0: return bound(drawn(ends));
    case 1: return opened(drawn(ends));
    case 2: return context(roll(3));
    case 3: return node(CC_VAR, 1 + roll(3), 0, 0, 0);
    case 4: return unit;
    case 5: case 6: case 7:
        return node(binders[roll(5)], 0, random_term(depth - 1, ends), random_term(depth - 1, ends), 0);
    case 8: return app(random_term(depth - 1, ends), random_term(depth - 1, ends));
    case 9: return node(CC_PAIR, 0, random_term(depth - 1, ends), random_term(depth - 1, ends),
                        random_term(depth - 1, ends));
    case 10: return node(CC_PLAM, roll(2), random_term(depth - 1, ends), random_term(depth - 1, ends), 0);
    case 11: case 12:
        return node(roll(2) ? CC_PATH : CC_TRANS, roll(2), random_term(depth - 1, ends),
                    random_term(depth - 1, ends), random_term(depth - 1, ends));
    case 13: case 14:
        return node(roll(2) ? CC_COMP : CC_HCOMP, roll(2), random_term(depth - 1, ends),
                    random_tubes(depth - 1, ends), random_term(depth - 1, ends));
    case 15: return node4(CC_SUMREC, 0, random_term(depth - 1, ends), random_term(depth - 1, ends),
                          random_term(depth - 1, ends), random_term(depth - 1, ends));
    default: return node(CC_PAPP, ck_interval_variable(k, roll(2)), random_term(depth - 1, ends),
                         roll(2) ? random_term(depth - 1, ends) : 0, 0);
    }
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
    /* Refused as a symbol of UINT32_MAX is (section 3.2). */
    assert(!ck_make(k, CC_BOUND, UINT32_MAX, 0, 0, 0, 0) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Term symbol space exhausted."));
    cc_kernel_clear_error(k);
    assert(!ck_make(k, CC_OPENED, UINT32_MAX, 0, 0, 0, 0) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Term symbol space exhausted."));
    cc_kernel_clear_error(k);
    /* None of the kernel's kinds is part of ABI 3. */
    const uint32_t payloads[] = {0, UINT32_MAX - 1, UINT32_MAX};
    const cc_term_kind kinds[] = {CC_BOUND, CC_CONTEXT, CC_OPENED};
    for (unsigned i = 0; i < 3; ++i)
        for (unsigned j = 0; j < 3; ++j) {
            uint32_t payload = kinds[i] == CC_CONTEXT ? (uint32_t)entries[0] : payloads[j];
            assert(!cc_kernel_term(k, kinds[i], payload, 0, 0, 0, 0));
            assert(!strcmp(cc_kernel_error(k), "Unknown term constructor."));
            cc_kernel_clear_error(k);
        }
    /* A context reference names a live term or level entry. */
    cc_entry_id dimension = cc_instr_dimension(k, 0);
    assert(dimension);
    const uint32_t dead[] = {0, (uint32_t)dimension, (uint32_t)cc_kernel_entry_count(k)};
    const char *refusals[] = {"Unknown context entry.", "Expected a term entry.", "Unknown context entry."};
    for (unsigned i = 0; i < 3; ++i) {
        assert(!ck_make(k, CC_CONTEXT, dead[i], 0, 0, 0, 0));
        assert(!strcmp(k->error, refusals[i]));
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
    assert(!strcmp(k->error, "Fresh symbol space exhausted."));
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

/* Each term and level binder binds index 0 in its body only, and a path
 * abstraction binds none: the expected results written out. */
static void binder_cases(void) {
    const cc_term_kind kinds[] = {CC_PI, CC_LAM, CC_SIGMA, CC_LPI, CC_LLAM};
    cc_term v = node(CC_VAR, 7, 0, 0, 0);
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
        every = sum(every, node(CC_PAPP, ck_interval_variable(k, d), node(CC_VAR, 30, 0, 0, 0), 0, 0));
    assert(ck_free_dims(k, every) == UINT64_MAX && !k->nodes[every].loose);
    cc_term point = node(CC_POINT, 0, 0, 0, 0), values[] = {point, every};
    cc_term t = node(CC_PLAM, 0, unit, bound(0), 0);
    assert(same(ck_instantiate_all(k, t, values, 2), node(CC_PLAM, 0, unit, point, 0)) && !k->error[0]);
    cc_term outer = node(CC_PLAM, 0, unit, bound(1), 0);
    assert(same(ck_instantiate(k, outer, every), outer) && !k->error[0]);
    cc_term at = node(CC_PAPP, ck_interval_variable(k, 0), node(CC_VAR, 31, 0, 0, 0), 0, 0);
    assert(same(ck_instantiate(k, node(CC_HCOMP, 0, bound(0), 0, unit), at), node(CC_HCOMP, 0, at, 0, unit)));
    assert(!k->error[0]);
    cc_term renamed = ck_instantiate(k, node(CC_COMP, 0, bound(0), 0, unit), at);
    assert(renamed && k->nodes[renamed].payload != 0 && !k->error[0]);
    renamed = ck_instantiate(k, node(CC_PLAM, 0, unit, lam(unit, bound(1)), 0), at);
    assert(renamed && k->nodes[renamed].payload != 0 && ck_free_dims(k, renamed) == 1 && !k->error[0]);
}

/* Instantiation renames a dimension binder its value would be captured by,
 * as term substitution does (SUBSTITUTE_RENAME_DIMENSION). */
static void dimension_capture(void) {
    cc_term value = node(CC_PAPP, ck_interval_variable(k, 0), node(CC_VAR, 10, 0, 0, 0), 0, 0);
    cc_term at = node(CC_PAPP, ck_interval_variable(k, 0), node(CC_VAR, 11, 0, 0, 0), 0, 0);
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
    for (unsigned i = 0; i < 4096; ++i) level[i] = app(bound(0), node(CC_VAR, 1000 + i, 0, 0, 0));
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
    assert(same(rightmost, app(unit, node(CC_VAR, 1000 + 4095, 0, 0, 0))));
}

/* An allocation fault or an exhausted budget gives no result and memoizes
 * nothing: the operation repeated gives the whole answer. */
static void failures(void) {
    cc_term t = chain(bound(255));
    /* The first allocation of frames on the heap, its growth, and the budget.
     * Each run has operands of its own, so no memo entry answers it. */
    for (unsigned operation = 0; operation < 3; ++operation)
        for (unsigned fault = 1; fault <= 3; ++fault) {
            cc_term value = node(CC_VAR, 500 + fault, 0, 0, 0);
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
    cc_term t = sum(bound(0), bound(1)), a = node(CC_VAR, 20, 0, 0, 0), b = node(CC_VAR, 21, 0, 0, 0);
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
            entries[i] = cc_instr_extend(k, type, 100 + i);
            assert(entries[i]);
        }
        metadata();
        bounds();
        laws();
        binder_cases();
        serial_wrap();
        capture_scan();
        dimension_capture();
        filter_collision();
        dag();
        deep_and_wide();
        failures();
        cc_kernel_free(k);
        memo_failure(sharing ? CC_SHARE_SYNTAX : 0);
    }
    puts("Locally nameless primitives: ok");
    return 0;
}
