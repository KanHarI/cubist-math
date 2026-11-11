/* Raw syntax exercises scope/level traversal independently of type checking.
 * Allocation injection applies to comparison, levels and the shared memo. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static unsigned mallocs, reallocs, fail_malloc, fail_realloc, fail_calloc;
static bool fail_existing_realloc;
void *cc_test_traversal_malloc(size_t size) {
    ++mallocs;
    if (fail_malloc && !--fail_malloc) return NULL;
    return malloc(size);
}
void *cc_test_traversal_realloc(void *pointer, size_t size) {
    ++reallocs;
    if (fail_realloc && (!fail_existing_realloc || pointer) && !--fail_realloc) return NULL;
    return realloc(pointer, size);
}
void *cc_test_traversal_calloc(size_t count, size_t size) {
    if (fail_calloc && !--fail_calloc) return NULL;
    return calloc(count, size);
}
static cc_term node(cc_kernel *k, cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c) {
    cc_term term = ck_make(k, kind, payload, a, b, c, 0);
    assert(term && !k->error[0]);
    return term;
}
static void resource(cc_kernel *k, const char *message) {
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE && !strcmp(k->error, message));
    cc_kernel_clear_error(k);
    k->budget = 1000000;
}

/* Only dimension binders keep names, and so scopes, in the comparison: term
 * and level binders bind indices. So the chain is of path abstractions, 200
 * deep, the outermost over dimension `outer` and the others cycling through
 * the 31 above it. The outer dimension occurs beneath every inner binder,
 * so pruning cannot hide stale scope links after a frame-array move.
 * Families use the previous binder's dimension; the innermost use
 * distinguishes its binding from its parent. */
static unsigned dimension_at(unsigned outer, unsigned i) { return i ? outer + 1 + i % 31 : outer; }
static cc_term at(cc_kernel *k, unsigned dimension) {
    return node(k, CC_PAPP, ck_interval_variable(k, dimension), node(k, CC_POINT, 0, 0, 0, 0), 0, 0);
}
static cc_term scoped(cc_kernel *k, unsigned outer, bool wrong) {
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_term t = node(k, CC_SUM, 0, at(k, outer), at(k, dimension_at(outer, wrong ? 198 : 199)), 0);
    for (unsigned i = 200; i-- > 0;) {
        cc_term family = i ? node(k, CC_SUM, 0, unit, at(k, dimension_at(outer, i - 1)), 0) : unit;
        t = node(k, CC_PLAM, dimension_at(outer, i), family, t, 0);
    }
    return t;
}
static void comparisons(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term left = scoped(k, 0, false), right = scoped(k, 32, false), wrong = scoped(k, 32, true);
    fail_malloc = 1;
    assert(!ck_alpha_equal(k, left, right) && !fail_malloc);
    resource(k, "Alpha-comparison stack allocation failed.");
    fail_realloc = 1;
    assert(!ck_alpha_equal(k, left, right) && !fail_realloc);
    resource(k, "Alpha-comparison stack allocation failed.");
    k->budget = 20;
    assert(!ck_alpha_equal(k, left, right) && cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    k->budget = 1000000;
    assert(ck_alpha_equal(k, left, right) && !k->error[0]);
    assert(!ck_alpha_equal(k, left, wrong) && !k->error[0]);
    k->budget = 1;
    assert(ck_alpha_equal(k, left, right) && !k->error[0]);
    cc_kernel_free(k);
}

static cc_term composition(cc_kernel *k, unsigned direction, bool wrong_face) {
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_term body = node(k, CC_PAPP, ck_interval_variable(k, direction), node(k, CC_POINT, 0, 0, 0, 0), 0, 0);
    cc_term tubes = 0;
    for (unsigned i = 0; i < 450; ++i) {
        cc_formula_id face = ck_endpoint_face(k, wrong_face && i == 0 ? 3 : 2, 0);
        tubes = node(k, CC_TUBE, face, body, tubes, 0);
    }
    return node(k, CC_COMP, direction, unit, tubes, unit);
}
static void tube_scopes(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term left = composition(k, 0, false), right = composition(k, 1, false);
    cc_term wrong = composition(k, 1, true);
    assert(ck_alpha_equal(k, left, right));
    assert(!ck_alpha_equal(k, left, wrong) && !k->error[0]);
    /* The inner dimension renaming must never apply to the outer faces. */
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_term a = node(k, CC_TUBE, ck_endpoint_face(k, 0, 0), unit, 0, 0);
    cc_term b = node(k, CC_TUBE, ck_endpoint_face(k, 1, 0), unit, 0, 0);
    a = node(k, CC_COMP, 0, unit, a, unit);
    b = node(k, CC_COMP, 1, unit, b, unit);
    assert(!ck_alpha_equal(k, a, b) && !k->error[0]);
    cc_kernel_free(k);
}

/* A level variable: a new level entry's reference. */
static cc_term level_variable(cc_kernel *k) {
    cc_entry_id entry = cc_instr_level(k);
    assert(entry);
    return node(k, CC_CONTEXT, entry, 0, 0, 0);
}
static cc_term arithmetic(cc_kernel *k, cc_term first, cc_term second, bool deep_right) {
    cc_term t = first;
    for (unsigned i = 0; i < 200; ++i) {
        cc_term deeper = node(k, CC_LSUCC, 1, t, 0, 0), variable = second;
        t = node(k, CC_LMAX, 0, deep_right ? variable : deeper, deep_right ? deeper : variable, 0);
    }
    return t;
}
static void arithmetic_failures(unsigned optimizations, bool deep_right) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term first = level_variable(k), second = level_variable(k);
    cc_term term = arithmetic(k, first, second, deep_right);
    cc_level_nf nf;
    fail_malloc = 1;
    assert(!ck_level_normal(k, term, &nf) && !nf.terms && !fail_malloc);
    resource(k, "Level traversal stack allocation failed.");
    /* Right descent keeps a separately allocated left NF in each ancestor.
     * Skip initial realloc(NULL) buffers to fail the grown frame array. */
    fail_existing_realloc = deep_right;
    fail_realloc = 1;
    assert(!ck_level_normal(k, term, &nf) && !nf.terms && !fail_realloc);
    fail_existing_realloc = false;
    resource(k, "Level traversal stack allocation failed.");
    k->budget = 100;
    unsigned before = mallocs;
    assert(!ck_level_normal(k, term, &nf) && !nf.terms && cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    assert(mallocs > before);
    cc_kernel_clear_error(k);
    k->budget = 1000000;
    assert(ck_level_normal(k, term, &nf) && !k->error[0]);
    assert(nf.tier == 0 && nf.constant == 200 && nf.count == 2);
    assert(nf.terms[0].key == k->nodes[first].payload && nf.terms[0].offset == 200);
    assert(nf.terms[1].key == k->nodes[second].payload && nf.terms[1].offset == 199);
    ck_level_nf_free(&nf);
    /* The query-local memo can fail after both children own normal forms. */
    fail_calloc = 1;
    assert(!ck_level_normal(k, term, &nf) && !nf.terms && !fail_calloc);
    resource(k, "Level normal form allocation failed.");
    assert(ck_level_normal(k, term, &nf) && nf.count == 2);
    ck_level_nf_free(&nf);
    cc_kernel_free(k);
}

static void canonical_failures(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0), variable = level_variable(k);
    cc_term t = node(k, CC_U, 0, node(k, CC_LMAX, 0, variable, variable, 0), 0, 0);
    for (unsigned i = 0; i < 450; ++i) t = node(k, CC_SUM, 0, t, unit, 0);
    fail_malloc = 1;
    assert(!ck_canonical_levels(k, t) && !fail_malloc);
    resource(k, "Level traversal stack allocation failed.");
    fail_realloc = 1;
    assert(!ck_canonical_levels(k, t) && !fail_realloc);
    resource(k, "Level traversal stack allocation failed.");
    k->budget = 100;
    unsigned before = reallocs;
    assert(!ck_canonical_levels(k, t) && cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    assert(reallocs > before);
    cc_kernel_clear_error(k);
    k->budget = 1000000;
    cc_term out = ck_canonical_levels(k, t), whole = out;
    assert(out && !k->error[0]);
    for (unsigned i = 0; i < 450; ++i) {
        assert(k->nodes[out].kind == CC_SUM && k->nodes[out].child[1] == unit);
        out = k->nodes[out].child[0];
    }
    assert(k->nodes[out].kind == CC_U);
    cc_node level = k->nodes[k->nodes[out].child[0]];
    assert(level.kind == CC_CONTEXT && level.payload == k->nodes[variable].payload);
    k->budget = 0;
    assert(ck_canonical_levels(k, t) == whole && !k->error[0]);
    cc_kernel_free(k);
}

static void cumulative(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term lower = ck_universe_at(k, 0), upper = ck_universe_at(k, 1);
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    for (unsigned i = 0; i < 200; ++i) {
        lower = node(k, CC_PI, 0, unit, lower, 0);
        upper = node(k, CC_PI, 0, unit, upper, 0);
    }
    assert(ck_syntactic_cumulative(k, lower, upper));
    assert(!ck_syntactic_cumulative(k, upper, lower) && !k->error[0]);
    cc_kernel_free(k);
}

/* Even an immediate canonical result must return failure if publishing its
 * completed memo entry fails. A nonzero handle alongside an error is not
 * a successful query result. */
static void canonical_memo_failure(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    fail_calloc = 1;
    assert(!ck_canonical_levels(k, unit) && !fail_calloc);
    resource(k, "Syntax memo allocation failed.");
    assert(ck_canonical_levels(k, unit) == unit && !k->error[0]);
    cc_kernel_free(k);
}

int main(void) {
    for (unsigned sharing = 0; sharing < 2; ++sharing) {
        unsigned options = sharing ? CC_SHARE_SYNTAX : 0;
        comparisons(options);
        tube_scopes(options);
        arithmetic_failures(options, false);
        arithmetic_failures(options, true);
        canonical_failures(options);
        cumulative(options);
        canonical_memo_failure(options);
    }
    puts("Comparison and level traversal stacks: ok");
    return 0;
}
