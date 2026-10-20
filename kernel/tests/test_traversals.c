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

/* The outer name occurs beneath every inner binder, so pruning cannot hide
 * stale scope links after a frame-array move. Domains use the previous
 * binder; the innermost use distinguishes its binding from its parent. */
static cc_term scoped(cc_kernel *k, unsigned names, bool wrong) {
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_term t = node(k, CC_SUM, 0, ck_var(k, names), ck_var(k, names + (wrong ? 198 : 199)), 0);
    for (unsigned i = 200; i-- > 0;) {
        cc_term domain = i ? node(k, CC_SUM, 0, unit, ck_var(k, names + i - 1), 0) : unit;
        t = node(k, CC_LAM, names + i, domain, t, 0);
    }
    return t;
}
static void comparisons(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term left = scoped(k, 100, false), right = scoped(k, 1000, false), wrong = scoped(k, 2000, true);
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
    cc_term body = node(k, CC_PAPP, ck_interval_variable(k, direction), ck_var(k, 10), 0, 0);
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

static cc_term arithmetic(cc_kernel *k, bool deep_right) {
    cc_term t = ck_var(k, 7);
    for (unsigned i = 0; i < 200; ++i) {
        cc_term deeper = node(k, CC_LSUCC, 1, t, 0, 0), variable = ck_var(k, 8);
        t = node(k, CC_LMAX, 0, deep_right ? variable : deeper, deep_right ? deeper : variable, 0);
    }
    return t;
}
static void arithmetic_failures(unsigned optimizations, bool deep_right) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term term = arithmetic(k, deep_right);
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
    assert(nf.terms[0].key == 7 && nf.terms[0].offset == 200);
    assert(nf.terms[1].key == 8 && nf.terms[1].offset == 199);
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
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0), variable = ck_var(k, 7);
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
    assert(level.kind == CC_VAR && level.payload == 7);
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
        lower = node(k, CC_PI, 100 + i, unit, lower, 0);
        upper = node(k, CC_PI, 1000 + i, unit, upper, 0);
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
