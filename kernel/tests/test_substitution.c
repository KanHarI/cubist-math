/* Dependency analysis is a syntax operation, so scope tests intentionally
 * use raw nodes. It must distinguish binder scopes without a typing context. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static bool fail_allocation;
static unsigned allocations, failures, fail_on;
static bool allocation_fails(void) {
    ++allocations;
    if (fail_allocation || (fail_on && allocations == fail_on)) {
        fail_allocation = false;
        fail_on = 0;
        ++failures;
        return true;
    }
    return false;
}
void *cc_test_substitution_malloc(size_t size) {
    if (allocation_fails()) return NULL;
    return malloc(size);
}
void *cc_test_substitution_realloc(void *pointer, size_t size) {
    if (allocation_fails()) return NULL;
    return realloc(pointer, size);
}

static cc_term node(cc_kernel *k, cc_term_kind kind, unsigned payload, cc_term a, cc_term b, cc_term c) {
    cc_term result = ck_make(k, kind, payload, a, b, c, 0);
    assert(result && !k->error[0]);
    return result;
}
static void expect(cc_kernel *k, cc_term term, uint64_t names) {
    uint64_t conservative = k->nodes[term].dims;
    assert(ck_free_dims(k, term) == names && !k->error[0]);
    assert(!(names & ~conservative));
}

static void scopes(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0), p = ck_var(k, 10);
    for (unsigned d = 0; d < CC_DIMENSIONS; ++d) {
        uint64_t bit = UINT64_C(1) << d;
        cc_term at = node(k, CC_PAPP, ck_interval_variable(k, d), p, 0, 0);
        expect(k, at, bit);
        expect(k, node(k, CC_PATH, d, at, unit, unit), 0);
        expect(k, node(k, CC_PATH, d, unit, at, unit), bit);
        expect(k, node(k, CC_PATH, d, unit, unit, at), bit);
        expect(k, node(k, CC_PLAM, d, at, at, 0), 0);
        expect(k, node(k, CC_PLAM, (d + 1) % CC_DIMENSIONS, unit, at, 0), bit);
        /* A term binder with the same numeric name does not bind dimensions. */
        expect(k, node(k, CC_LAM, d, unit, at, 0), bit);
        cc_formula_id face = ck_endpoint_face(k, d, 0);
        cc_term body = node(k, CC_TUBE, ck_endpoint_face(k, (d + 1) % CC_DIMENSIONS, 1), at, 0, 0);
        uint64_t other = UINT64_C(1) << ((d + 1) % CC_DIMENSIONS);
        expect(k, body, bit | other);
        expect(k, node(k, CC_COMP, d, at, body, unit), other);
        expect(k, node(k, CC_HCOMP, d, at, body, unit), bit | other);
        expect(k, node(k, CC_COMP, d, unit, 0, at), bit);
        cc_term sides = node(k, CC_TUBE, face, unit, body, 0);
        expect(k, node(k, CC_COMP, d, unit, sides, unit), bit | other);
        expect(k, node(k, CC_HCOMP, d, unit, sides, unit), bit | other);
        expect(k, node(k, CC_TRANS, d, at, unit, unit), 0);
        expect(k, node(k, CC_TRANS, d, unit, at, unit), bit);
        expect(k, node(k, CC_TRANS, d, unit, unit, at), bit);
        cc_term gluing = node(k, CC_GLUE_SYSTEM, face, unit, unit, 0);
        expect(k, node(k, CC_GLUE, 0, unit, gluing, 0), bit);
        cc_term annotation = node(k, CC_PATH, (d + 1) % CC_DIMENSIONS, at, unit, unit);
        expect(k, node(k, CC_PAPP, ck_interval_variable(k, (d + 1) % CC_DIMENSIONS), p, annotation, 0), bit | other);
    }
    cc_kernel_free(k);
}

static cc_term deep(cc_kernel *k, unsigned dim) {
    cc_term t = node(k, CC_PAPP, ck_interval_variable(k, dim), ck_var(k, 10), 0, 0);
    for (unsigned i = 0; i < 450; ++i) t = node(k, CC_SUM, 0, t, t, 0);
    return t;
}

static void interruption_and_pressure(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term left = node(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 11), 0, 0);
    cc_term t = node(k, CC_SUM, 0, left, deep(k, 63), 0);
    uint64_t expected = (UINT64_C(1) << 63) | 1;
    unsigned before = allocations;
    fail_allocation = true;
    assert(!ck_free_dims(k, t) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Dimension scan allocation failed."));
    assert(allocations == before + 1 && failures && !fail_allocation);
    assert(!k->nodes[t].dimensions_known);
    cc_kernel_clear_error(k);
    expect(k, left, 1);
    k->budget = 100;
    before = allocations;
    assert(!ck_free_dims(k, t) && cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    assert(allocations == before + 1 && !k->nodes[t].dimensions_known);
    cc_kernel_clear_error(k);
    k->budget = 1000;
    expect(k, t, expected);
    /* Evict the old fixed memo through unrelated real syntax queries. */
    cc_formula_id coordinate = ck_interval_variable(k, 1);
    k->budget = 1000000;
    for (unsigned i = 0; i < 10000; ++i) {
        cc_term unrelated = node(k, CC_PAPP, coordinate, ck_var(k, 100 + i), 0, 0);
        expect(k, unrelated, UINT64_C(1) << 1);
    }
    k->budget = 1;
    expect(k, t, expected);
    assert(k->budget == 1);
    cc_kernel_free(k);
}

static void rollback(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term p = ck_var(k, 10);
    cc_formula_id i = ck_interval_variable(k, 0), j = ck_interval_variable(k, 63);
    cc_kernel_checkpoint(k);
    cc_term old = node(k, CC_PAPP, i, p, 0, 0);
    expect(k, old, 1);
    cc_kernel_rollback(k);
    cc_term replacement = node(k, CC_PAPP, j, p, 0, 0);
    assert(old == replacement);
    expect(k, replacement, UINT64_C(1) << 63);
    cc_kernel_free(k);
}

static cc_term term_of(cc_kernel *k, cc_judgement_id judgement) {
    cc_judgement_info info;
    assert(judgement && cc_kernel_judgement(k, judgement, &info));
    return info.term;
}
static void compaction(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_checkpoint(k);
    for (unsigned i = 0; i < 100; ++i) assert(ck_var(k, 100 + i));
    cc_judgement_id unit = cc_instr_unit(k), point = cc_instr_point(k);
    cc_entry_id dimension = cc_instr_dimension(k, 0);
    cc_judgement_id path = cc_instr_path(k, dimension, unit, point, point);
    cc_entry_id p = cc_instr_extend(k, path, 300);
    cc_judgement_id along = cc_instr_path_apply(k, cc_instr_variable(k, p), dimension, 0);
    cc_term body = term_of(k, along);
    expect(k, body, 1);
    cc_judgement_id closed = cc_instr_lambda(k, p, cc_instr_path_lambda(k, dimension, along));
    cc_term reference = term_of(k, cc_instr_define(k, 301, closed));
    assert(cc_kernel_commit_checkpoint(k));
    cc_term relocated = cc_kernel_relocated(k, body);
    assert(relocated && relocated != body);
    k->budget = 0;
    expect(k, relocated, 1);
    k->budget = 10000;
    assert(cc_instr_lookup(k, cc_kernel_relocated(k, reference)));
    cc_kernel_free(k);
}

static void capture_and_shadowing(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    assert(!ck_term_free(k, 0, 7) && !k->error[0]);
    cc_term unit = node(k, CC_UNIT, 0, 0, 0, 0), x = ck_var(k, 78), y = ck_var(k, 77);
    const cc_term_kind binders[] = {CC_PI, CC_LAM, CC_SIGMA, CC_LPI, CC_LLAM};
    for (size_t i = 0; i < sizeof binders / sizeof *binders; ++i) {
        cc_term shadowed = node(k, binders[i], 77, y, y, 0);
        cc_term out = ck_substitute(k, shadowed, 77, x);
        assert(out && k->nodes[out].child[0] == x && k->nodes[out].child[1] == y);
        cc_term body = node(k, CC_SUM, 0, x, y, 0);
        out = ck_substitute(k, node(k, binders[i], 77, unit, body, 0), 78, y);
        assert(out && k->nodes[out].payload != 77);
        cc_node changed = k->nodes[k->nodes[out].child[1]];
        assert(changed.child[0] == y);
        assert(k->nodes[changed.child[1]].kind == CC_VAR &&
               k->nodes[changed.child[1]].payload == k->nodes[out].payload);
        assert(ck_term_free(k, out, 77) && !ck_term_free(k, out, 78));
    }
    cc_term nested = node(k, CC_SUM, 0, x, y, 0);
    for (unsigned i = 0; i < 50; ++i) nested = node(k, CC_LAM, 77, unit, nested, 0);
    cc_term renamed = ck_substitute(k, nested, 78, y);
    assert(renamed && !k->error[0]);
    unsigned innermost = 0;
    for (unsigned i = 0; i < 50; ++i) {
        assert(k->nodes[renamed].kind == CC_LAM && k->nodes[renamed].payload != 77);
        innermost = k->nodes[renamed].payload;
        renamed = k->nodes[renamed].child[1];
    }
    assert(k->nodes[renamed].child[0] == y);
    assert(k->nodes[k->nodes[renamed].child[1]].payload == innermost);
    cc_term p = ck_var(k, 90);
    cc_formula_id i = ck_interval_variable(k, 0), j = ck_interval_variable(k, 1);
    cc_term at_i = node(k, CC_PAPP, i, p, 0, 0), at_j = node(k, CC_PAPP, j, p, 0, 0);
    cc_term pair = node(k, CC_SUM, 0, x, at_i, 0);
    cc_term path_lambda = node(k, CC_PLAM, 0, unit, pair, 0);
    cc_term out = ck_substitute(k, path_lambda, 78, at_i);
    assert(out && k->nodes[out].payload != 0);
    cc_node changed = k->nodes[k->nodes[out].child[1]];
    assert(changed.child[0] == at_i);
    assert(ck_free_dims(k, changed.child[1]) == (UINT64_C(1) << k->nodes[out].payload));
    assert(ck_free_dims(k, out) == 1);

    /* Renaming the direction changes family/tube bodies, never endpoints,
     * faces or the starting lid. The later substitution still visits them. */
    cc_term family = node(k, CC_SUM, 0, at_i, at_j, 0);
    cc_formula_id face = ck_endpoint_face(k, 0, 0);
    cc_term tube = node(k, CC_TUBE, face, family, 0, 0);
    const cc_term_kind dimensions[] = {CC_PATH, CC_COMP, CC_HCOMP, CC_TRANS};
    for (size_t a = 0; a < sizeof dimensions / sizeof *dimensions; ++a) {
        cc_term middle = dimensions[a] == CC_COMP || dimensions[a] == CC_HCOMP ? tube : at_i;
        cc_term input = node(k, dimensions[a], 0, family, middle, at_i);
        out = ck_dimension_substitute(k, input, 1, cc_kernel_get_formula(k, i));
        assert(out && k->nodes[out].payload != 0 && k->nodes[out].payload != 1);
        unsigned fresh = k->nodes[out].payload;
        changed = k->nodes[k->nodes[out].child[0]];
        assert(ck_free_dims(k, changed.child[0]) ==
               (dimensions[a] == CC_HCOMP ? 1 : UINT64_C(1) << fresh));
        assert(ck_free_dims(k, changed.child[1]) == 1);
        assert(k->nodes[out].child[2] == at_i);
        if (dimensions[a] == CC_COMP || dimensions[a] == CC_HCOMP) {
            cc_node side = k->nodes[k->nodes[out].child[1]];
            assert(side.payload == face);
            cc_node body = k->nodes[side.child[0]];
            assert(ck_free_dims(k, body.child[0]) == (UINT64_C(1) << fresh));
            assert(ck_free_dims(k, body.child[1]) == 1);
        } else assert(k->nodes[out].child[1] == at_i);
        assert(ck_free_dims(k, out) == 1);
    }
    cc_kernel_free(k);
}

static void long_tubes(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term p = ck_var(k, 30), unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_term at = node(k, CC_PAPP, ck_interval_variable(k, 0), p, 0, 0);
    cc_formula_id face = ck_endpoint_face(k, 0, 0);
    cc_term tubes = 0;
    for (unsigned i = 0; i < 450; ++i) tubes = node(k, CC_TUBE, face, at, tubes, 0);
    cc_term input = node(k, CC_COMP, 0, unit, tubes, at);
    cc_formula one, empty;
    cc_init(&one, CC_INTERVAL);
    cc_init(&empty, CC_FACE);
    assert(cc_one(&one) == CC_OK);
    cc_term out = ck_dimension_substitute(k, input, 0, &one);
    assert(out && k->nodes[out].payload == 0 && !k->error[0]);
    cc_node lid = k->nodes[k->nodes[out].child[2]];
    assert(lid.kind == CC_PAPP && cc_equal(cc_kernel_get_formula(k, lid.payload), &one));
    cc_term side = k->nodes[out].child[1];
    for (unsigned i = 0; i < 450; ++i) {
        cc_node n = k->nodes[side];
        assert(n.kind == CC_TUBE && n.child[0] == at);
        assert(cc_equal(cc_kernel_get_formula(k, n.payload), &empty));
        side = n.child[1];
    }
    assert(!side);
    cc_clear(&one);
    cc_clear(&empty);
    cc_kernel_free(k);
}

static void variable_scan_failures(unsigned optimizations) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term t = ck_var(k, 7), unit = node(k, CC_UNIT, 0, 0, 0, 0);
    for (unsigned i = 0; i < 450; ++i) t = node(k, CC_SUM, 0, t, unit, 0);
    fail_allocation = true;
    assert(!ck_term_free(k, t, 7) && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(k->error, "Variable scan allocation failed.") && !fail_allocation);
    cc_kernel_clear_error(k);
    k->budget = 80;
    assert(!ck_term_free(k, t, 7) && cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    cc_kernel_clear_error(k);
    k->budget = 10000;
    assert(ck_term_free(k, t, 7));
    /* Colliding symbol bits require the exact scan, rather than the mask. */
    assert(!ck_term_free(k, t, 71) && !k->error[0]);
    cc_kernel_free(k);
}

static void substitution_failures(unsigned optimizations, bool dimensions) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_set_optimizations(k, optimizations);
    cc_term x = ck_var(k, 10), unit = node(k, CC_UNIT, 0, 0, 0, 0);
    cc_formula_id variable = ck_interval_variable(k, 0);
    cc_term t = dimensions ? node(k, CC_PAPP, variable, x, 0, 0) : x;
    for (unsigned i = 0; i < 450; ++i) t = node(k, CC_SUM, 0, t, unit, 0);
    if (dimensions) expect(k, t, 1);
    else assert(ck_term_free(k, t, 10));
    cc_formula one;
    cc_init(&one, CC_INTERVAL);
    assert(cc_one(&one) == CC_OK);
    for (unsigned allocation = 1; allocation <= 2; ++allocation) {
        /* Fail both local-to-heap growth and a later reallocation. */
        fail_on = allocations + allocation;
        cc_term out = dimensions ? ck_dimension_substitute(k, t, 0, &one) : ck_substitute(k, t, 10, unit);
        assert(!out && cc_kernel_error_kind(k) == CC_ERROR_RESOURCE && !fail_on);
        assert(!strcmp(k->error, "Substitution stack allocation failed."));
        cc_kernel_clear_error(k);
    }
    k->budget = 100;
    unsigned before = allocations;
    cc_term out = dimensions ? ck_dimension_substitute(k, t, 0, &one) : ck_substitute(k, t, 10, unit);
    assert(!out && cc_kernel_error_kind(k) == CC_ERROR_BUDGET && allocations > before);
    cc_kernel_clear_error(k);
    k->budget = 100000;
    out = dimensions ? ck_dimension_substitute(k, t, 0, &one) : ck_substitute(k, t, 10, unit);
    assert(out && !k->error[0]);
    for (unsigned i = 0; i < 450; ++i) {
        assert(k->nodes[out].kind == CC_SUM && k->nodes[out].child[1] == unit);
        out = k->nodes[out].child[0];
    }
    if (dimensions) {
        assert(k->nodes[out].kind == CC_PAPP && k->nodes[out].child[0] == x);
        assert(cc_equal(cc_kernel_get_formula(k, k->nodes[out].payload), &one));
    } else assert(out == unit);
    cc_clear(&one);
    cc_kernel_free(k);
}

int main(void) {
    for (unsigned sharing = 0; sharing < 2; ++sharing) {
        scopes(sharing ? CC_SHARE_SYNTAX : 0);
        interruption_and_pressure(sharing ? CC_SHARE_SYNTAX : 0);
        rollback(sharing ? CC_SHARE_SYNTAX : 0);
        capture_and_shadowing(sharing ? CC_SHARE_SYNTAX : 0);
        long_tubes(sharing ? CC_SHARE_SYNTAX : 0);
        variable_scan_failures(sharing ? CC_SHARE_SYNTAX : 0);
        substitution_failures(sharing ? CC_SHARE_SYNTAX : 0, false);
        substitution_failures(sharing ? CC_SHARE_SYNTAX : 0, true);
    }
    compaction();
    printf("Bounded substitution and dependency analysis: ok (%zu-byte syntax nodes).\n", sizeof(cc_node));
    return 0;
}
