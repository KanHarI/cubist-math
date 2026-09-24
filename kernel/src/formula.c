/* Free distributive lattices represented by antichains of finite meets.
 * Mathematics: absorption a OR (a AND b) = a removes larger clauses.
 * Empty list = bottom; a list containing the empty clause = top. */
#include "internal.h"
#include <stdlib.h>

/* A proof may contain a compact formula whose distributed normal form is
 * exponential. Refuse that expansion before allocating or comparing it. */
enum { CC_MAX_CLAUSES = 4096, CC_MAX_LATTICE_WORK = 4000000 };

bool cc_valid_sort(cc_sort sort) {
    return sort == CC_INTERVAL || sort == CC_FACE;
}

void cc_init(cc_formula *f, cc_sort sort) {
    *f = (cc_formula){ .sort = sort };
}

void cc_clear(cc_formula *f) {
    free(f->clauses);
    cc_init(f, f->sort);
}

void cc_publish(cc_formula *output, cc_formula *candidate) {
    cc_clear(output);
    *output = *candidate;
    cc_init(candidate, candidate->sort);
}

bool cc_clause_subset(cc_clause a, cc_clause b) {
    return (a.positive & b.positive) == a.positive &&
           (a.negative & b.negative) == a.negative;
}

cc_status cc_insert_work(cc_formula *f, cc_clause clause, size_t *work) {
    if (!cc_valid_sort(f->sort))
        return CC_BAD_INPUT;
    if (f->length > CC_MAX_CLAUSES)
        return CC_LIMIT_EXCEEDED;
    /* This contradiction rule belongs ONLY to the face lattice. */
    if (f->sort == CC_FACE && (clause.positive & clause.negative))
        return CC_OK;
    for (size_t i = 0; i < f->length; ++i) {
        if (++*work > CC_MAX_LATTICE_WORK) return CC_LIMIT_EXCEEDED;
        if (cc_clause_subset(f->clauses[i], clause))
            return CC_OK;
    }

    size_t kept = 0;
    for (size_t i = 0; i < f->length; ++i) {
        if (++*work > CC_MAX_LATTICE_WORK) return CC_LIMIT_EXCEEDED;
        if (!cc_clause_subset(clause, f->clauses[i])) ++kept;
    }
    if (kept == CC_MAX_CLAUSES) return CC_LIMIT_EXCEEDED;
    if (kept == f->capacity) {
        if (f->capacity > SIZE_MAX / (2 * sizeof(cc_clause)))
            return CC_ALLOCATION_FAILED;
        size_t capacity = f->capacity ? 2 * f->capacity : 4;
        cc_clause *grown = realloc(f->clauses, capacity * sizeof(cc_clause));
        if (!grown)
            return CC_ALLOCATION_FAILED;
        f->clauses = grown;
        f->capacity = capacity;
    }
    size_t next = 0;
    for (size_t i = 0; i < f->length; ++i)
        if (!cc_clause_subset(clause, f->clauses[i])) f->clauses[next++] = f->clauses[i];
    f->length = next;
    f->clauses[f->length++] = clause;
    return CC_OK;
}

cc_status cc_insert(cc_formula *f, cc_clause clause) {
    size_t work = 0;
    return cc_insert_work(f, clause, &work);
}

cc_status cc_zero(cc_formula *out) {
    if (!cc_valid_sort(out->sort))
        return CC_BAD_INPUT;
    cc_clear(out);
    return CC_OK;
}

cc_status cc_one(cc_formula *out) {
    if (!cc_valid_sort(out->sort))
        return CC_BAD_INPUT;
    cc_formula candidate;
    cc_init(&candidate, out->sort);
    cc_status status = cc_insert(&candidate, (cc_clause){0, 0});
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    return status;
}

cc_status cc_generator(cc_formula *out, unsigned dimension, bool positive) {
    if (!cc_valid_sort(out->sort) || dimension >= CC_DIMENSIONS)
        return CC_BAD_INPUT;
    uint64_t bit = UINT64_C(1) << dimension;
    cc_formula candidate;
    cc_init(&candidate, out->sort);
    cc_status status = cc_insert(&candidate, (cc_clause){positive ? bit : 0, positive ? 0 : bit});
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    return status;
}

cc_status cc_copy(cc_formula *out, const cc_formula *a) {
    if (out->sort != a->sort || !cc_valid_sort(a->sort))
        return CC_BAD_INPUT;
    cc_formula candidate;
    cc_init(&candidate, out->sort);
    cc_status status = CC_OK;
    if (a->length > CC_MAX_CLAUSES) return CC_LIMIT_EXCEEDED;
    size_t work = 0;
    for (size_t i = 0; i < a->length && status == CC_OK; ++i)
        status = cc_insert_work(&candidate, a->clauses[i], &work);
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    return status;
}

cc_status cc_join_work(cc_formula *out, const cc_formula *a, const cc_formula *b,
                       size_t *work) {
    if (out->sort != a->sort || a->sort != b->sort || !cc_valid_sort(a->sort))
        return CC_BAD_INPUT;
    cc_formula candidate;
    cc_init(&candidate, out->sort);
    cc_status status = CC_OK;
    if (a->length > CC_MAX_CLAUSES || b->length > CC_MAX_CLAUSES ||
        b->length > CC_MAX_CLAUSES - a->length) return CC_LIMIT_EXCEEDED;
    for (size_t i = 0; i < a->length && status == CC_OK; ++i)
        status = cc_insert_work(&candidate, a->clauses[i], work);
    for (size_t i = 0; i < b->length && status == CC_OK; ++i)
        status = cc_insert_work(&candidate, b->clauses[i], work);
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    return status;
}

cc_status cc_join(cc_formula *out, const cc_formula *a, const cc_formula *b) {
    size_t work = 0;
    return cc_join_work(out, a, b, &work);
}

cc_status cc_meet_work(cc_formula *out, const cc_formula *a, const cc_formula *b,
                       size_t *work) {
    if (out->sort != a->sort || a->sort != b->sort || !cc_valid_sort(a->sort))
        return CC_BAD_INPUT;
    cc_formula candidate;
    cc_init(&candidate, out->sort);
    cc_status status = CC_OK;
    if (a->length && b->length > CC_MAX_CLAUSES / a->length)
        return CC_LIMIT_EXCEEDED;
    for (size_t i = 0; i < a->length && status == CC_OK; ++i)
        for (size_t j = 0; j < b->length && status == CC_OK; ++j) {
            cc_clause clause = {a->clauses[i].positive | b->clauses[j].positive,
                                a->clauses[i].negative | b->clauses[j].negative};
            status = cc_insert_work(&candidate, clause, work);
        }
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    return status;
}

cc_status cc_meet(cc_formula *out, const cc_formula *a, const cc_formula *b) {
    size_t work = 0;
    return cc_meet_work(out, a, b, &work);
}

bool cc_equal(const cc_formula *a, const cc_formula *b) {
    if (a->sort != b->sort || !cc_valid_sort(a->sort) || a->length != b->length)
        return false;
    for (size_t i = 0; i < a->length; ++i) {
        bool found = false;
        for (size_t j = 0; j < b->length; ++j)
            if (a->clauses[i].positive == b->clauses[j].positive &&
                a->clauses[i].negative == b->clauses[j].negative) {
                found = true;
                break;
            }
        if (!found)
            return false;
    }
    return true;
}
