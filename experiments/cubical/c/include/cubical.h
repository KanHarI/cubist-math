#ifndef CUBICAL_EXPERIMENT_H
#define CUBICAL_EXPERIMENT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* First part of a NEW experimental kernel, not the production thth API.
 * Interval expressions and faces are different mathematical sorts. Their
 * shared representation is a disjunction of conjunctions of generators.
 * In an interval clause, positive means i and negative means 1-i.
 * In a face clause, positive means i=1 and negative means i=0.
 * Only the latter forbids both generators for the same dimension. */
typedef enum { CC_INTERVAL, CC_FACE } cc_sort;
typedef enum { CC_OK, CC_BAD_INPUT, CC_ALLOCATION_FAILED } cc_status;
typedef struct { uint64_t positive, negative; } cc_clause;
typedef struct {
    cc_sort sort;
    cc_clause *clauses;
    size_t length, capacity;
} cc_formula;

/* Dimension identifiers 0..63 are supported in this first native prototype.
 * An out-of-range identifier is REJECTED, never truncated or identified with
 * another dimension. Growing beyond 64 needs a wider representation; it is
 * not a mathematical restriction on the selected cubical calculus. */
enum { CC_DIMENSIONS = 64 };

void cc_init(cc_formula *, cc_sort);
void cc_clear(cc_formula *);
/* Initialize every output before use. Operations are transactional and permit
 * output/input aliasing. Failure leaves the output unchanged. No allocation
 * failure is interpreted as a mathematical equality or a successful check. */
cc_status cc_zero(cc_formula *);
cc_status cc_one(cc_formula *);
cc_status cc_generator(cc_formula *, unsigned dimension, bool positive);
cc_status cc_copy(cc_formula *, const cc_formula *);
cc_status cc_join(cc_formula *, const cc_formula *, const cc_formula *);
cc_status cc_meet(cc_formula *, const cc_formula *, const cc_formula *);
bool cc_equal(const cc_formula *, const cc_formula *);

/* Reversal in the free De Morgan algebra, not Boolean complementation. */
cc_status cc_reverse(cc_formula *, const cc_formula *);
cc_status cc_interval_substitute(cc_formula *, const cc_formula *, unsigned,
                                 const cc_formula *);

/* (r=endpoint) is a face formula, computed from interval expression r. */
cc_status cc_endpoint(cc_formula *, const cc_formula *, unsigned endpoint);
cc_status cc_face_substitute(cc_formula *, const cc_formula *, unsigned,
                             const cc_formula *);
/* Return the decision in result only on CC_OK. Interval implication is NOT
 * silently used for face entailment or vice versa. */
cc_status cc_face_entails(const cc_formula *, const cc_formula *, bool *result);

#endif
