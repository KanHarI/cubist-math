#ifndef CUBICAL_TERM_INTERNAL_H
#define CUBICAL_TERM_INTERNAL_H
#include "cubical_kernel.h"
#include "internal.h"
#include <stdlib.h>
#include <string.h>
#include <limits.h>

typedef struct {
    cc_term_kind kind;
    uint32_t payload;
    cc_term child[4];
    unsigned depth;
} cc_node;

typedef struct cc_context {
    uint32_t name;
    cc_term type;
    const struct cc_context *previous;
} cc_context;

typedef struct {
    cc_term expression, type;
} cc_judgement;

struct cc_kernel {
    cc_node *nodes;
    cc_term *weak_cache;
    size_t count, capacity;
    cc_formula *formulas;
    size_t formula_count, formula_capacity;
    uint32_t next_symbol;
    uint64_t checking_steps, reduction_steps, budget;
    unsigned recursion;
    char error[192];
};

bool ck_fail(cc_kernel *, const char *);
bool ck_tick(cc_kernel *, bool checking);
unsigned ck_arity(cc_term_kind);
cc_term ck_make(cc_kernel *, cc_term_kind, uint32_t, cc_term, cc_term, cc_term, cc_term);
cc_term ck_var(cc_kernel *, uint32_t);
uint32_t ck_fresh_symbol(cc_kernel *);
bool ck_term_binder(cc_term_kind);
bool ck_dim_binder(cc_term_kind);
bool ck_term_free(cc_kernel *, cc_term, uint32_t);
uint64_t ck_free_dims(cc_kernel *, cc_term);
unsigned ck_fresh_dimension(cc_kernel *, uint64_t avoid);
cc_term ck_substitute(cc_kernel *, cc_term, uint32_t, cc_term);
cc_term ck_dimension_substitute(cc_kernel *, cc_term, unsigned, const cc_formula *);
cc_term ck_restrict(cc_kernel *, cc_term, cc_clause);
cc_term ck_whnf(cc_kernel *, cc_term);
cc_term ck_normal(cc_kernel *, cc_term);
bool ck_convertible(cc_kernel *, cc_term, cc_term);
bool ck_expect(cc_kernel *, cc_term actual, cc_term expected);
bool ck_infer(cc_kernel *, cc_term, const cc_context *, uint64_t, cc_judgement *);
bool ck_check(cc_kernel *, cc_term, cc_term, const cc_context *, uint64_t, cc_term *);
bool ck_type(cc_kernel *, cc_term, const cc_context *, uint64_t, cc_term *, uint32_t *);
bool ck_functions(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
bool ck_inductives(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
bool ck_paths(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
bool ck_composition(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
cc_term ck_reduce_composition(cc_kernel *, cc_term);
cc_term ck_endpoint_term(cc_kernel *, cc_term, unsigned, unsigned);
cc_formula_id ck_interval_variable(cc_kernel *, unsigned);
cc_formula_id ck_endpoint_face(cc_kernel *, unsigned, unsigned);

cc_context *ck_restricted_context(cc_kernel *, const cc_context *, cc_clause, size_t *);
cc_formula_id ck_clause_formula(cc_kernel *, cc_clause);
bool ck_glue(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
cc_term ck_equiv_type(cc_kernel *, cc_term, cc_term);
cc_term ck_fiber_type(cc_kernel *, cc_term, cc_term, cc_term, cc_term);
cc_term ck_contractible_type(cc_kernel *, cc_term);
cc_term ck_identity_equiv(cc_kernel *, cc_term);
cc_term ck_append_tube(cc_kernel *, cc_term, cc_formula_id, cc_term);
cc_term ck_fill(cc_kernel *, unsigned, cc_term, cc_term, cc_term, const cc_formula *);
cc_term ck_glue_composition(cc_kernel *, unsigned, cc_term, cc_term, cc_term);
cc_term ck_universe_composition(cc_kernel *, unsigned, cc_term, cc_term);
#endif
