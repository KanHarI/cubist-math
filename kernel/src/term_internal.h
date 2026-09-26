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
    uint64_t identity; /* Exact telescope identity, never a pointer or hash. */
} cc_context;

typedef struct {
    cc_term expression, type;
} cc_judgement;

typedef struct {
    uint32_t symbol;
    cc_term value, type;
} cc_definition;

/* The judgement graph (instructions.c). A fact is a typing judgement
 * Γ ⊢ term : type, or an equality judgement Γ ⊢ term ≡ other : type, with
 * the instruction and operands that derived it. Its context is a set of
 * entries, sorted by creation; an entry records the context its own type
 * needs, so every set is closed under dependencies. Context set zero is the
 * empty context; fact and entry zero are invalid. */
enum { CC_FACT_TYPING = 1, CC_FACT_EQUALITY = 2, CC_FACT_SYSTEM = 3 };
typedef struct {
    uint32_t rule;
    uint32_t premise[4];
    uint32_t entry;
    uint32_t operand[2];
    uint32_t position, depth; /* into the kernel's positions */
} cc_derivation;
typedef struct {
    uint32_t kind;
    cc_term term, other, type;
    uint32_t context;
    cc_derivation how;
} cc_fact;
typedef struct {
    uint32_t symbol;  /* a term symbol, or a dimension index */
    cc_term type;     /* zero for a dimension */
    uint32_t level;   /* the universe of the type */
    uint32_t context; /* the context the type needs */
    uint32_t scope;   /* that context and the entry itself */
    uint32_t source;  /* the judgement that the type is a type */
    bool dimension;
} cc_entry;
typedef struct {
    size_t offset;
    uint32_t count;
} cc_context_set;

/* Exact-key memo entries affect time only. A collision discards the older
 * entry; it can never establish equality or approve an unchecked term. */
typedef struct {
    uint32_t operation, term, name, value;
    uint64_t result;
} cc_syntax_memo;
#define CC_SYNTAX_MEMO_SIZE 8192
#define CC_INTERN_MINIMUM 65536

/* Conversion keys include exact, never-reused binder-renaming scopes. An
 * identity renaming is equivalent to the empty renaming and uses scope zero.
 * Success is reusable in every strategy; failure means only that the folded
 * syntax differed. This caches equality, never a typing judgement. */
typedef struct {
    cc_term left, right;
    uint64_t term_scope, dimension_scope;
    bool equal;
} cc_alpha_memo;
#define CC_ALPHA_MEMO_SIZE 8192

/* Intern complete renaming chains so repeated comparisons beneath the same
 * binders can share results. Evicted identities are never reassigned. */
typedef struct {
    uint32_t left, right;
    uint64_t parent, scope;
} cc_alpha_scope;

typedef struct {
    uint32_t name;
    cc_term type;
    uint64_t parent, identity;
} cc_context_memo;
typedef struct {
    cc_term raw;
    uint64_t context, dimensions;
    cc_judgement checked;
} cc_infer_memo;
#define CC_CHECK_MEMO_SIZE 16384

struct cc_kernel {
    unsigned optimizations;
    cc_node *nodes;
    cc_term *weak_cache;
    cc_context_memo *contexts;
    cc_infer_memo *inferred;
    uint64_t next_context;
    /* The syntax hash graph: with CC_SHARE_SYNTAX, identical syntax has one
     * handle. An index of live nodes, never a typing certificate. Discarded
     * handles act as tombstones until the table is rebuilt. */
    cc_term *interned;
    size_t intern_capacity, intern_used;
    cc_syntax_memo *syntax_memo;
    cc_alpha_memo *alpha_memo;
    cc_alpha_scope *alpha_scopes;
    uint64_t next_alpha_scope;
    size_t count, capacity;
    size_t checkpoint_count, checkpoint_definitions;
    cc_term *relocation;
    size_t relocation_base, relocation_count;
    uint32_t *unfolding_hints;
    size_t unfolding_hint_count;
    cc_definition *definitions;
    size_t definition_count, definition_capacity;
    cc_formula *formulas;
    size_t formula_count, formula_capacity;
    uint32_t next_symbol;
    uint64_t checking_steps, reduction_steps, budget, operation_budget;
    double deadline_ms;
    unsigned deadline_ticks;
    unsigned recursion;
    char error[192];
    cc_error_kind error_kind; /* meaningful only while error is set */
    cc_term mismatch_found, mismatch_expected; /* meaningful for a MISMATCH error */
    /* An optional record of checking events. It observes the rules and never
     * influences them. trace_mute silences events nested in a conversion. */
    cc_trace_event *trace;
    size_t trace_count, trace_capacity;
    unsigned trace_depth, trace_mute;
    cc_fact *facts;
    size_t fact_count, fact_capacity;
    cc_entry *entries;
    size_t entry_count, entry_capacity;
    cc_context_set *context_sets;
    size_t context_set_count, context_set_capacity;
    uint32_t *context_items;
    size_t context_item_count, context_item_capacity;
    uint8_t *positions;
    size_t position_count, position_capacity;
    /* Facts by derivation. Truncated ids are tombstones until a rebuild. */
    uint32_t *derivations;
    size_t derivation_capacity, derivation_used;
    /* Term entries by symbol, and the dimension entry of each index. Truncated
     * ids are ignored, as in the derivation index. */
    uint32_t *entry_index;
    size_t entry_index_capacity, entry_index_used;
    uint32_t dimension_entries[CC_DIMENSIONS];
    cc_derivation pending; /* the instruction being checked */
    const uint8_t *pending_position;
    size_t checkpoint_store[5]; /* facts, entries, context sets, items, positions */
};
bool ck_alpha_equal(cc_kernel *, cc_term, cc_term);
bool ck_syntactic_cumulative(cc_kernel *, cc_term actual, cc_term expected);
void ck_trace(cc_kernel *, cc_trace_kind, uint32_t a, uint32_t b, uint32_t c);
void ck_intern(cc_kernel *, cc_term);

cc_context ck_extend(cc_kernel *, uint32_t, cc_term, const cc_context *);
void ck_clear_check_cache(cc_kernel *);
bool ck_inference_get(cc_kernel *, cc_term, const cc_context *, uint64_t, cc_judgement *);
void ck_inference_put(cc_kernel *, cc_term, const cc_context *, uint64_t, cc_judgement);

bool ck_memo_get(cc_kernel *, uint32_t operation, cc_term, uint32_t name, cc_term value, uint64_t *result);
void ck_memo_put(cc_kernel *, uint32_t operation, cc_term, uint32_t name, cc_term value, uint64_t result);
bool ck_fail(cc_kernel *, const char *);
bool ck_fail_as(cc_kernel *, cc_error_kind, const char *);
bool ck_tick(cc_kernel *, bool checking);
bool ck_deadline(cc_kernel *);
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
cc_term ck_expose(cc_kernel *, cc_term);
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
cc_term ck_inductive_composition(cc_kernel *, cc_term, cc_term, cc_term);
cc_term ck_endpoint_term(cc_kernel *, cc_term, unsigned, unsigned);
cc_formula_id ck_interval_variable(cc_kernel *, unsigned);
cc_formula_id ck_endpoint_face(cc_kernel *, unsigned, unsigned);

cc_context *ck_restricted_context(cc_kernel *, const cc_context *, cc_clause, size_t *);
cc_formula_id ck_clause_formula(cc_kernel *, cc_clause);
bool ck_hit_composition(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
cc_term ck_hit_reduce(cc_kernel *, cc_term);
cc_term ck_pushout_composition(cc_kernel *, unsigned, cc_term, cc_term, cc_term);
cc_term ck_pushout_eliminate_hcomp(cc_kernel *, cc_term, cc_term);
bool ck_pushout(cc_kernel *, cc_node, const cc_context *, uint64_t, cc_judgement *);
cc_term ck_pushout_bridge_type(cc_kernel *, cc_term, cc_term, cc_term, cc_term, cc_term);
cc_term ck_pushout_reduce(cc_kernel *, cc_term);
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
