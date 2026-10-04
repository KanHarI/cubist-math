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
    /* The names a node mentions, over-approximated, computed when it is made:
     * bit s % 64 for each term variable symbol s below it, and bit d for each
     * dimension d in a formula below it or bound by it. A clear bit proves
     * the name absent: alpha comparison checks it before asking exactly
     * whether a renamed name is free. */
    uint64_t symbols, dims;
} cc_node;

/* A definition: registered by instruction Define, from a derived closed
 * judgement, and read back by Lookup. */
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
enum { CC_FACT_TYPING = 1, CC_FACT_EQUALITY = 2, CC_FACT_SYSTEM = 3, CC_FACT_SIGNATURE = 4, CC_FACT_INSTANCE = 5,
       CC_FACT_ELIMINATOR = 6 };
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
    /* A composition system: the positions of the tubes its last tube
     * overlaps and has not yet been shown to agree with. */
    uint64_t pending;
} cc_fact;
typedef struct {
    uint32_t symbol;  /* a term symbol, or a dimension index */
    cc_term type;     /* zero for a dimension */
    cc_term level;    /* the level of the type's universe, canonical */
    uint32_t context; /* the context the type needs */
    uint32_t scope;   /* that context and the entry itself */
    uint32_t source;  /* the judgement that the type is a type */
    bool dimension;
    bool level_variable; /* a level entry x < ω: its type is LBound(1) */
    /* A face entry, Γ, φ: the assumption that a clause holds, which Restrict
     * adds. It has no symbol and no type; its context is the clause's
     * dimension entries, so no binder discharges them while it is there.
     * Only an instruction that takes a value on a face implying the clause,
     * a partial element, discharges it. */
    bool face;
    cc_clause clause;
} cc_entry;
typedef struct {
    size_t offset;
    uint32_t count;
} cc_context_set;

/* Declared types (signatures.c, H1). A constructor's type is over the
 * admission symbols: the universe and term parameters, the sort and the
 * earlier constructors. A signature is open until SignatureClose, then
 * immutable. The checkpoint fields restore an open signature on rollback. */
typedef struct {
    uint32_t symbol, data, positions, dimensions;
    cc_term type;
    bool generated;
} cc_constructor;
typedef struct {
    bool admitted, experimental;
    uint32_t modifier, sort_symbol, level_count, parameter_count, recorded;
    cc_term former, level;
    uint32_t *symbols;            /* universe parameters, then term parameters */
    cc_term *parameter_types;     /* one per term parameter, over earlier symbols */
    cc_constructor *constructors;
    uint32_t constructor_count, constructor_capacity;
    uint32_t checkpoint_constructors;
    bool checkpoint_admitted;
} cc_signature;
void ck_signatures_free(cc_kernel *);
void ck_signatures_checkpoint(cc_kernel *);
void ck_signatures_rollback(cc_kernel *);
/* A signature opened or extended since the checkpoint, and still open. */
bool ck_signatures_open(const cc_kernel *);
/* An instance term's admitted signature, a constructor's type at an instance
 * (3.2), and whether a signature is a higher sort (3.4). */
const cc_signature *ck_instance_signature(cc_kernel *, cc_term instance);
cc_term ck_constructor_type(cc_kernel *, cc_term instance, uint32_t constructor);
bool ck_signature_higher(const cc_signature *);

/* Exact-key memo entries affect time only. A collision discards the older
 * entry; it can never establish equality or approve an unchecked term. */
typedef struct {
    uint32_t operation, term, name, value;
    uint64_t result;
} cc_syntax_memo;
#define CC_SYNTAX_MEMO_SIZE 8192
#define CC_INTERN_MINIMUM 65536

/* Comparison keys include exact, never-reused binder-renaming scopes. An
 * identity renaming is equivalent to the empty renaming and uses scope zero.
 * An entry holds the result of the syntactic comparison (ck_alpha_equal) for
 * its pair: equal or different, up to bound names. It caches syntax, never a
 * typing judgement. */
enum { CC_FOLDED_UNKNOWN, CC_FOLDED_EQUAL, CC_FOLDED_DIFFERENT };
typedef struct {
    cc_term left, right;
    uint64_t term_scope, dimension_scope;
    uint8_t folded;
} cc_alpha_memo;
#define CC_ALPHA_MEMO_SIZE 8192

/* Intern complete renaming chains so repeated comparisons beneath the same
 * binders can share results. Evicted identities are never reassigned. */
typedef struct {
    uint32_t left, right;
    uint64_t parent, scope;
} cc_alpha_scope;

struct cc_kernel {
    unsigned optimizations;
    cc_node *nodes;
    cc_term *weak_cache;
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
    cc_definition *definitions;
    size_t definition_count, definition_capacity;
    cc_formula *formulas;
    size_t formula_count, formula_capacity;
    uint32_t next_symbol;
    uint64_t budget, operation_budget;
    /* Cumulative work (cc_kernel_work) and the kind of operation now running,
     * which its steps and its error are charged to. Never reset. */
    cc_work_counters work;
    unsigned work_phase;
    double deadline_ms;
    unsigned deadline_ticks;
    unsigned recursion;
    char error[192];
    cc_error_kind error_kind; /* meaningful only while error is set */
    cc_term mismatch_found, mismatch_expected; /* meaningful for a MISMATCH error */
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
    /* Declared types (H1). Index 0 is invalid. */
    unsigned extensions;
    cc_signature *signatures;
    size_t signature_count, signature_capacity, checkpoint_signatures;
};
/* The instruction machinery (instructions.c), for instruction families kept
 * in their own files. */
bool ck_instr_ready(cc_kernel *);
/* The machinery instruction families share (instructions.c): judgements,
 * premises, contexts and their entries, the syntactic comparison of a side
 * condition, and building syntax. */
bool ck_instr_entry(cc_kernel *, cc_entry_id, bool dimension, cc_entry *out);
cc_judgement_id ck_instr_typing(cc_kernel *, cc_term term, cc_term type, uint32_t context);
bool ck_instr_same(cc_kernel *, cc_term found, cc_term expected, const char *message);
bool ck_instr_universe(cc_kernel *, cc_term type, cc_term *level);
cc_term ck_instr_make(cc_kernel *, cc_term_kind, uint32_t payload, cc_term a, cc_term b, cc_term c, cc_term d);
cc_term ck_instr_app(cc_kernel *, cc_term f, cc_term x);
bool ck_instr_merge3(cc_kernel *, uint32_t a, uint32_t b, uint32_t c, uint32_t *out);
bool ck_instr_discharge(cc_kernel *, uint32_t set, const cc_entry_id *removed, size_t count, uint32_t *out);
bool ck_instr_bind(cc_kernel *, uint32_t body, cc_entry_id, uint32_t *out);
cc_entry_id ck_instr_dimension_entry(cc_kernel *, unsigned index);
cc_entry_id ck_instr_face_entry(cc_kernel *, cc_clause);
bool ck_instr_on_face(cc_kernel *, uint32_t set, cc_clause, uint32_t *out);
/* Paths and composition (instruction_paths.c), for Glue's systems. */
bool ck_instr_formula_context(cc_kernel *, const cc_formula *, uint32_t *out);
cc_term ck_instr_append_tube(cc_kernel *, cc_term tubes, cc_formula_id face, cc_term tube);
cc_judgement_id ck_instr_system_fact(cc_kernel *, cc_term comp, cc_term type, uint32_t context, uint64_t pending);
bool ck_instr_begin(cc_kernel *, cc_derivation, const uint8_t *position, size_t depth, cc_judgement_id *found);
/* Begin an instruction whose result depends on the signature table, which
 * changes: it is never answered from the derivation cache. */
bool ck_instr_begin_stateful(cc_kernel *, cc_derivation);
cc_judgement_id ck_instr_publish(cc_kernel *, uint32_t kind, cc_term term, cc_term other, cc_term type,
                                 uint32_t context);
bool ck_instr_premise(cc_kernel *, cc_judgement_id, uint32_t kind, cc_fact *);
bool ck_instr_merge(cc_kernel *, uint32_t a, uint32_t b, uint32_t *out);
bool ck_instr_finite_level(cc_kernel *, cc_term level, cc_term *canonical, uint32_t *context);
bool ck_instr_level(cc_kernel *, cc_term level, bool finite, cc_term *canonical, uint32_t *context);
bool ck_alpha_equal(cc_kernel *, cc_term, cc_term);

/* Universe levels (levels.c, G0 §2.4). A normal form is finite, a tier-0
 * constant with an offset for each variable it mentions, sorted by key; or a
 * constant of tier 1 or above, with no variables. Keys are symbols. */
typedef struct {
    uint64_t key;
    uint32_t offset;
} cc_level_term;
typedef struct {
    uint32_t tier, constant, count, capacity;
    cc_level_term *terms;
} cc_level_nf;
bool ck_level_normal(cc_kernel *, cc_term level, cc_level_nf *);
void ck_level_nf_free(cc_level_nf *);
cc_term ck_level_build(cc_kernel *, const cc_level_nf *);
cc_term ck_level_constant(cc_kernel *, uint32_t tier, uint32_t value);
bool ck_level_equal(cc_kernel *, cc_term, cc_term);
bool ck_level_leq(cc_kernel *, cc_term, cc_term);
cc_term ck_level_canonical(cc_kernel *, cc_term);
cc_term ck_level_max(cc_kernel *, cc_term, cc_term);
cc_term ck_level_limit(cc_kernel *, uint32_t symbol, cc_term);
cc_term ck_universe(cc_kernel *, cc_term level);
void ck_level_nf_sort(cc_level_nf *);
bool ck_level_nf_succ(cc_kernel *, cc_level_nf *);
bool ck_level_nf_equal(const cc_level_nf *, const cc_level_nf *);
/* t[x := l] for a level variable x, capture-avoiding, with every level of
 * the result in normal form (G0 §2.8). */
cc_term ck_level_instantiate(cc_kernel *, cc_term body, uint32_t symbol, cc_term level);
cc_term ck_canonical_levels(cc_kernel *, cc_term);
cc_term ck_universe_at(cc_kernel *, uint32_t level);
bool ck_syntactic_cumulative(cc_kernel *, cc_term actual, cc_term expected);
void ck_intern(cc_kernel *, cc_term);

bool ck_memo_get(cc_kernel *, uint32_t operation, cc_term, uint32_t name, cc_term value, uint64_t *result);
void ck_memo_put(cc_kernel *, uint32_t operation, cc_term, uint32_t name, cc_term value, uint64_t result);
bool ck_fail(cc_kernel *, const char *);
bool ck_fail_as(cc_kernel *, cc_error_kind, const char *);
bool ck_tick(cc_kernel *);
/* Start an operation (cubical_kernel.h, cc_kernel_work): charge its steps and
 * its error to its kind, count it, and give it a full budget. It leaves the
 * recursion depth to the caller, as each entry point did before. */
enum { CC_WORK_NONE, CC_WORK_INSTRUCTION, CC_WORK_QUERY };
void ck_operation(cc_kernel *, unsigned phase);
void ck_standalone(cc_kernel *);
/* cc_kernel_formula without leaving the current operation: for the kernel's
 * own use inside an operation. */
cc_formula_id ck_formula(cc_kernel *, const cc_formula *);
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
/* Glue eta with its side conditions normalized (CC_STEP_GLUE). */
cc_term ck_glue_step(cc_kernel *, cc_term);
cc_term ck_reduce_composition(cc_kernel *, cc_term);
cc_term ck_inductive_composition(cc_kernel *, cc_term, cc_term, cc_term);
/* Declared types (F4, inductive_composition.c): a saturated constructor
 * application's number and arguments; a constructor type's first count
 * arguments as the telescope Σ (x_1 : A_1). … Unit, a tuple in it, and
 * Con(c; I) applied to a tuple's components; composition at an instance. */
bool ck_constructor_application(cc_kernel *, cc_term, uint32_t *constructor, cc_term *arguments, uint32_t *count);
cc_term ck_telescope(cc_kernel *, cc_term type, uint32_t count);
cc_term ck_tuple(cc_kernel *, cc_term telescope, const cc_term *arguments, uint32_t count);
cc_term ck_apply_components(cc_kernel *, cc_term instance, uint32_t constructor, cc_term tuple, uint32_t count);
cc_term ck_sort_composition(cc_kernel *, cc_term term, cc_term family, cc_term system);
/* t @ r_1 … @ r_d, each application annotated with the type of the path it
 * applies, read from t's type (hit_composition.c). */
cc_term ck_apply_at(cc_kernel *, cc_term t, cc_term type, const cc_formula_id *formulas, uint32_t count);
/* Elimination of declared types (F5, eliminators.c): elim applied to an
 * argument, by Iota on a constructor and, when weak, on the weak head of the
 * argument, hcomp included; the application itself, not reduced, otherwise. */
cc_term ck_eliminate(cc_kernel *, cc_term eliminator, cc_term argument, bool weak, bool *reduced);
cc_term ck_clause_type(cc_kernel *, cc_term instance, cc_term motive, const cc_term *clauses, uint32_t constructor);
cc_term ck_endpoint_term(cc_kernel *, cc_term, unsigned, unsigned);
cc_formula_id ck_interval_variable(cc_kernel *, unsigned);
cc_formula_id ck_endpoint_face(cc_kernel *, unsigned, unsigned);

cc_formula_id ck_clause_formula(cc_kernel *, cc_clause);
cc_term ck_hit_reduce(cc_kernel *, cc_term);
cc_term ck_higher_composition(cc_kernel *, unsigned, cc_term, cc_term, cc_term);
cc_term ck_eliminate_hcomp(cc_kernel *, cc_term, cc_term);
cc_term ck_equiv_type(cc_kernel *, cc_term, cc_term);
cc_term ck_fiber_type(cc_kernel *, cc_term, cc_term, cc_term, cc_term);
cc_term ck_contractible_type(cc_kernel *, cc_term);
cc_term ck_identity_equiv(cc_kernel *, cc_term);
cc_term ck_append_tube(cc_kernel *, cc_term, cc_formula_id, cc_term);
/* A composition's system one clause to a tube, and with `drop_empty`
 * without its tubes on the face 0 (CC_STEP_SPLIT). */
cc_term ck_clause_tubes(cc_kernel *, cc_term, bool drop_empty);
cc_term ck_fill(cc_kernel *, unsigned, cc_term, cc_term, cc_term, const cc_formula *);
cc_term ck_glue_composition(cc_kernel *, unsigned, cc_term, cc_term, cc_term);
cc_term ck_universe_composition(cc_kernel *, unsigned, cc_term, cc_term);
#endif
