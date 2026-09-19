#ifndef THTH_H
#define THTH_H
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include "tt_opcodes.h"
#ifdef __cplusplus
extern "C" {
#endif

/* An ID is an address in an engine's tables, not a mathematical numeral.
 * Context IDs, judgement IDs, and expression IDs use different tables even
 * though all three have this C type. Never interchange them. */
typedef uint32_t tt_id;
typedef struct tt_engine tt_engine;
typedef enum { TT_OK, TT_INVALID, TT_LIMIT, TT_OOM } tt_status;
typedef struct {
    uint32_t max_expression_nodes; /* 0 = unlimited (subject to depth bound). */
    uint32_t max_depth;            /* Default 256; protects recursive visitors. */
    uint32_t max_counter;
    uint32_t max_judgements; /* 0 = unlimited. */
    uint32_t max_ast_nodes;  /* 0 = unlimited. */
    bool allow_axioms;
    bool cache_inference;
} tt_config;
typedef struct {
    const char *name;
    /* Required premise count; whether a context is injected; number of
     * discharge slots; whether the result is a context instead of a judgement. */
    uint8_t judgements, context, free_contexts, returns_context;
    /* Bit i of pop_judgements[k]: discharge context k from premise i.
     * Bit k of allowed_free_contexts[l]: discharged context l may depend on k.
     * These are finite subsets encoded as integers, not counts. */
    uint8_t pop_judgements[4], allowed_free_contexts[4];
} tt_opcode_info;
typedef struct {
    tt_id expression, type;
    uint32_t context_count;
    tt_opcode justification;
    bool highlighted;
} tt_judgement_view;
typedef struct {
    const char *kind;
    uint32_t parameter; /* Reference ID or numeric payload; VRef uses int32_t. */
    tt_id children[4];
    uint32_t tree_nodes;
    uint16_t depth;
    uint8_t arity;
} tt_ast_view;
typedef struct {
    uint64_t inference_calls, inference_cache_hits, accepted, rejected;
    uint32_t ast_nodes, judgements, contexts;
    size_t reserved_bytes;
} tt_stats;

tt_config tt_default_config(void);
tt_engine *tt_new(const tt_config *config);
void tt_free(tt_engine *engine);
const tt_opcode_info *tt_opcode_metadata(tt_opcode opcode);
/* Propose one inference: premises are previously checked judgement IDs.
 * context supplies the assumption for Vble/UVble; free_contexts lists the
 * assumptions to bind/discharge (zero slots mean no variable is used).
 * On TT_OK, *result is the kind of handle specified by returns_context.
 * On failure, *result is zero. There is no public unchecked judgement API.
 * See docs/kernel.md for a complete example and the mathematical notation. */
tt_status tt_apply(tt_engine *, tt_opcode, const tt_id *judgements, size_t nj, tt_id context,
                   const tt_id *free_contexts, size_t nf, tt_id *result);
bool tt_judgement(const tt_engine *, tt_id, tt_judgement_view *);
bool tt_ast(const tt_engine *, tt_id, tt_ast_view *);
/* Optional inference trace, including normalized expression fingerprints.
 * Caller owns the stream; NULL disables tracing. Used by the Rust oracle. */
void tt_set_trace(tt_engine *, FILE *);
/* For already checked closed judgements P : U and p : P, confirm that the
 * expression of proposition is exactly the type of proof. This does not replay
 * their derivations or infer a type for an arbitrary expression tree. */
bool tt_verify(const tt_engine *, tt_id proposition, tt_id proof);
void tt_get_stats(const tt_engine *, tt_stats *);
void tt_print_judgement(const tt_engine *, tt_id, FILE *);
/* Checked upstream builtins; axioms are explicit and require allow_axioms. */
bool tt_load_builtins(tt_engine *, bool full);
bool tt_prove_composition(tt_engine *, tt_id *proposition, tt_id *proof);
bool tt_prove_product_commutes(tt_engine *, tt_id *proposition, tt_id *proof);
bool tt_run_proof_suite(tt_engine *, FILE *report);

#ifdef __cplusplus
}
#endif
#endif
