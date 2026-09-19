#ifndef TT_INTERNAL_H
#define TT_INTERNAL_H
#include "thth.h"
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <assert.h>

/* Private trusted representation. Public clients see only opaque tt_engine and
 * checked handles in thth.h. See README.md beside this file before changing the
 * representation, binding conventions, or publication path. */

typedef enum {
    N_Axiom = 1,
    N_CRef,
    N_UCRef,
    N_VRef,
    N_DRef,
    N_U,
    N_UUOmega,
    N_UUKappa,
    N_Void,
    N_Unit,
    N_Singleton,
    N_Nat,
    N_ZN,
    N_SN,
    N_Lambda,
    N_Ap,
    N_Pi,
    N_Sigma,
    N_Tuple,
    N_Sum,
    N_Eq,
    N_Inl,
    N_Inr,
    N_Refl,
    N_DefEq,
    N_W,
    N_WSup,
    N_IndNat,
    N_IndSigma,
    N_IndSum,
    N_IndEq,
    N_IndVoid,
    N_IndUnit,
    N_IndW,
    N_Temp,
    N_Set,
    N_Path,
    N_Susp,
    N_North,
    N_South,
    N_Merid,
    N_IndSusp,
    N_SuspBeta,
    N_KIND_COUNT
} node_kind;
/* Mathematical syntax is a DAG (a tree with repeated subterms shared).
 * kind chooses the constructor; param is its reference/numeric payload;
 * ch[0..arity) are its ordered arguments. See docs/kernel.md's constructor map.
 * size counts the expanded tree, whereas arena length counts shared nodes. */
typedef struct {
    uint32_t kind, param;
    tt_id ch[4];
    uint32_t size;
    uint16_t depth;
    uint8_t arity, flags;
} node;
/* Only kind, param and children form the interning key. Size/depth/flags are
 * derived at allocation; arity is fixed by the constructor's kind. */
_Static_assert(offsetof(node, size) == 6 * sizeof(uint32_t), "node key layout");
enum { HAS_CONTEXT = 1, HAS_VARIABLE = 2, HAS_DEF = 4 };
/* Gamma |- expr : type. set encodes Gamma; path/highlight select a syntactic
 * occurrence for explicit rewriting. N_DefEq additionally records a checked
 * judgemental equality; it is not the identity type N_Eq. */
typedef struct {
    tt_id expr, type, set, path;
    uint32_t highlight; /* 0 absent, 1 expression, 2 type */
    uint16_t op, pad;
    tt_id inputs[5], free_ctx[4], ctx;
} judgement;
/* Semantic key ends at highlight. Derivation fields retain the first proof. */
_Static_assert(offsetof(judgement, op) == 5 * sizeof(uint32_t), "judgement key layout");
/* One named assumption x : type, together with assumptions needed by its type.
 * The context ID is x's identity. counter distinguishes otherwise identical
 * assumptions; it is neither a de Bruijn index nor a universe level. */
typedef struct {
    tt_id type, set;
    uint32_t counter;
    tt_id source;
} context;
_Static_assert(offsetof(context, source) == 3 * sizeof(uint32_t), "context key layout");
typedef struct {
    uint64_t hash;
    tt_id id;
    uint32_t pad;
} slot;
typedef struct {
    slot *slots;
    size_t cap, used;
} table;
typedef struct {
    uint32_t op;
    tt_id j[5], f[4], ctx, result;
    uint32_t status;
} inference_cache;
typedef struct {
    tt_id ast, ctx[4], values[4], result;
    uint32_t mode, depth, n, generation;
} map_cache;
struct tt_engine {
    tt_config conf;
    /* For each arena: n* is the number of occupied entries, c* its allocated
     * capacity. IDs index these arrays; entry zero is reserved as a sentinel. */
    node *nodes;
    uint32_t nn, cn;
    judgement *judgements;
    uint32_t nj, cj;
    context *contexts;
    uint32_t nc, cc;
    table nt, jt, ct;
    inference_cache *cache;
    size_t cache_cap;
    map_cache *maps;
    size_t map_cap;
    tt_stats stats;
    tt_status error;
    tt_id builtin[128];
    unsigned nbuiltin;
    bool full_builtins;
    bool proof_failed;
    uint32_t map_generation;
    uint64_t accepted_opcodes[204];
    FILE *trace;
};

uint64_t tt_mix(uint64_t x);
/* Internal rule functions accept already validated handles and copied premises.
 * They may allocate tentative AST nodes but must not publish judgements. */
bool context_matches(tt_engine *, tt_id context_id, tt_id type);
bool check_contexts(tt_engine *, const tt_opcode_info *, const judgement *, const tt_id *);
tt_id output_context(tt_engine *, const tt_opcode_info *, const judgement *, tt_id, const tt_id *);
bool infer_rule(tt_engine *, tt_opcode, const tt_id *, const judgement *, tt_id, const tt_id *,
                judgement *);
bool infer_suspension(tt_engine *, tt_opcode, const judgement *, judgement *);
bool infer_eliminator(tt_engine *, tt_opcode, const judgement *, const tt_id *, judgement *);
tt_id intern(tt_engine *, node);
void rollback_nodes(tt_engine *, uint32_t);
uint64_t fingerprint(const tt_engine *, tt_id);
tt_id leaf(tt_engine *, node_kind, uint32_t);
tt_id make1(tt_engine *, node_kind, tt_id);
tt_id make2(tt_engine *, node_kind, tt_id, tt_id);
tt_id make3(tt_engine *, node_kind, tt_id, tt_id, tt_id);
tt_id make4(tt_engine *, node_kind, tt_id, tt_id, tt_id, tt_id);
tt_id set_add(tt_engine *, tt_id, tt_id);
bool set_has(const tt_engine *, tt_id, tt_id);
uint32_t set_count(const tt_engine *, tt_id);
tt_id save_judgement(tt_engine *, judgement);
tt_id save_context(tt_engine *, context);
unsigned binders(unsigned kind);
bool universe(const tt_engine *, tt_id);
tt_id max_universe(tt_engine *, tt_id, tt_id);
/* Map modes retain upstream's node-wide binder-depth convention.
 * CONTEXT: replace named context references simultaneously; zero slots are absent.
 * BIND: replace contexts by VRef(depth + offset), closing an abstraction.
 * INSTANTIATE: replace the selected VRef in a dependent family (legacy behavior).
 * REPLACE: rewrite a structurally equal subtree by a DefEq witness.
 * SHIFT: shift free de Bruijn indices, checking signed overflow.
 * BETA_SUBST: remove binders and substitute, including legacy eliminator shifts.
 * W_MOTIVE: specialize C(z) at children(y), with y bound at the current depth. */
enum {
    MAP_CONTEXT,
    MAP_BIND,
    MAP_INSTANTIATE,
    MAP_REPLACE,
    MAP_SHIFT,
    MAP_BETA_SUBST,
    MAP_W_MOTIVE
};
tt_id transform(tt_engine *, tt_id, unsigned, const tt_id *, const tt_id *, unsigned, unsigned);
tt_id replace_ctx(tt_engine *, tt_id, tt_id, tt_id);
tt_id bind_ctx(tt_engine *, tt_id, tt_id, unsigned);
tt_id instantiate(tt_engine *, tt_id, tt_id);
tt_id reduce(tt_engine *, tt_id, bool, bool);
bool reducible(const tt_engine *, tt_id, bool);
tt_id pointed(const tt_engine *, tt_id, tt_id);
tt_id at_path(tt_engine *, tt_id, tt_id, tt_id);
tt_id path_append(tt_engine *, tt_id, unsigned);
tt_id path_pop(tt_engine *, tt_id);
#endif
