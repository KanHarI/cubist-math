#ifndef CUBICAL_TERM_KERNEL_H
#define CUBICAL_TERM_KERNEL_H

#include "cubical.h"

/* Raw syntax constructors are deliberately NOT proof certificates. Only
 * cc_kernel_check publishes a checked result. Names are numeric symbols whose
 * readable spelling is maintained by the caller; bound names are alpha-renamed.
 * A dimension name is separate from a term name and is currently 0..63. */
typedef uint32_t cc_term;
typedef uint32_t cc_formula_id;
typedef struct cc_kernel cc_kernel;

typedef enum {
    CC_U = 1, CC_VAR, CC_PI, CC_LAM, CC_APP, CC_SIGMA, CC_PAIR, CC_FST, CC_SND,
    CC_NAT, CC_ZERO, CC_SUCC, CC_NATREC, CC_UNIT, CC_POINT,
    CC_PATH, CC_PLAM, CC_PAPP, CC_COMP, CC_TUBE,
    CC_VOID, CC_ABORT, CC_W, CC_SUP, CC_WREC,
    CC_SUM, CC_INL, CC_INR, CC_SUMREC, CC_UNITREC,
    CC_GLUE, CC_GLUE_SYSTEM, CC_GLUE_TERM, CC_UNGLUE, CC_DEFREF,
    CC_PUSHOUT, CC_PUSH_LEFT, CC_PUSH_RIGHT, CC_PUSH_PATH, CC_PUSH_ELIM, CC_HCOMP, CC_TRANS
} cc_term_kind;

typedef struct {
    uint32_t symbol;
    cc_term type;
} cc_assumption;

typedef struct {
    cc_term expression, type, normal;
    uint64_t checking_steps, reduction_steps;
    size_t arena_nodes, arena_bytes;
} cc_checked_result;

cc_kernel *cc_kernel_new(void);
void cc_kernel_free(cc_kernel *);
/* Resource budget per checking/reduction operation; zero leaves it unchanged.
 * Raising it never bypasses a rule or certifies a previously rejected term. */
void cc_kernel_set_step_budget(cc_kernel *, uint64_t steps);
/* Optional wall-clock deadline shared by successive operations. Zero disables.
 * Expiry only rejects work; it can never make a judgement succeed. */
void cc_kernel_set_deadline_ms(cc_kernel *, double duration_ms);
const char *cc_kernel_error(const cc_kernel *);
/* Clear a rejected request before constructing corrected raw syntax. */
void cc_kernel_clear_error(cc_kernel *);
/* Diagnostic transactions. Abort invalidates ALL handles made since begin.
 * Callers must discard their corresponding syntax caches and context handles.
 * Only one checkpoint is retained; definitions before it remain checked. */
void cc_kernel_checkpoint(cc_kernel *);
void cc_kernel_rollback(cc_kernel *);
/* Commit keeps checked definitions and discards intermediate syntax. Handles
 * created since checkpoint must be translated with relocated() before reuse.
 * The relocation table lasts until the next checkpoint. */
bool cc_kernel_commit_checkpoint(cc_kernel *);
cc_term cc_kernel_relocated(const cc_kernel *, cc_term);

/* Child order:
 * U(level), Var(symbol); Pi/Lam/Sigma/W(symbol; domain, body).
 * App(fn,arg); Pair(type,first,second); Fst/Snd(pair); Succ(value).
 * NatRec(motive,zero,step,value).
 * Path(dimension; family,left,right); PLam(dimension; family,body).
 * PApp(formula; path); Comp(dimension; family,tubes,base).
 * Tube(face-formula; partial-term,next-tube), with zero terminating the list.
 * Abort(type,impossible); Sup(W-type,label,children); WRec(motive,step,value).
 * Sum(left,right); Inl/Inr(sum-type,value); SumRec(motive,left,right,value).
 * UnitRec(motive,point-case,value).
 * Glue(base,system); GlueSystem(face-formula; partial-type,equivalence,next).
 * GlueTerm(Glue-type,base-value,partial-tubes); Unglue(Glue-type,value).
 * Pushout(center,left,right,maps), maps : (center -> left) x (center -> right).
 * PushLeft/PushRight(pushout,value); PushPath(interval-formula; pushout,value).
 * PushElim(motive,left-case,right-case,bridge-case) is a function on the pushout.
 * HComp(dimension; pushout-type,tubes,base) binds only tube terms.
 * Trans(dimension; pushout-family,face-tube,base) binds only the family.
 * Trans's single face-tube stores phi; its term is discarded and rebuilt as base.
 * DefRef(registry-index) refers only to a previously checked definition.
 * Nat/Zero/Unit/Point/Void have no children. Missing children must be zero.
 * The checker discards an untrusted PApp's optional second child (annotation).
 */
cc_term cc_kernel_term(cc_kernel *, cc_term_kind, uint32_t payload,
                       cc_term a, cc_term b, cc_term c, cc_term d);
cc_formula_id cc_kernel_formula(cc_kernel *, const cc_formula *);

/* Ordered assumptions are themselves checked as a telescope. An expected type
 * of zero requests inference only. On failure, result is cleared. No old
 * production-kernel handle or axiom fallback can be supplied through this API. */
bool cc_kernel_check(cc_kernel *, cc_term, cc_term expected,
                     const cc_assumption *, size_t count, cc_checked_result *);

/* Check under named interval dimensions (bit d enables dimension d).
 * Assumption types may depend on those dimensions. No endpoints are sampled:
 * ordinary cubical rules check the whole open cube. The result remains open
 * in this telescope/cube and is not a closed definition certificate. */
bool cc_kernel_check_in_cube(cc_kernel *, cc_term, cc_term expected,
                             const cc_assumption *, size_t count,
                             uint64_t dimensions, cc_checked_result *);

/* Optional conversion strategy, never a typing certificate. References must
 * belong to this kernel's checked definition registry. Listed definitions
 * unfold in a preliminary comparison; count zero clears the strategy. The list
 * applies to check/define operations until replaced. Invalid input preserves
 * the prior list. Clear after a scoped hint even when a check is rejected. */
bool cc_kernel_set_unfolding_hints(cc_kernel *, const cc_term *references, size_t count);

/* Register a closed definition, checked using only earlier checked references.
 * A symbol may be registered once. On failure no definition is published.
 * The returned expression is a folded DefRef, never an assumed axiom. */
cc_term cc_kernel_define(cc_kernel *, uint32_t symbol, cc_term value, cc_term expected_type);
bool cc_kernel_definition(const cc_kernel *, cc_term reference, uint32_t *symbol,
                          cc_term *value, cc_term *type);
/* Expose only the demanded head. Like normalize, this is inspection only:
 * it accepts raw syntax but does not certify it, including under free names. */
cc_term cc_kernel_whnf(cc_kernel *, cc_term);

/* Explicit inspection reduction. Checking itself leaves terms compact.
 * This function does not certify a raw term; pass a successful checked handle. */
cc_term cc_kernel_normalize(cc_kernel *, cc_term);

/* Read-only inspection of inert syntax. It does not assert that a handle was
 * checked; callers should start from the handles in a successful result. */
bool cc_kernel_node(const cc_kernel *, cc_term, cc_term_kind *, uint32_t *, cc_term children[4]);
const cc_formula *cc_kernel_get_formula(const cc_kernel *, cc_formula_id);

#endif
