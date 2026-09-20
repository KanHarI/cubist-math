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
    CC_SUM, CC_INL, CC_INR, CC_SUMREC, CC_UNITREC
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
const char *cc_kernel_error(const cc_kernel *);
/* Clear a rejected request before constructing corrected raw syntax. */
void cc_kernel_clear_error(cc_kernel *);

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

/* Explicit inspection reduction. Checking itself leaves terms compact.
 * This function does not certify a raw term; pass a successful checked handle. */
cc_term cc_kernel_normalize(cc_kernel *, cc_term);

/* Read-only inspection of inert syntax. It does not assert that a handle was
 * checked; callers should start from the handles in a successful result. */
bool cc_kernel_node(const cc_kernel *, cc_term, cc_term_kind *, uint32_t *, cc_term children[4]);
const cc_formula *cc_kernel_get_formula(const cc_kernel *, cc_formula_id);

#endif
