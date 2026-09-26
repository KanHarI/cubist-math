#ifndef CUBICAL_TERM_KERNEL_H
#define CUBICAL_TERM_KERNEL_H

#include "cubical.h"

/* Raw syntax constructors are deliberately NOT proof certificates. Only
 * cc_kernel_check publishes a checked result. Names are numeric symbols whose
 * readable spelling is maintained by the caller; bound names are renamed when necessary to avoid shadowing.
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
/* Independent performance switches, enabled by default. Neither changes the
 * judgement rules. Disabling a cache discards its entries immediately. */
enum { CC_SHARE_SYNTAX = 1, CC_REUSE_CHECKS = 2 };
void cc_kernel_set_optimizations(cc_kernel *, unsigned flags);
/* Optional wall-clock deadline shared by successive operations. Zero disables.
 * Expiry only rejects work; it can never make a judgement succeed. */
void cc_kernel_set_deadline_ms(cc_kernel *, double duration_ms);
const char *cc_kernel_error(const cc_kernel *);
/* The class of the recorded error, so callers need not read its text.
 * MISMATCH: a type is not convertible to, or cumulative with, the expected
 * type. BUDGET, DEADLINE: the step budget or the deadline ran out, so no
 * judgement was made. OTHER: any other rejection. NONE: no error. */
typedef enum {
    CC_ERROR_NONE, CC_ERROR_MISMATCH, CC_ERROR_BUDGET, CC_ERROR_DEADLINE, CC_ERROR_OTHER
} cc_error_kind;
cc_error_kind cc_kernel_error_kind(const cc_kernel *);
/* For a MISMATCH error, the type that was found and the type it was expected
 * to match, for diagnostics. Returns false for any other error or none. The
 * handles are valid until the next rollback, which also clears the error. */
bool cc_kernel_mismatch(const cc_kernel *, cc_term *found, cc_term *expected);
/* An optional trace of the checker's actions, for inspection only. It
 * records events as the rules run and never changes a judgement. Starting a
 * trace discards the previous one; events beyond its capacity are counted but
 * not kept. Handles in events are valid until the next rollback.
 *   INFER      a: raw term; the events that check it follow, one level deeper.
 *   INFERRED   a: raw term, b: checked term, c: its type; b = c = 0 on failure.
 *   REUSED     a: raw term, b: checked term, c: its type, from the check cache.
 *   EXTEND     a: bound symbol, b: its type: the context gains an assumption.
 *   CONVERT    a: type found, b: type expected, c: 1 when they agree.
 *   REDUCE     a: term, b: its weak head normal form, when they differ.
 * Reductions inside a conversion are not recorded. */
typedef enum {
    CC_TRACE_INFER = 1, CC_TRACE_INFERRED, CC_TRACE_REUSED, CC_TRACE_EXTEND, CC_TRACE_CONVERT, CC_TRACE_REDUCE
} cc_trace_kind;
typedef struct {
    uint32_t kind, depth, a, b, c;
} cc_trace_event;
bool cc_kernel_trace_start(cc_kernel *, size_t capacity);
void cc_kernel_trace_stop(cc_kernel *);
size_t cc_kernel_trace_count(const cc_kernel *);
bool cc_kernel_trace_event(const cc_kernel *, size_t index, cc_trace_event *);
/* Instructions (instructions.c): THTH-style forward rules on a store of
 * judgements, beside cc_kernel_check. An instruction takes earlier judgements
 * and context entries, checks its side conditions syntactically — types must
 * be identical up to bound names — and returns a new judgement, or 0 with an
 * error. Nothing is reduced or unfolded except by an equality instruction
 * that names the position and the rule. A judgement keeps only the context
 * entries it depends on, and the contexts of premises merge.
 *
 * Judgements are typing judgements Γ ⊢ t : T, or equality judgements
 * Γ ⊢ a ≡ b : T. Equalities are built from reflexivity by targeted steps: a
 * step contracts one redex at a position (a path of child indices, the
 * highlighted subterm), and a replacement rewrites a highlighted occurrence
 * of a by b, given a ≡ b. Conversion moves t : A to t : B along A ≡ B.
 *
 * The store is truncated by rollback and by commit_checkpoint to its size at
 * the checkpoint; judgements from before it stay valid after a rollback. */
typedef uint32_t cc_judgement_id;
typedef uint32_t cc_entry_id;
typedef enum {
    CC_STEP_BETA = 1,  /* App(Lam(x. b), a) to b[a/x] */
    CC_STEP_DELTA,     /* a definition to its checked value */
    CC_STEP_IOTA,      /* an eliminator or projection on a constructor */
    CC_STEP_PATH,      /* a path lambda applied at an interval point, or a
                        * path applied at an endpoint of its annotated type */
    CC_STEP_NORMALIZE  /* the normal form, by the kernel's fixed strategy */
} cc_step_rule;

cc_judgement_id cc_instr_universe(cc_kernel *, uint32_t level);           /* ⊢ U(l) : U(l+1) */
cc_judgement_id cc_instr_nat(cc_kernel *);                                /* ⊢ Nat : U0 */
cc_judgement_id cc_instr_zero(cc_kernel *);                               /* ⊢ 0 : Nat */
cc_judgement_id cc_instr_succ(cc_kernel *, cc_judgement_id);              /* n : Nat ⊢ succ(n) : Nat */
cc_judgement_id cc_instr_nat_elim(cc_kernel *, cc_judgement_id motive, cc_judgement_id zero,
                                  cc_judgement_id step, cc_judgement_id value);
cc_judgement_id cc_instr_unit(cc_kernel *);
cc_judgement_id cc_instr_point(cc_kernel *);
cc_judgement_id cc_instr_unit_elim(cc_kernel *, cc_judgement_id motive, cc_judgement_id point,
                                   cc_judgement_id value);
cc_judgement_id cc_instr_void(cc_kernel *);
cc_judgement_id cc_instr_abort(cc_kernel *, cc_judgement_id type, cc_judgement_id impossible);
/* A term entry x : A, from Γ ⊢ A : U(i); the symbol must be new. */
cc_entry_id cc_instr_extend(cc_kernel *, cc_judgement_id type, uint32_t symbol);
/* A dimension entry, with its interval index. */
cc_entry_id cc_instr_dimension(cc_kernel *, unsigned index);
cc_judgement_id cc_instr_variable(cc_kernel *, cc_entry_id);              /* Γ, x : A ⊢ x : A */
/* Binders discharge an entry that no other entry of the premise depends on. */
cc_judgement_id cc_instr_pi(cc_kernel *, cc_entry_id, cc_judgement_id codomain);
cc_judgement_id cc_instr_lambda(cc_kernel *, cc_entry_id, cc_judgement_id body);
cc_judgement_id cc_instr_apply(cc_kernel *, cc_judgement_id function, cc_judgement_id argument);
cc_judgement_id cc_instr_sigma(cc_kernel *, cc_entry_id, cc_judgement_id family);
cc_judgement_id cc_instr_pair(cc_kernel *, cc_judgement_id type, cc_judgement_id first, cc_judgement_id second);
/* Γ ⊢ Π(x : A). B : U(l) or Σ(…) gives Γ ⊢ A : U(l), and B[a/x] : U(l). */
cc_judgement_id cc_instr_domain(cc_kernel *, cc_judgement_id type);
cc_judgement_id cc_instr_family(cc_kernel *, cc_judgement_id type, cc_judgement_id argument);
cc_judgement_id cc_instr_first(cc_kernel *, cc_judgement_id pair);
cc_judgement_id cc_instr_second(cc_kernel *, cc_judgement_id pair);
cc_judgement_id cc_instr_sum(cc_kernel *, cc_judgement_id left, cc_judgement_id right);
cc_judgement_id cc_instr_inject(cc_kernel *, cc_judgement_id type, cc_judgement_id value, bool right);
cc_judgement_id cc_instr_sum_elim(cc_kernel *, cc_judgement_id motive, cc_judgement_id left,
                                  cc_judgement_id right, cc_judgement_id value);
cc_judgement_id cc_instr_path(cc_kernel *, cc_entry_id dimension, cc_judgement_id family,
                              cc_judgement_id left, cc_judgement_id right);
cc_judgement_id cc_instr_path_lambda(cc_kernel *, cc_entry_id dimension, cc_judgement_id body);
/* At a dimension entry, or at endpoint 0 or 1 when the entry is 0. */
cc_judgement_id cc_instr_path_apply(cc_kernel *, cc_judgement_id path, cc_entry_id dimension, unsigned endpoint);
/* A closed typing judgement becomes a definition; the result is its lookup. */
cc_judgement_id cc_instr_define(cc_kernel *, uint32_t symbol, cc_judgement_id closed);
cc_judgement_id cc_instr_lookup(cc_kernel *, cc_term reference);         /* ⊢ d : T */
/* Equalities. Side 0 is the left term, side 1 the right. A position is the
 * path of child indices from that side's root to the highlighted subterm.
 * A step contracts the highlighted redex by the named rule. A replacement
 * swaps a highlighted occurrence of a for b, given a ≡ b; when a or b uses
 * a name bound on the way down, the given equality must have that name as a
 * context entry of the binder's type, and the entry is discharged. */
cc_judgement_id cc_instr_refl(cc_kernel *, cc_judgement_id typing);      /* t ≡ t : T */
cc_judgement_id cc_instr_step(cc_kernel *, cc_judgement_id equality, unsigned side,
                              const uint8_t *position, size_t depth, cc_step_rule);
cc_judgement_id cc_instr_replace(cc_kernel *, cc_judgement_id equality, unsigned side,
                                 const uint8_t *position, size_t depth, cc_judgement_id by);
/* t : T for a Π, Σ or path type T gives t ≡ its eta expansion : T. */
cc_judgement_id cc_instr_eta(cc_kernel *, cc_judgement_id typing);
cc_judgement_id cc_instr_side(cc_kernel *, cc_judgement_id equality, unsigned side); /* a : T */
cc_judgement_id cc_instr_symmetry(cc_kernel *, cc_judgement_id equality);
cc_judgement_id cc_instr_transitivity(cc_kernel *, cc_judgement_id first, cc_judgement_id second);
/* t : A and A ≡ B : U(i) give t : B. Lift raises t : A to a cumulative B. */
cc_judgement_id cc_instr_convert(cc_kernel *, cc_judgement_id typing, cc_judgement_id equality);
cc_judgement_id cc_instr_lift(cc_kernel *, cc_judgement_id typing, cc_judgement_id type);

/* Reading the store. Kind 1 is typing and 2 equality; for typing, other is 0. */
bool cc_kernel_fact(const cc_kernel *, cc_judgement_id, uint32_t *kind, cc_term *term,
                    cc_term *other, cc_term *type);
/* The index-th entry of a judgement's context, in creation order, or 0. */
cc_entry_id cc_kernel_fact_context(const cc_kernel *, cc_judgement_id, size_t index);
bool cc_kernel_entry(const cc_kernel *, cc_entry_id, uint32_t *symbol, cc_term *type, bool *dimension);

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
