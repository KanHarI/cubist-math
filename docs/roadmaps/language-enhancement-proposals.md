# Language enhancement proposals

Status: proposals, not scheduled. Each records a language feature that was
considered and deferred, why it was deferred, and what would justify taking
it up. None belongs to a roadmap milestone until a use case appears. Taking
one up means specifying it in the owning roadmap first, with its own review.

| ID | Proposal | Origin | Owner when taken up |
| --- | --- | --- | --- |
| E1 | Level constraints between universe variables | G0 question Q7 | Kernel G0 |
| E2 | Generic definitions and builtins at tier 1 | G0 question Q10 | Kernel G0 |

## E1. Level constraints

**Idea.** Let a declaration state constraints between its universe
variables, such as `U` strictly below `V`, as Coq allows. The kernel would
then check the declaration under those constraints, and each instantiation
would have to satisfy them.

**Why deferred.** Unconstrained universe variables with `max` and `next`
express every signature we know of: `Group(U) : next(U)`, quotients at
`max(U, V)`, and the H design's examples. A universe binder's bound, as in
`U < UU0`, is not a constraint between variables. Constraints would bring
in a constraint problem with loop checking (Bezem–Coquand) in both checkers,
and level comparison would become relative to a constraint set.

**What would justify it.** A signature or theorem whose universe levels
cannot be written with `max` and `next` alone, without an unwanted increase
in level.

**Reference.** [G0 specification](g0-universe-specification.md), Q7.

## E2. Generic definitions and builtins at tier 1

**Idea.** Let results about types in `UU0` use generic definitions, in two
steps:

1. The computing builtins (`ua`, `UnivalenceBeta`, `FunExt`) accept a
   universe argument of tier 1 or above, such as `ua(UU0, A, B, e)`. The
   elaborator builds the same closed body at that constant level. It checks
   by the same kernel rules and computes, and it is not a template.
2. Binders `V < UUU0`, whose variable ranges over every `U_n` and `UU_n`, so
   that one definition serves both tiers. Section 1.5 of the G0
   specification describes what this needs: variables that carry their
   bound, a bound-aware order test, and a model over the ordinal ω·2.

**Why deferred.** No result needs it yet. Generic statements already live in
`UU0` and can be named, paired and compared. Only reasoning about types in
`UU0` themselves, for example equivalences between generic statements, needs
generic definitions at tier 1. In this version a universe argument of tier 1
or above is rejected, including by the builtins. `LEM`, `Choice` and
`Truncate` stay below `UU0` by decision, independently of this proposal.

**What would justify it.** A library result that needs univalence,
function extensionality or a generic library definition at a type in `UU0`.
Step 1 is enough for a result that needs only the builtins. Step 2 is needed
when a library definition must serve both tiers.

**Reference.** [G0 specification](g0-universe-specification.md), section 1.5
and Q10.
