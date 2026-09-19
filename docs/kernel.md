# Reading the kernel as inference rules

The kernel checks a derivation one inference at a time. A successful instruction
adds a judgement of the form **Γ ⊢ t : A**: under assumptions Γ, the expression
t has type A. A proof is an expression, and its proposition is its type.
MathScript chooses and submits these instructions; the C kernel checks them.

This guide is for a reader who knows dependent types but does not regularly
write C. It describes the current implementation, including its unusual binding
convention. It is a reading aid, not an independent proof of soundness.

## Where to start

1. Read the short `PiElim` case in [rules.c](../src/kernel/rules.c): it is
   dependent function application.
2. Follow `PiIntro` and the worked example below to see an assumption become a
   bound variable.
3. Read [contexts.c](../src/kernel/contexts.c) to see why an assumption cannot
   be discharged while another surviving assumption still needs it.
4. Read `NatElim` and `EqElim` in
   [eliminators.c](../src/kernel/eliminators.c): check both the motive and each
   branch's type, not just the shape of the expression being eliminated.
5. Follow [apply.c](../src/kernel/apply.c), which validates inputs and publishes
   the conclusion only after the rule and context checks succeed.
6. Review [ast.c](../src/kernel/ast.c) and
   [store.c](../src/kernel/store.c) for substitution and exact syntax identity.
   These are part of the trusted code too.

The [implementation review guide](../src/kernel/README.md) gives file-by-file
responsibilities, storage invariants, and validation commands.

## Enough C to read a rule

| C spelling | Read it as |
|---|---|
| `tt_id` | An integer handle into one engine's tables |
| `e->nodes[id]` | The expression node named by `id` in engine `e` |
| `j[i].expr`, `EXPR(i)` | The expression of premise i |
| `j[i].type`, `TYPE(i)` | The type of premise i |
| `r->expr = ...`, `r->type = ...` | Set the proposed conclusion's expression and type |
| `n.kind` | The constructor at the root of an expression |
| `n.ch[0]`, `n.ch[1]` | Its first and second children; numbering starts at zero |
| `REQUIRE(P)` | Reject this inference unless condition P holds |
| `a == b` | Exact equality of the stored handles |
| `P && Q`, `P \|\| Q`, `!P` | And, or, not |
| `P ? a : b` | a if P holds, otherwise b |
| `make2(e, N_Pi, A, B)` | Store/reuse the syntax node Π(A,B), returning its ID |
| `&x`, `*p` | Address of x; value at address p (used to return results) |
| `return false` | The proposed rule does not apply |

`REQUIRE` remains active in optimized builds. It is not the C `assert` macro,
which a build can disable. Constructing a syntax node with `make2` does **not**
by itself certify a judgement. Only the checked publication path does that.

Contexts, judgements, and expression nodes live in different tables. A context
ID and an expression ID with the same numerical value do not denote the same
thing. Zero means absent/failure; natural-number zero is a nonzero ID for an
`N_ZN` node. Names such as `NatForm` are opcodes (inference instructions), whereas
`N_Nat` is a constructor in the syntax produced by those instructions.

For example, `PiElim` reads:

```text
Γ ⊢ f : Π(x:A). B(x)     Δ ⊢ a : A
----------------------------------
Γ ∪ Δ ⊢ f(a) : B(a)
```

Its first `REQUIRE` checks that the function's type is a Π and that its domain
is exactly the argument's type. `make2(N_Ap, ...)` constructs the application.
`instantiate` substitutes the argument into the codomain. The surrounding
`tt_apply` computes the union of assumptions; the individual case need not
repeat that operation. A definitionally equal but differently stored argument
type first needs explicit conversion instructions.

## What the nodes mean

The `N_` prefix marks a node kind, not an extra mathematical operation.
Constructor order is fixed in [internal.h](../src/kernel/internal.h).

| Node | Mathematical reading |
|---|---|
| `U(i)` | Universe Uᵢ; `UUOmega`, `UUKappa` are the port's additional universe constructors |
| `CRef(c)`, `UCRef(c)` | An open context variable; the latter is a universe variable |
| `VRef(i)` | A bound-variable index, subject to the convention below |
| `DRef(j)` | A named definition backed by checked judgement j |
| `Axiom(j)` | An explicitly assumed inhabitant of the closed type in judgement j |
| `Pi(A,B)`, `Lambda(t)`, `Ap(f,a)` | Π(x:A).B(x), λx.t, f(a) |
| `Sigma(A,B)`, `Tuple(a,b)` | Σ(x:A).B(x), (a,b) |
| `Sum(A,B)`, `Inl(a)`, `Inr(b)` | A+B, its left injection, its right injection |
| `Eq(A,a,b)`, `Refl(a)` | Identity type a =ₐ b, its reflexivity constructor |
| `Void`, `Unit`, `Singleton` | Empty type, unit type, the point of unit |
| `Nat`, `ZN`, `SN(n)` | Natural numbers, zero, successor |
| `W(A,B)`, `WSup(a,f)` | Well-founded trees with labels a:A and children indexed by B(a) |
| `Susp(A)`, `North(A)`, `South(A)`, `Merid(A,a)` | Suspension, its poles, and its A-indexed meridian paths |
| `IndNat`, `IndSigma`, `IndSum`, `IndEq`, `IndVoid`, `IndUnit`, `IndW`, `IndSusp` | Checked eliminators; their types are determined by their rule premises |
| `SuspBeta` | The propositional meridian computation witness for suspension |
| `DefEq(t,u)` | A special checked definitional-equality judgement, with a common type stored separately |

Some type information is deliberately absent from term nodes. A `Lambda` stores
its body but not its domain; an `IndNat` stores its zero branch, step branch,
and input but not its motive. The checked judgement and its premises supply
that information. Reading an isolated node is therefore insufficient to audit
its type.

For eliminators the stored children, in order, are:

| Node | Children |
|---|---|
| `IndVoid` | input |
| `IndUnit` | point branch, input |
| `IndSigma` | pair branch (two bound variables), input |
| `IndSum` | left branch, right branch, input |
| `IndEq` | reflexive branch, first endpoint, second endpoint, path |
| `IndNat` | zero branch, successor branch (predecessor and induction hypothesis), input |
| `IndW` | branch (label and child function), input |
| `IndSusp` | motive, north value, south value, a private pair (meridian coherence, input) |
| `SuspBeta` | motive, north value, south value, a private pair (meridian coherence, meridian index) |

`N_Set` and `N_Path` are internal bookkeeping: a dependency list and a route
through syntax children. `N_Path` is **not** a HoTT path. `N_Temp` supplies
private symbolic placeholders for comparing dependent premises; it has no
public introduction rule.

## A complete example: the identity on the unit type

These are the mathematical steps:

| Instruction | Checked result |
|---|---|
| `UnitForm` | ⊢ Unit : U₀ |
| `CtxExt` using Unit | Allocate the assumption x : Unit |
| `Vble` using that context | x : Unit ⊢ x : Unit |
| `PiIntro` using Unit and x, discharging x | ⊢ λx.x : Π(x:Unit).Unit |
| `PiForm` using Unit twice, with no dependent variable | ⊢ Π(x:Unit).Unit : U₀ |

The following complete C program submits exactly those steps through the public
API. A failed step exits with a nonzero status; it cannot silently continue.

```c
#include "thth.h"

int main(void) {
    tt_engine *engine = tt_new(NULL);
    if (!engine)
        return 1;
    tt_id unit = 0, context = 0, variable = 0, identity = 0, function_type = 0;
    tt_id absent = 0;
    int failed = 1;

    if (tt_apply(engine, TT_UnitForm, NULL, 0, 0, NULL, 0, &unit) != TT_OK)
        goto done;
    if (tt_apply(engine, TT_CtxExt, &unit, 1, 0, &absent, 1, &context) != TT_OK)
        goto done;
    if (tt_apply(engine, TT_Vble, NULL, 0, context, NULL, 0, &variable) != TT_OK)
        goto done;
    tt_id intro_premises[] = {unit, variable};
    if (tt_apply(engine, TT_PiIntro, intro_premises, 2, 0, &context, 1, &identity) != TT_OK)
        goto done;
    tt_id formation_premises[] = {unit, unit};
    if (tt_apply(engine, TT_PiForm, formation_premises, 2, 0, &absent, 1,
                 &function_type) != TT_OK)
        goto done;

    failed = !tt_verify(engine, function_type, identity);
done:
    tt_free(engine);
    return failed;
}
```

Save the block as `/tmp/kernel-identity.c`, then, from the repository root:

```sh
make build/libthth.a
cc -std=c11 -Iinclude /tmp/kernel-identity.c build/libthth.a -o /tmp/kernel-identity
/tmp/kernel-identity
```

In `PiIntro`, `bind_ctx` replaces the reference to x by `VRef(0)`. The stored
expression is `Lambda(VRef(0))`. The result has no remaining assumptions.
`tt_verify` compares two already checked, closed judgements; it does not rerun
their derivations or reconstruct a type from arbitrary untrusted syntax.

## Contexts and the side conditions on abstraction

A context record represents one assumption, such as x:A. It stores A and the
assumptions needed to form A. A judgement stores its finite set of assumptions,
including dependencies. These are canonical lists of context IDs, not a
user-written ordered telescope. In particular, a record for x:A can refer to
the earlier record for A:U₀ through its dependency set.

To introduce a function, an open assumption is **discharged**: its occurrences
become bound variables, and it is removed from the relevant premise's context.
But from `A:U₀, x:A ⊢ x:A`, abstracting A while leaving x open is illegal:
the surviving assumption x:A still refers to A. Abstract x first.

The details are part of each opcode's metadata, not guesses based on variable
names. Read `free_contexts` as the number of *discharge slots*. A zero in such
a slot means the corresponding variable was unused/absent; it does not bypass
the remaining type checks.

For `PiIntro`, `pop_judgements = {2}`. The number 2 is binary `10`: discharge
slot 0 from premise 1 (the body), but not premise 0 (the domain).

For `SigmaElim`, the slots are `[z:Σ(x:A).B(x), x:A, y:B(x)]` and the masks
are `{1,2,2}`. Thus z is discharged from the motive, and x and y from the pair
branch. `allowed_free_contexts = {0,0,2}` permits y to depend on x while both
are discharged together. Each integer is a finite subset represented by bits:
`mask & (1u << i)` means “does this subset contain i?”

`check_contexts` rejects forbidden dependencies before any conclusion is
published. `output_context` then takes the union of premise assumptions after
the permitted removals. Dropping all discharge slots from every premise would
be a different, unjustified rule.

`CtxExt` reuses an identical assumption record unless a preceding context is
supplied to advance its counter. This lets callers distinguish two variables
of the same type. That counter is an identity discriminator, not a bound index.

## Three different equalities

**Structural identity** means exactly the same stored syntax. Nodes are
interned: constructor, payload, and children determine an ID. A hash locates
candidates, but full field comparison decides whether to reuse an ID. Even a
hash collision cannot establish equality between different syntax trees.

**Definitional equality** is explicitly represented by `DefEq(t,u)` with its
common type in the judgement. Computation and definition rules produce these
judgements; `Subs` and `HighSubs` use them to rewrite. `DefEqExtL/R` recover
either side with that type. Ordinary premise matching does not secretly run a
normalizer until two types agree.

**Identity equality** is the type `Eq(A,a,b)`. An inhabitant is a path, and
`EqElim` is path induction. Such a path is not automatically a definitional
equality. There is no equality-reflection instruction that permits rewriting
the kernel's syntax merely because a path exists.

Univalence, function extensionality, truncation, excluded middle, and choice
are not implicit consequences of these C equality checks. When a library
development uses an explicit axiom, its derivation is relative to that axiom.
`Axiom` requires configuration opt-in and a checked **closed** type. `Def`
instead names an already checked closed expression; it does not assume a new
inhabitant of an arbitrary type.

## Substitution and the binding convention

While constructing a proof, open variables use context references. Closing
an abstraction changes them to numerical `VRef` indices. In an ordinary nested
lambda, index 0 names the nearest binder, index 1 the next outer binder, and
so on. For example, λx.λy.x has body `VRef(1)` beneath the two lambdas.

This kernel inherits an unusual **node-wide** depth convention. During a
traversal, a constructor contributes the following depth increment to **every**
child, including children which mathematical notation would put outside the
binder's scope:

| Depth increment | Constructors |
|---|---|
| 1 | Lambda, Pi, Sigma, W, IndEq |
| 2 | IndNat, IndSigma, IndSum, IndW |
| 0 | All others |

For a concrete consequence, applying `bind_ctx` to replace A in the open term
`Lambda(Pi(CRef(A), CRef(A)))` at offset zero produces
`Lambda(Pi(VRef(2), VRef(2)))`, before the caller adds any outer binder.
Both Π children receive the same increment.
A textbook de Bruijn encoder would treat the domain differently. Here the
number is a traversal coordinate, not always a count of visible binders in
the displayed mathematics. The rule that builds a binder first closes its
body/family at depth zero, then constructs the binder node.

`transform` performs several deliberately distinct operations:

| Mode | Purpose |
|---|---|
| `MAP_CONTEXT` | Replace specified open context references simultaneously |
| `MAP_BIND` | Close specified contexts, using traversal depth plus a binder offset |
| `MAP_INSTANTIATE` | Substitute the selected index in a dependent family |
| `MAP_SHIFT` | Adjust indices at or above a cutoff when moving a term across levels |
| `MAP_BETA_SUBST` | Substitute for removed binders and lower indices above them |
| `MAP_REPLACE` | Replace a structurally matching subtree, for checked definitional rewriting |
| `MAP_W_MOTIVE` | Specialize a W motive at a child application under a fresh binder |

Simultaneous substitution does not substitute again inside a replacement during
that same operation. This matters when the two replacements mention each
other's contexts. Instantiating a family and eliminating a lambda binder are
different operations here; do not merge them based only on their mathematical
informal description.

The negative shifts in eliminator computation compensate for virtual levels.
For natural-number induction, the predecessor leaves the eliminator's two
levels, but the recursively constructed induction term retains them. The tests
in `recursive_binding` compare reduction before and after closing an external
assumption; testing only closed numerals would miss variable capture.

`reduce` makes one bottom-up pass and reduces each visited root once. It does
not loop until a normal form is reached. Further computation can require
another checked reduction instruction. The `defs` parameter decides whether
definition references may unfold; `recursive` decides whether to visit the
children or just the selected root.

## Reviewing dependent elimination

For `NatElim`, take a family C(n), a base case z:C(0), and a step
`s:C(succ(k))` under `k:Nat, h:C(k)`. The result at n is in C(n). In the C
case, find these checks separately: the base type, the induction hypothesis
type C(k), and the step type C(succ(k)). The last two are not interchangeable.
Its computation rule is `ind(z,s,succ(n)) ≡ s(n,ind(z,s,n))`.

For `EqElim`, the family is C(x,y,p), and the reflexive branch has type
C(z,z,refl(z)). The code compares these after simultaneous substitution using
a private placeholder. Its computation at reflexivity returns that branch.

For `WElim`, a branch receives a label a, a child function f:B(a)→W(A,B),
and a recursive result for **each** child: Π(b:B(a)).C(f(b)). Its result must
have type C(sup(a,f)). Look for `recursive_motive` and `expected` in the rule;
the `WComp` case constructs the recursive function supplied to the branch.

[suspension.c](../src/kernel/suspension.c) adds a native higher inductive type.
For C:Susp(A)→U, its data are n:C(north), s:C(south), and

```text
h : Π(a:A). transport(C, merid(a), n) = s.
```

The code checks these endpoints and fibers before constructing a section.
Computation at north and south is definitional. Computation along a meridian
is a path supplied by `SuspMeridComp`; it is not an instruction to collapse
all paths. `Transport` and `Apd` build existing identity-eliminator terms and
add no new axioms. Suspension itself is an extension of the primitive calculus,
so its rules belong in a foundational review even though they are not labelled
`Axiom` in a proof's dependency list.

## What an audit must trust, and what tests establish

The trusted implementation includes the rule checks, context metadata and
discharge, binding/substitution, reduction, exact interning, caches, and
publication. The C compiler, memory allocator/runtime, and execution environment
also matter. File boundaries are an aid to review, not a memory sandbox: code
including the private header can modify the engine. Public clients should use
only [thth.h](../include/thth.h).

MathScript, proof generators, the workbench, and rendering code propose
inferences or display results. They do not authorize a new inference rule. A
folded mathematical display is useful for inspection, but its text alone is
not the certificate. Review the checked terms and derivation/dependencies when
auditing a proof.

Accepted nodes are immutable. Repeated syntax shares storage, and caches reuse
results only for matching complete keys. Copies of nodes and premises survive
arena growth: holding a raw pointer into an arena across `realloc` would be
unsafe. On a rejected instruction, temporary nodes are rolled back and the
transformation-cache generation changes before those IDs can be reused.
These details are performance mechanisms with correctness obligations, not
additional mathematical rules.

Useful focused checks, without recompiling the entire MathScript library:

```sh
make test collision-test
python3 tools/check_reference.py
make lint
```

Native tests exercise all implemented opcodes, dependent motives, invalid
inputs, binding regressions, resource bounds, cache equivalence, and suspension.
The collision configuration forces all interning hashes to zero. The reference
check compares a frozen independently replayed inference trace; see
[compatibility.md](compatibility.md) for its provenance and exact scope.
These checks catch regressions; they do not prove semantic soundness,
normalization, consistency, or completeness of the implemented calculus.
