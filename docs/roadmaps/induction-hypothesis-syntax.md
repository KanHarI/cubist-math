# Separate induction hypotheses from constructor fields

Decision adopted on 2026-10-11. Status: specified, not implemented or
scheduled. The [work plan](work-plan.md) owns scheduling; this document
specifies a surface-language change to the existing induction mechanism.

## Decision

An induction clause names constructor fields inside the constructor pattern
and names induction hypotheses separately, after `with`:

```cubist
node(a, children) with ih => ...
branch(left, right) with ih_left, ih_right => ...
```

These are proposed clause headers, not syntax the current parser accepts.
The current spelling of the first header is `node(a, children, ih) => ...`.
It mixes stored constructor fields with results supplied by induction,
making a two-field constructor appear to have three fields.

With the adopted spelling, `node(a, children)` has the same fields in
`match` and `induction`. The `with` clause names the additional induction
results. Hypothesis names are chosen by the author; `ih` is a convention,
not a keyword.

## Syntax and binding contract

The planned clause header is:

```text
constructor(fields) [@ coordinate ...] [with hypothesis, ...] => body
```

Here brackets describe optional syntax, and a nullary constructor keeps
its existing spelling without parentheses. The existing expression and
proof-block forms of `body` both support the new header.

- The constructor pattern binds exactly its declared fields, in their
  declared order. Path-constructor coordinates keep their existing `@`
  spelling and precede `with`.
- There is one hypothesis for each recursive field, in the order of those
  fields. Ordinary data fields contribute no hypotheses. This does not
  mean that the hypothesis is always a third parameter.
- A direct recursive field `child : Tree` supplies a result of type
  `P(child)`, for the induction motive `P`.
- A recursive field `children : B(a) -> Tree` supplies a function of type
  `forall b : B(a). P(children(b))`. There is one hypothesis for the
  whole field, not a separate binder for each child. More general accepted
  recursive field shapes retain their current generated result types.
- Omitting `with` leaves every hypothesis unnamed, as omitting the appended
  names does today. If `with` is present, it names all the recursive-field
  results. An empty list, a wrong count, or hypotheses on a constructor
  with no recursive fields is an error.
- `with` hypotheses are available only in an `induction` clause. A plain
  `match` clause does not accept them. Existing structural recursive calls
  in recursive definitions keep their behavior.
- Fields, coordinates and hypotheses bind in the clause body under the
  existing name and scope rules. Hypotheses are not extra constructor
  arguments when constructing or inspecting a value.

`with` is already reserved. Its role in a clause header is separate from
the existing `with unfolding [...] { ... }` expression in a clause body.
The specialized natural-number induction syntax remains unchanged; this
decision concerns constructor clause headers.

## Tree example and the empty case

The Russell proof uses this existing declaration:

```cubist
inductive Tree(U < UU0, A : U, B : A -> U) : U {
  node(a : A, children : B(a) -> Tree(U, A, B));
}
```

For an arbitrary motive `P`, the node case receives:

```text
a        : A
children : B(a) -> Tree(U, A, B)
ih       : forall b : B(a). P(children(b))
goal     : P(node(a, children))
```

For `no_self_member`, take
`P(t) := member(U, A, B, t, t) -> Void`. Then `ih(b)` says that child
`children(b)` cannot be its own immediate child. The planned header in
that proof is `node(a, children) with ih => ...`; its motive and proof
body retain the same mathematical meaning.

A leaf is a node whose child-index type `B(a)` is empty. That type need
not be literally or definitionally `Void`: evidence `B(a) -> Void` is
enough. When `B(a)` is `Void`, the following schematic definitions make
the vacuity explicit, with their displayed types supplying the expected
result type for `absurd`:

```text
children : Void -> Tree(U, A, B)
children := fun (b : Void) => absurd(b)

ih : forall b : Void. P(children(b))
ih := fun (b : Void) => absurd(b)
```

The eliminator does not test whether `B(a)` is empty or insert an
`absurd` expression as a special leaf rule. Its uniform computation rule
supplies `ih(b)` by applying the same induction to `children(b)`. At a
leaf there is no child index at which to apply that function. Describing
the hypothesis by empty elimination is logically valid without claiming
that this is the generated term's literal syntax or a definitional
equality between the two presentations.

## Implementation and migration

1. Parse the `with` list into a separate hypothesis-binder field on the
   clause AST. Preserve token locations for diagnostics and inspection.
   The constructor's argument list must contain only constructor fields.
2. Update clause elaboration in `web/translator/match.mjs` to bind these
   names to the existing recursive results. Keep the same motive,
   eliminator, clause ordering and kernel computation rules. No kernel
   extension or new proof principle is involved.
3. Update the formatter, scope analysis, source inspection and generated
   proof output to preserve or emit the separate list. Audit consumers
   that currently infer the field/hypothesis split from argument count.
4. Add a migration from appended hypothesis names to `with`. Initially
   accept the old spelling for compatibility, while emitting and
   documenting the new one. Reject a clause that combines both spellings.
   Any eventual removal of the old spelling is a separate decision.
5. Migrate the maintained library, including `universe_smallness`, and
   update the induction chapter, quick reference and arity diagnostics.
   Historical snapshots remain historical unless explicitly migrated.

## Acceptance evidence

- Check expression and proof-block clauses with zero, one and multiple
  recursive fields, including fields interleaved with ordinary data.
- Check function-valued recursive fields, the empty child-index case and
  existing supported path-constructor cases. Preserve coordinate binding.
- Verify omitted hypotheses, binder scope, formatter round trips and
  migration of nested clauses and comments.
- Reject wrong field/hypothesis counts, `with` on plain `match`, mixed old
  and new binders, and attempts to pass hypotheses as constructor fields.
- Compare canonical elaborated kernel terms before and after migration;
  the syntax change must preserve proof terms and axiom dependencies.
- Check the Russell proof and existing induction/reference regressions.

The document records the decision only. None of these implementation
steps is claimed complete by adding this roadmap.
