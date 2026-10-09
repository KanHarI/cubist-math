# TODO: PR #188 review findings and failures shared with main

Reviewed on 2026-10-09 against main `cb525f07796348d8bc806cd8cda11663a6544f0e`
and PR #188 head `68f1bf35d82a9a7065c4a42a25671212418ed888`, with the same
WASM kernel. The first part lists defects this PR introduces, to fix in it.
The second part lists failures reproduced on both revisions: they are
follow-up work, not regressions attributed to this PR, and are not fixed
here. No fixes for these shared failures are included in the PR review follow-up.

At the reviewed PR head, `npm test -- --test-concurrency=4` passed (735/735)
in a fresh worktree. The review follow-up passes 741/741 tests, including six
new tests, and passes the site build, browser checks, Cubist lint,
diagnostic-code checks and `git diff --check`. The five tests demonstrating
the reported regressions fail at `68f1bf35`; the additional negative test
guards against treating a captured data type as a proposition. The final
expanded cases also pass separately, covering absent caller notation,
public header-label collisions and ordinary E514 errors.

# Introduced by PR #188

## Inlined proposition helpers lose proposition classification

- [x] Recognize a declared proposition by its captured identity after
  inlining a derived operation.

```cubist
import hlevels;
inductive P : prop U0 { proof_point; }
theory T(U < UU0) {
  M : set U;
  def Q(a : Unit) : U0 := P;
  law ok : Q(tt);
}
```

This checks on main but fails at `68f1bf35` with E818. The same regression
affects helpers returning `Trunc`. The fix recognizes `reference` nodes by
their binding, without resolving their display spelling again. Tests cover
both forms, inheritance after rebinding `P`, and the rejection of a captured
data type even when its spelling is rebound to a proposition.

## Inherited operator operands are re-read in the child's notation

- [x] Keep an inherited operator's operands in the parent's notation.

```cubist
import hlevels;
import nat;
use nat;
theory P(U < UU0) { M : set U; point(n : Nat) : M; law base : point(0 + 0) = point(0); }
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory Q(U < UU0) extends P {}
initial N : Q(U0);
```

On the PR, `Q`'s model type and `N`, `N.model` and `N.fold` are accepted with
the law `point(nat.(1 + 1)) = point(0)`, which nobody wrote: `+` is read in
`nat`, but its operands in `shifted`. The only errors are `Q.p` (E606, `found
m.point(nat.(1 + 1)) = m.point(0), expected m.point(nat.(0 + 0)) =
m.point(0)`) and `Q.Hom.p` (E391). Across modules the same law fails at the
child: with `P` imported from a module that uses `nat`, a child in a module with
no selection is refused (`0 means the natural number in a selected notation
that reads it`).

Main also rejects this source (E397, `+ is not in shifted's notation`), but it
never accepts the re-read law. That acceptance, and the initial model built
from it, are new.

Cause: `capturedTheorySyntax` (`web/translator/theories.mjs:338-342`) marks a
binary operator with `lexicalNotation` by replacing the node, and `rewritten`
does not enter a replaced node, so the operands stay unmarked. That is
correct in the parent, where the operator's scope covers its operands. A
child's capture then meets the already-marked operator at line 338, returns it
unchanged, and so enters it, stamping the unmarked operands with the child's
notation.

Checked fix: return a copy at line 338, `if(n.lexicalNotation)return {...n};`,
so marked subtrees are not entered, as `select` already does. With it, the
same-module source above, the cross-module case and the plain-numeral
inheritance case all check, and `tests/theory-resolution`, `initial-models`,
`theories` and `references` pass (81/81). The review follow-up implements this
fix and adds regression tests for a same-module child under another
selection, and cross-module children with another selection or no selection.
They check both operator expressions and plain numerals, the inherited law
in initial/free models, and parent model/homomorphism projections.

## A shadowed theory name gives a misleading E374

- [x] Refuse an initial/free header whose theory name now names something
  else, with the header's own spelling.

```cubist
import hlevels;
import algebra;
import nat;
def Monoid : Nat := zero;
initial N : Monoid(U0);
```

This gives E374 at the header: `Monoid has no named parameters: a named
argument gives a parameter that a definition declares.` The source has no
named argument. `initial-models.mjs:32` and `:39` accept the head through the
theory namespace (`theoryBinding(head.name)`), which the def does not replace.
Line 90 then rewrites the positional arguments as named ones and elaborates
`head.name`, which is the def.

Expected: E850 (`Monoid is none`), or a hiding message as in E862. Ordinary
uses of a shadowed theory (`def m : Monoid(U0) := …`) already fail with E352.
The fix checks that the current binding is the retained theory's model type
before expanding arguments. Positional and named initial/free applications
now receive E850 at their written theory expression.

## Minor

- [x] E514 names a binder the expansion generated. `free W(A : U1) :
  Monoid(U0) on A;` reports `W.gen's argument a lives in a universe above W's
  declared one`. The source has no `a`: it is `v.a`
  (`initial-models.mjs:186`, `:195`). Name the generator type, or the header
  parameter, instead.
- [x] Headerless theories expose their generated universe as a public
  argument label, and the label depends on internal binder names. The PR's
  own test needs `Numbered(U_1 := U0)` because an operation binds `U`, and
  E868 asks a child to bind `U_1`. Renaming that operation binder changes
  the label callers must write. Consider a stable name, or no named access.
- [ ] Checking `import hlevels; import algebra;` is about 9% slower (six runs
  each, median about 1.10 s on main and 1.20 s on the PR). It is likely the
  whole-tree `elaborationSyntax` copy of every generated declaration plus the
  capture passes. This is not blocking.

Oversized generators now receive E870 at the expression after `on`, naming
the generator type; ordinary inductive data errors retain E514. Headerless
theories now record public universe labels separately from fresh internal
binders. The label is `U`, or the first available `U_1`, `U_2`, etc. when a
public term parameter already takes that name. Named applications,
constructors, projections, and inheritance use this stable label.

An additional interleaved measurement used two warm-up rounds and seven
measured rounds per revision, checking a fresh `CubicalProgram` with
`import algebra; def unit_type : U0 := Unit;`. Median times were 1,125 ms on
main, 1,186 ms at `68f1bf35`, and 1,183 ms with the review fixes. The fixes
did not materially change the PR's cost; this run measured about 5% overhead
relative to main. Timings depend on the machine and run. No performance fix
is claimed.

## Checked without findings

These cases check or give the intended refusal on the PR:

- models named after the carrier (`initial M : Monoid(U0)`), after an
  operation (`initial one`), or after a free parameter;
- a free parameter that shares a theory parameter's name;
- a function-valued theory parameter used in a law;
- a recursive derived operation in a law (E845);
- prop carriers, two header universes, `initial Z : CommRing(U0)`;
- imported theories with operator laws in initial models;
- parent-failure cascades into `initial` (E340);
- reserved `gen`/`model`/`fold`;
- generator universes above the carrier (E514 at the reviewed head; E870
  after the diagnostic fix).

The shared scope traversal's new `TypeError` for unregistered kinds is
reachable only from theory, notation-rule and generated syntax. Every kind
built there is registered.

# Shared by main and PR #188

## Recursive derived operations with a binder named after the theory

- [ ] Preserve recursive calls when a derived operation's parameter or match
  variable has the theory's name.

```cubist
import hlevels;
import nat;
theory T(U < UU0) {
  M : set U;
  c : M;
  op(x : M) : M;
  def iter(T : Nat) : M := match T {
    zero => c;
    succ(n) => op(iter(n));
  };
}
```

Main rejects `T.iter` with E862: `T` hides `T.M`. The PR rejects it
with E547, treating the recursive call as an unsupported self-reference.
The variant `iter(n : Nat)` with `succ(T) => op(iter(T))` also fails on
both: main reports that `T` hides `T.op`; the PR reports E547.
Track both variants when adding regression coverage.

## Homomorphism arguments depending on laws

- [ ] Detect unsupported dependencies on laws before generating invalid
  homomorphism and isomorphism declarations, and report a focused refusal.

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  c : M;
  law l : c = c;
  op(p : l = l) : M;
}
```

Both revisions reject `T.Hom` with E606:
`Type mismatch: found A.l = A.l, expected B.l = B.l`.
Dependent Hom/Iso declarations then produce E340 cascades. This is also
listed among the PR description's existing follow-ups.

## Homomorphism universes omit fixed operation argument types

- [ ] Account for the universes of fixed operation domains when assigning
  the universe of the generated homomorphism type.

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  op(A : U0, x : A) : M;
}
```

Both revisions reject `T.Hom` with E606:
`Type mismatch: found max(U, max(V, U1)), expected max(U, V)`.
The fixed domain `U0` raises the universe of the preservation field;
the generated Hom universe does not include it. Dependent Hom/Iso
declarations then produce E340 cascades.

## Nested matches in derived operations cannot find carrier evidence

- [ ] Investigate how a generated derived operation supplies its model's
  carrier evidence to automatic clauses for nested matches.

```cubist
import hlevels;
inductive Bit : set U0 { off; yes; }
inductive Bits : set U0 { nil; cons(b : Bit, rest : Bits); }
theory T(U < UU0) {
  M : set U;
  c : M;
  def value(n : Bits) : M := match n {
    nil => c;
    cons(off, rest) => c;
    cons(yes, rest) => c;
  };
}
```

Both revisions reject `T.value` with E546:
`Cannot generate Bit.squash: m.M must be of h-level 1; no local evidence,
hint or rule gives that`. The theory declares `M : set U`, but automatic
clause generation does not discover the model's evidence in this case.
An imported theory inherited by an otherwise empty child has the same
failure in both the parent and child's derived operation.

## Unused-binder advice removes theory morphism support

- [ ] Make unused-binder suggestions aware of named theory operation
  arguments, so the suggested rewrite preserves the generated interface.

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  op : forall x, y : M. M;
}
```

Both revisions' lint emits W706 for `x` and `y`, suggesting arrow form.
With `op : M -> M -> M`, both revisions reject a use of `T.Hom.id` with
E817 because no homomorphisms are generated. The single-quantifier form
also receives arrow advice (W705). The PR's initial/free construction
additionally requires named operation arguments and rejects arrow form
with E864. The W706 issue is already mentioned in the PR description.

## A def and an inductive may share a name

- [ ] Refuse a second declaration of a name when one is a def and the other
  an inductive (or an initial/free model).

```cubist
def N : Unit := tt;
inductive N : U0 { c; }
def t : N := N.c;
def u : Unit := N;
```

Both revisions accept `N` twice without a duplicate-declaration error. The
outputs list `N` once, `t` fails with E343 (`Untranslated name: N.c`), and `u`
with E606 (`found U0, expected Unit`): the inductive silently replaced the def.
Two defs or two inductives of one name are refused with E604. On the PR,
`def N : Unit := tt; initial N : Monoid(U0);` is accepted the same way.

## A child of a failed parent theory repeats the parent's error

- [ ] Report a child theory of a failed parent as an untranslated dependency.

```cubist
import hlevels;
theory P(U < UU0) {
  M : set U;
  e : M;
  law bad : e = Undefined;
}
theory C(U < UU0) extends P {
  law again : e = e;
}
```

Both revisions report `P` with E343 (`Untranslated name: Undefined`) and
then the same E343 again at `C`, instead of E340 `Untranslated dependency: P`.

## A failed parent projection makes `Hom.p` report E391

- [ ] When a child's parent projection fails, report its `Hom.p` as an
  untranslated dependency.

```cubist
import hlevels;
import nat;
use nat;
theory P(U < UU0) { M : set U; point(n : Nat) : M; law base : point(0) = point(0); }
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory Q(U < UU0) extends P {}
```

On main, `Q.p` fails with E606 because the inherited numeral is read in
`shifted`; the PR fixes that trigger, but reaches the same state through
inherited operator operands (`point(0 + 0)`). In both cases, once `Q.p`
fails, `Q.Hom.p` reports E391 (`Nothing determines the universe U of
P.Hom`) instead of E340 `Untranslated dependency: Q.p`.
