# One-sort signatures (H1): rules, soundness note and truncation policy

Status: draft for review; not implemented. Written on 2026-09-27 as work-plan
items K2.1 (the H1 fragment and its soundness note) and K2.5 (G2's truncation
and resizing policy, with its migration ledger). It is the contract that K2.2
(instructions), K2.3 (driver and bridges), K2.4 (differential fixtures) and
L2.1 (the `inductive` declaration) implement. Default admission and release
wait for review of section 4. Until then, H1 runs only in the experimental
mode of section 5.7, and its results carry the `kernel extension: H1` marker.

It refines the adopted
[higher inductive-inductive type design](higher-inductive-types-design.md)
for its first stage. It keeps the level rules of the
[G0 specification](historical/g0-universe-specification.md), and revisits two
of G0's statements about declared types: the level-abstracted constants of
its section 2.12, and Q1's distinct instances. The
[work plan](work-plan.md) schedules the packages. Where this document narrows
or departs from the design or from G0, section 0 says so and section 11 asks
for a decision.

## Revisions after review

A review of the first draft (PR #53) found one blocking and four further
defects. This version corrects them:

- **Level-erased instances** (2.3, 3.1, 5.3, 7.2). The native formers carry
  no level, and the archive relies on it: a generic definition instantiated
  at `U1` accepts a sum built at `U0`. Level-abstracted declared constants
  could not translate that. Instances of a declared sort now carry no level,
  and H1 admits only level-parametric signatures, where this is sound (D9).
- **Path abstraction in boundaries** (1.4). `S2`'s outer endpoints are
  `⟨j⟩ base`, which the first grammar could not generate.
- **Commit keeps signatures** (5.1). `cc_kernel_commit_checkpoint` keeps new
  definitions and relocates their syntax; admitted signatures are kept the
  same way. Only rollback removes them.
- **UU-tier arguments** (2.3, 7.2). Native formers accept them. The first
  revision let every level-parametric signature without a tier-1 constant
  read any tier; the second review narrowed that (below).
- **The ledger's remedies** (8.3, 8.4). Raising the tower's quantifier moves
  membership up a universe each time, and the same holds for the union of
  independent sets. Those remedies are replaced, and the Cauchy root is
  identified as an artifact of a wrapper's fixed universe.
- **Open obligations** (4.3, 4.5) are marked as such for D1, D4, D5 and
  Lemma H2.

A second review, of that revision, found one blocking and two further
defects:

- **Hidden tier bounds** (2.3, 3.1, 5.2, 5.3, D9, Q8, Q16). A signature can
  inherit a level bound from a signature or definition it uses, as `Outer`
  does from `Tag(A : UU0)`, without a tier-1 constant of its own. Instances
  now read finite levels, the range admission checked. That revision let a
  syntactically checked class of tier-parametric signatures read tier-1
  levels; the third review found a hole in the class (below).
- **Levels inside parameter terms** (2.4, D8, Lemma H2). Level substitution
  recurses through parameters, motives and clauses: `Trunc(U(x))` at `0` is
  `Trunc(U(0))`.
- **Propositions against witness types** (8.2, 8.4). `LEM` resizes
  propositions only. Group 7 needed no resizing at all, only double negation
  at `U1`, which a local check on the archive confirms. Groups 4 and 6 now
  name the propositions they resize and keep their witness types.

A third review found that the syntactic class of the second revision still
admitted a hidden bound, in the constructor of a parameter-free signature
(`Outer2` over `Big : UU1 { pack(B : UU0); }`). This version:

- **States the criterion semantically** (2.3): a signature reads tier-1
  levels only if its admission is derivable without the finiteness of its
  level parameters.
- **Checks the derivation, not the text.** Three rules on the recorded
  admission derivation, closed transitively over the signatures it uses,
  parameter-free ones included, implement the criterion. Their sufficiency
  is proved in outline by induction on the derivation; each instruction's
  classification into the proof's cases is a K2.2 review item.
- **Makes the extension optional** (Q16). The recommended first release has
  instances at finite levels only, and keeps the native sum, W and pushout
  instructions for tier-1 arguments, which no archive or library
  declaration uses today. Rejection fixture V19 covers the new
  counterexample.

A fourth review found two consistency defects, now fixed:

- **The walk's coverage** (2.3, 5.2). The closed former judgement ends in
  a prenex of `LevelPi` and `Pi`, in `U(ω)`, which rules 1 and 2 would
  reject. The walk now starts below that prenex, from the parameter types'
  judgements, `U(ℓ)` and the constructor judgements, and still refuses
  level quantification within them.
- **τ's guarantees under the conservative option** (7.2–7.4). They hold
  for finite-tier declarations only. A mixed-tier call, such as
  `big_id(Nat, small)` with `big_id(A : UU0, x : A or A)`, has no image,
  and the migration verifier rejects it (fixture X8). No such call exists
  today.

## 0. Relation to the adopted design and to G0

The design fixes one signature format for H1–H4. For H1 this document makes
seven choices precise. Each is an open question in section 11 with a
recommendation.

| Design statement | H1 as specified here | Why |
| --- | --- | --- |
| One heterogeneous formal composition `fcomp` per sort, along a line of parameters and indices | Higher sorts get a formal homogeneous `hcomp` at fixed parameters; transport along a parameter line computes by recursion on its argument; general composition is `hcomp` after transport (Q1, Q2) | An eliminator's motive is over the sort at fixed parameters, so a formal element joining two parameter values could not be eliminated. This is Coquand–Huber–Mörtberg's split, which the kernel already implements for pushouts. |
| `fcomp` pushes through constructors of sorts without path constructors | Data sorts get no formal composition at all; composition pushes through equal constructor heads and is otherwise neutral (Q1) | A formal element that also pushes breaks confluence and stability under substitution. This is how the hand-coded `Nat`, sums and W types compute. |
| Boundaries may mention earlier constructors and formal compositions | Boundaries are constructor expressions: positions and earlier constructors at interval formulas, with no compositions (Q3) | Displayed boundaries then follow by substitution; every H1 example needs no more. |
| Boundaries are systems on faces of the constructor's dimensions | Boundaries are cube boundaries: a piece on both faces of every dimension (Q4) | A cube boundary is an iterated path type, which the kernel already has. Partial boundaries would need extension types. |
| Constructors take dimension arguments | A constructor with dimensions is a function into an iterated path type, applied at interval formulas by path application (Q5) | Boundary reduction is then the kernel's existing path step, and overlap agreement is typing. |
| A sort's level is the maximum of its data and arity levels | The former's type declares the level; the kernel checks that every constructor type lives in that universe, and the elaborator declares the least such level (Q7) | The instruction kernel does not infer principal levels. |
| G0 2.12: generated constants are level-abstracted, as `Trunc : Π (x < ω). Π (A : U(x)). U(x)`; G0 Q1: instances at different levels are distinct | Instances carry no level of their own. A sort instance, a constructor and an eliminator are one term at every universe, and the levels are read from the parameters' judgements, within the finite range admission checked. An extension lets tier-parametric signatures read every tier (Q16). H1 admits only level-parametric signatures, whose constructor types mention no level parameter (Q8, Q15, Q16) | The native formers are level-erased, and the archive relies on it (7.2). A sort built from its parameters alone does not depend on the universe it is viewed in (D9). |

Everything else follows the design: one signature format, positions as
cubes, generated squash constructors for `set` and `prop`, clause typing
through the partial eliminator, computation on every constructor and on
formal compositions, and staged trust.

## Decisions in brief

- **Fragment.** One sort, uniform parameters (level and term), no indices.
  Constructors are checked in order. Each takes data, then positions, and has
  zero or more dimensions with a cube boundary. The sort is `type`, `set` or
  `prop`; the last two append generated squash constructors.
- **Constructors are path-valued.** A constructor with `d` dimensions has a
  `d`-fold iterated path type whose endpoints are its boundary. It is applied
  at dimensions by path application. At an endpoint it reduces to its
  boundary by the existing path step.
- **Admission reuses ordinary instructions.** A constructor's type is derived
  by ordinary instructions in a context with the sort `S : U(ℓ)` and the
  earlier constructors as entries. The kernel checks only the normal form and
  positivity, syntactically. Overlap agreement is the typing of the iterated
  path type.
- **Two Kan classes.** A *data sort* (no dimensions anywhere, modifier `type`)
  composes by pushing through constructors, like `Nat`, sums and W types
  today. A *higher sort* has a formal `hcomp` at fixed parameters; transport
  along parameters computes by recursion with boundary correction; general
  composition is `hcomp` after transport, like pushouts today.
- **One dependent eliminator.** It is a function node with one clause per
  constructor, generated squash constructors included. The motive may land in
  any universe of any tier. Clause types come from the displayed boundary. It
  computes on constructors by `Iota` and on `hcomp` by composition in the
  motive.
- **Universes.** A sort lives in the universe its former's type declares, and
  every data type and arity must fit in it. Parameters count only through
  those types. Lowering is rejected.
- **Level-erased instances.** Level parameters type the parameters only, and
  never occur in a constructor type. An instance `S(a⃗)` carries no level of
  its own: its universe is read from the parameters' judgements, so one term
  serves every universe, as native sums do. The read levels are finite.
  Letting tier-parametric signatures read every tier is a specified
  extension, recommended for later (Q16).
- **Trust.** Admission requires the kernel's H1 extension flag until review.
  Results carry `kernel extension: H1` transitively; it is visible, and it is
  not a non-computing dependency.
- **Differential oracle (K2.4).** `Nat`, sums, W types and pushouts are
  declared as signatures and compared with the hand-coded instructions by a
  level-free translation. In the recommended first release, the `Nat`
  instructions retire, and the sum, W and pushout instructions stay only
  for arguments at tier-1 levels (Q16). Native and declared forms are different
  types; no conversion relates them.
- **Truncation (K2.5, G2).** `Trunc` is universe-preserving and has no
  resizing. The archive keeps its legacy assumptions. Measured on the archive,
  a universe-preserving truncation breaks 47 of 3,804 declarations, from 8
  roots. No remedy needs a resizing assumption: two declarations wait for
  H2's inductive families, four take an explicit smallness hypothesis that
  their one consumer discharges from `LEM`, and the rest need restatement or
  nothing (section 8).

## Notation

| Symbol | Meaning |
| --- | --- |
| `S` | the sort being declared; also its instance `S(a⃗)` at parameters `a⃗` |
| `x⃗` | the signature's level parameters; they type the parameters, and each instance reads them from its parameters' judgements |
| `ρ` | the levels read at an instance, one per level parameter |
| `p⃗ : P⃗` | the signature's term parameters, a telescope over `x⃗` |
| `ℓ` | the sort's level, a level expression over `x⃗` |
| `c_1 … c_n` | constructors, in order; `c_k` also names the constructor at an instance |
| `t⃗ : D⃗` | a constructor's data telescope |
| `q⃗ : Q⃗` | a constructor's positions |
| `A` | an arity, the domain of a position |
| `d_k` | the number of dimensions of `c_k` |
| `r`, `s` | interval formulas |
| `i`, `j`, `h` | dimensions |
| `φ`, `ψ` | face formulas |
| `M` | a motive `Π (z : S). U(l')` |
| `m_k` | the clause for `c_k` |
| `e`, `E` | constructor expressions (1.4) |
| `⟦e⟧` | the displayed version of a constructor expression (3.6) |

"The kernel" is the instruction kernel, `kernel/src/instructions.c`, and the
reduction code it calls. "The driver" is the untrusted
`web/cubical-instruction-driver.mjs`. The term checker and the JavaScript
reference checker are not extended, as the
[work plan](work-plan.md#the-instruction-kernel-and-this-plan) records.

## 1. Signatures

A signature is a parameter telescope, a sort with a level and an h-level
modifier, and an ordered list of constructors.

### 1.1 Parameters

- The telescope starts with level parameters `x⃗`, then term parameters
  `p⃗ : P⃗`, each type well formed over the ones before. At admission the
  telescope is presented as G0's prenex level binders `x⃗ < ω` (G0 Q8).
- **Level-parametric.** A level parameter occurs only in the parameter types,
  never in a constructor type `T_k`. The constructors are therefore built
  from the parameters' values alone, which is what makes level-erased
  instances sound (D9). A signature that stores a type of a parameter level,
  such as `wrap(B : U(x))`, is level-dependent and excluded from H1 (Q15).
- **Determined.** Every level parameter occurs as the whole universe at the
  end of some parameter's type, as in `A : U(x)` or `B : L → U(y)`; `U(x + 1)`
  and `U(max(x, y))` do not count. Each instance reads the level there, from
  that parameter's judgement, as a level expression (3.1). A level parameter
  with no such occurrence is rejected.
- **Finite levels.** The instances of a signature with level parameters
  read finite levels, the range its admission checked. A proposed extension
  would let *tier-parametric* signatures, whose admission derivation never
  uses the finiteness of a level parameter, read levels of every tier (2.3,
  Q16). A signature may also be stated at fixed levels of any tier, with no
  level parameters.
- Parameters are uniform: every occurrence of `S` inside the signature is at
  the declared parameters. A constructor cannot mention `S` at other
  arguments; that is an index, which is H2.

### 1.2 Constructor normal form

The kernel accepts a constructor type `T_k` only in this shape. `s` is the
sort entry and `c_1 … c_{k-1}` are the entries of the earlier constructors
(section 5.2).

```text
T_k  ::= Π (t_1 : D_1) … Π (t_a : D_a). Π (q_1 : Q_1) … Π (q_b : Q_b). R
Q_j  ::= Π (y_1 : A_1) … Π (y_m : A_m). C              m ≥ 0: the arity
C    ::= s  |  Path(i; C, E, E)                          a cube over s
R    ::= s  |  Path(i; R, E, E)                          the result; its depth is d_k
```

- **Data** `D_i` may mention parameters and earlier data. It may not mention
  `s`, any constructor or any position.
- **Positions** `Q_j`: an arity `A_1 … A_m`, a telescope over the parameters
  and data that mentions no `s`, constructor or position; then a cube `C`
  over `s`. A 0-cube `s` is an element, a 1-cube is a path between two
  constructor expressions, and so on.
- **Result** `R`: `s` for a point constructor, or an iterated path type over
  `s` for a constructor with `d_k ≥ 1` dimensions. The endpoints of the path
  over dimension `i_1`, then of the path over `i_2` inside it, and so on, are
  the constructor's boundary.
- **Order.** All data precede all positions, and the kernel rejects a data
  type after a position. Since no data type can mention a position, the
  elaborator can always move source data ahead of the positions (L2.1).
- **Binders.** `Path(i; C, E, E')` is the kernel's dependent path node: its
  family may mention the dimensions of enclosing paths through the endpoints
  of inner paths, and its endpoints mention the enclosing dimensions only.

### 1.3 Positivity

Strict positivity holds by construction, and the kernel checks the shape
above syntactically:

- `s` occurs only as the carrier of a cube `C` at the end of a position, or
  of the result `R`;
- no arity, data type or data argument mentions `s`, a constructor or a
  position;
- nothing else of type `s` exists in the admission context, so positions
  and earlier constructors are the only elements the endpoints can name.

Rejected, each a test: `s` in data (`bad(f : s → Nat)`), `s` in an arity
(`bad(f : (s → Nat) → s)`), `s` under a function inside a cube, a data type
after a position, and an arity mentioning a position.

### 1.4 Boundaries: cube boundaries and constructor expressions

An endpoint `E` of `R` or of a position's cube is a *constructor expression*:

```text
E ::= q_j(u⃗)                          a position applied to data terms at its arity
   |  c_m(u⃗, E⃗')                       an earlier constructor, data terms then positional arguments
   |  E @ r                            path application at an interval formula
   |  ⟨i⟩ E                            path abstraction: a cube of one more dimension
E' ::= E  |  λ (y : A). E'             positional arguments, under the arity's binders
```

- `u⃗` are *data terms*: any terms that mention no `s`, constructor or
  position. They may mention parameters, data, arity variables, and
  dimensions in scope.
- `r` is any interval formula over the dimensions in scope: the enclosing
  paths' dimensions of the result or of the position's cube, and those bound
  by `⟨i⟩`.
- `⟨i⟩ E` is typed by the ordinary `PathLambda` instruction, as a path from
  `E[i := 0]` to `E[i := 1]`. It supplies the 1-cubes that a boundary of
  dimension two or more needs, such as `S2`'s outer endpoints `⟨j⟩ base`, and
  positional arguments of path type.
- No composition, transport, `hcomp` or other operation of type `s` occurs in
  an endpoint (Q3).
- **Cube boundaries.** A constructor with `d` dimensions has a piece on both
  faces `i_l = 0` and `i_l = 1` of every dimension `i_l`: the endpoints of
  its iterated path type. No other face carries a piece (Q4).
- **Overlap agreement is typing.** Forming the iterated path type requires
  each endpoint to have the type of the family at that end. Where two faces
  meet, the two pieces agree by that typing. The driver derives it, by the
  conversions and path steps it already uses. The kernel checks no separate
  agreement condition.

### 1.5 Ordering and forward references

Constructors are admitted one at a time. The admission context for `c_k`
holds `s` and `c_1 … c_{k-1}` only, so an endpoint cannot name `c_k` itself
or a later constructor: the name is not in scope, and the typing judgement
cannot be formed. Rejection tests cover both.

### 1.6 H-level modifiers

`type` adds nothing. `prop` and `set` append one generated constructor after
the user constructors:

```text
prop:  squash : Π (y, z : s). Path(i; s, y, z)
set:   squash : Π (y, z : s). Π (u, v : Path(s, y, z)). Path(i; Path(j; s, y, z), u, v)
```

They are ordinary constructors of the normal form, with positions and a cube
boundary. The elaborator knows their meaning for automatic clauses (L2.2b).
A user constructor cannot mention them, since they come last.

### 1.7 What H1 excludes

- Indices, and constructors that choose result indices: H2.
- Several sorts, and companion sorts: H3 when every sort is `set` or `prop`,
  otherwise H4.
- Non-uniform parameters: an index in disguise, H2.
- Arities that depend on positions (design open question 1).
- Partial boundaries, and boundaries with compositions (Q3, Q4).
- Level-dependent signatures, whose constructor types mention a level
  parameter (Q15).
- Instances at tier-1 levels, in the recommended first release. Q16's
  extension would allow them for tier-parametric signatures.
- Induction-recursion (design open question 2).

### 1.8 Examples in normal form

Level parameters are written `x`, `y`, `z`; `U(x)` is the universe. `Path(S, a, b)`
abbreviates `Path(i; S, a, b)` when `i` is not used. The former type is the
signature's presentation at admission; an instance carries no level (3.1).
Every example is level-parametric: no constructor type mentions `x`, `y` or
`z`.

| Declaration | Former type | Constructors |
| --- | --- | --- |
| `Nat` | `U(0)` | `zero : s`; `succ : Π (n : s). s` |
| `List` | `Π (x < ω). Π (A : U(x)). U(x)` | `nil : s`; `cons : Π (a : A). Π (l : s). s` |
| `W` | `Π (x, y < ω). Π (L : U(x)). Π (B : L → U(y)). U(max(x, y))` | `sup : Π (l : L). Π (c : Π (b : B(l)). s). s` |
| `Pushout` | `Π (x, y, z < ω). Π (C : U(x)). Π (A : U(y)). Π (B : U(z)). Π (m : Σ (f : C → A). C → B). U(max(x, y, z))` | `inl : Π (a : A). s`; `inr : Π (b : B). s`; `push : Π (c : C). Path(s, inl(fst(m)(c)), inr(snd(m)(c)))` |
| `Susp` | `Π (x < ω). Π (A : U(x)). U(x)` | `north`, `south : s`; `merid : Π (a : A). Path(s, north, south)` |
| `S1` | `U(0)` | `base : s`; `loop : Path(s, base, base)` |
| `Torus` | `U(0)` | `b : s`; `p`, `q : Path(s, b, b)`; `surf : Path(i; Path(j; s, p @ i, p @ i), q, q)` |
| `S2` | `U(0)` | `base : s`; `surf : Path(i; Path(j; s, base, base), ⟨j⟩ base, ⟨j⟩ base)` |
| `Trunc`, `prop` | `Π (x < ω). Π (A : U(x)). U(x)` | `point : Π (a : A). s`; generated `squash` |
| `Quotient`, `set` | `Π (x, y < ω). Π (A : U(x)). Π (R : A → A → U(y)). U(max(x, y))` | `class : Π (a : A). s`; `glue : Π (a, b : A). Π (r : R(a, b)). Path(s, class(a), class(b))`; generated `squash` |

In `Torus`, the inner path over `j` runs from `p @ i` to `p @ i`, and the
outer endpoints are `q`. They agree at the four corners, `b`, by the typing
of the path types: `q : Path(s, b, b)` must have the type
`Path(j; s, p @ 0, p @ 0)`, which the path step reduces to it. In `S2`, the
outer endpoints `⟨j⟩ base` are path abstractions (1.4). In `Pushout`,
`fst(m)(c)` is a data term.

## 2. Universes and substitution

### 2.1 The sort's level

- The former's type `Π (x⃗ < ω). Π (p⃗ : P⃗). U(ℓ)` declares `ℓ`.
- Every constructor type `T_k` must be derived at `U(ℓ)` in the admission
  context, where `s : U(ℓ)`. By inversion of the formation rules, every data
  type and every arity in `T_k` then lives in `U(ℓ)`: the instruction kernel
  forms `Π` at the maximum of its parts and raises only by `Lift`, which never
  lowers. The generated squash types live in `U(ℓ)` because they mention only
  `s`.
- Parameters count only through those types (G0 Q6). A parameter that no data
  type or arity mentions contributes nothing.
- The kernel checks `ℓ` as an upper bound. The elaborator declares the least
  level: the maximum of the inferred levels of the data types and arities,
  and `0` when there are none (Q7).
- An instance `S(a⃗)` lives in `U(ℓ[ρ])`, where `ρ` is read from the
  parameters' judgements (3.1). `Trunc(A)` for `A : U(x)` lives in `U(x)`.

### 2.2 Fixtures by case

| Case | Declaration | Level |
| --- | --- | --- |
| Phantom parameter | `Box(x < ω, A : U(x)) { mk(n : Nat); }` | `U(0)` at every `x` |
| Stored data | `Pair(x, y < ω, A : U(x), B : U(y)) { mk(a : A, b : B); }` | `U(max(x, y))` |
| Arity | `W(x, y < ω, L : U(x), B : L → U(y))` | `U(max(x, y))`: `B(l)` is an arity |
| Relation | `Quotient(x, y < ω, A : U(x), R : A → A → U(y))` | `U(max(x, y))`: `r : R(a, b)` is data of `glue` |
| Large parameter only | `Tag(A : U(1)) { here; }` | `U(0)` |
| Tier 1 through parameters | `Pair(A, B)` for `A, B : UU0` | Refused in the first release; with Q16's extension, `UU0`, both level parameters reading `ω` |
| Tier 1 at fixed levels | `Big(A : UU0) { wrap(a : A); }` | `UU0` |

Indices, the fifth case the work plan lists, arrive with H2; the rule then
counts index types too (G0 2.12).

### 2.3 Instances and rejections

- **One term at every universe.** `Trunc(A)` is one term. It is typed at
  `U(ℓ[ρ])` for the levels `ρ` read from `A`'s judgement, and a derivation
  that first lifts `A` types it higher; cumulativity relates the two. So
  `point(a)`, built where `A : U(0)`, is a term of `Trunc(A)` where a generic
  definition sees `A : U(1)`. The native sums behave this way today:

  ```text
  def sum_id(U < UU0, A : U, x : A or A) : A or A := x;
  def small : Nat or Nat := left(0);
  def lifted : Nat or Nat := sum_id(U1, Nat, small);
  ```

  checks, and its translation (7.2) must check too. For declared sorts this
  replaces G0 Q1's distinct instances (Q8).
- **Instances within the admission's bound.** Admission derives the
  constructor types with level entries `x < ω`, so the derivation holds at
  every finite assignment, by G0's level substitution (G0 Lemma 4). An
  instance therefore reads finite levels: tier-0 level expressions, which may
  mention level variables. A read level of tier 1 or above is refused. This
  is the rule of the recommended first release (Q16).
- **Extension: tier-parametric signatures (Q16).** The native formers accept
  arguments at every tier. A signature could too, if its admission never
  relied on its level parameters being finite. Q16 decides whether H1
  includes this extension; the recommendation is to defer it. It is
  specified here so that the choice is concrete.

  *Criterion.* A signature is tier-parametric when its admission is
  derivable without using the bound `x < ω` of any level parameter, so that
  every level side condition of the derivation holds when the level
  parameters range over all ordinals below ω². G0's rules use the bound in
  three places: `LevelApply` requires a finite level; level normal forms
  absorb a variable into a constant of tier 1 or above, as in
  `max(x, ω) = ω` and `x ≤ ω`; and a level quantification lives at the
  limit `ω` of its body's levels.

  *The check.* A signature's own text does not show every bound: the two
  counterexamples below hide one in a type the signature uses. So the kernel
  checks the admission derivation itself, below the signature's own
  closing prenex. The closed former judgement that `SignatureBegin` takes
  ends in one `LevelPi` per level parameter and one `Pi` per term
  parameter, above the universe `U(ℓ)`. That prenex only closes the
  telescope, and it lives in `U(ω)` whenever a level parameter occurs, so
  the walk does not visit it. With the extension, `SignatureBegin` requires
  the former judgement to end in exactly that prenex. The walk starts from:

  - for each term parameter, the judgement that its type is a type: the
    source judgement recorded by `Extend` for the entry that the
    corresponding prenex `Pi` discharges;
  - the judgement `U(ℓ) : U(ℓ + 1)` below the prenex;
  - every `SignatureConstructor` judgement.

  From these it follows premises and the source judgements of the entries
  it meets, and visits each judgement once. It requires, of every judgement
  it visits:

  1. no `LevelPi`, `LevelLambda` or `LevelApply` instruction: level
     quantification used within a parameter type or a constructor type is
     still refused, only the closing prenex is exempt;
  2. no level of tier 1 or above in its term or its type;
  3. every signature whose instance, constructor or eliminator occurs is
     itself tier-parametric, by its recorded flag. A signature with no
     parameters is no exception: its flag comes from the same check on its
     own admission.

  Definitions may occur, through `Lookup` and `Delta`. A closed definition
  has no level entries, so it cannot use a binder bound, and its type and
  any unfolded value that appears in the derivation are subject to rule 2.
  The native formers need no flag: their instructions' side conditions are
  uniform in levels (cases (i) to (iv) below). The check reads the
  derivation as given, so a needless lift into a tier-1 universe makes a
  signature bounded; L2.1's driver derives with least levels, and the
  inspector shows the flag.

  *Sufficiency, proved here in outline.* Let `D` be the walked judgements:
  the derivations of the parameter types, of `U(ℓ)` and of the constructor
  types. Those are what an instance needs; formation reads the telescope
  directly, so the closing prenex plays no part. Let `ρ` be any assignment
  of ordinals below ω² to the level parameters. Then `D[ρ]` is a valid
  derivation, by induction on `D`, instruction by instruction:

  - (i) formation of `Π`, `Σ`, path types, sums, W types, pushouts and
    universes: the conclusion's level is the maximum or successor of the
    premises' levels, computed by the same arithmetic after substitution;
  - (ii) side conditions of alpha equality: levels are compared by normal
    form, and two tier-0 expressions with equal normal forms denote the same
    function of the ordinals;
  - (iii) `Lift`: an inequality between tier-0 normal forms that holds for
    every finite assignment holds coefficient by coefficient (G0 Lemma 2),
    the constants and each variable's offset. It then holds at every
    ordinal assignment, because `x ↦ x + n` and `max` are monotone on
    ordinals;
  - (iv) steps: no reduction rule reads a level (G0 Lemma 5, and 3.7), so
    each contraction commutes with `ρ`;
  - (v) forming an instance of another signature, with read levels `ρ'`:
    after substitution the read levels are `ρ'[ρ]`, possibly infinite, and
    they are accepted because that signature is tier-parametric. By
    induction on the order of admission, the claim already holds for it.

  Rule 1 excludes the only instructions that test finiteness, and rule 2
  keeps every level in tier-0 form, so no other case arises. Hence the
  constructor types are well formed at `ρ`, and their comparisons with `ℓ`
  hold. The classification of each instruction into (i) to (v) is a review
  item of each K2.2 family; an instruction added later must be classified
  before the check admits it.

  *Examples.* `Pair`, `Trunc`, `Quotient` and the K2.4 counterparts pass:
  their derivations use only their parameters, universes at their level
  parameters, `Π`, `Σ`, projections and path types. `Pair(A, B)` for
  `A, B : UU0` then lives in `UU0`, as the native `A or B` does.
- **Hidden bounds: two counterexamples.** Without the extension, both are
  refused at formation because they read a tier-1 level. With it, the check
  above rejects both classes of hidden bound:

  ```text
  inductive Tag(A : UU0) : U0 { here; }
  inductive Outer(U < UU0, A : U) : U0 { wrap(t : Tag(A)); }

  inductive Big : UU1 { pack(B : UU0); }
  inductive Outer2(U < UU0, A : U, F : Big -> U0) : U0 { wrap(t : F(pack(A))); }
  ```

  Both `Outer` and `Outer2` are admitted: for finite `x`, `A : U(x)` lifts
  into `UU0`. Neither passes the check. `Outer` forms `Tag(A)`, which lifts
  `A` to `U(ω)`, a tier-1 level (rule 2), and `Tag` itself is not
  tier-parametric (rule 3). `Outer2` constructs `pack(A)`, whose constructor
  has type `Π (B : UU0). Big` (rule 2), and `Big`, though it has no
  parameters, is not tier-parametric (rule 3). So `Outer(UU0)` and
  `Outer2(UU0, F)`, which read `x = ω + 1`, are refused at formation. Their
  constructor types would contain `Tag(UU0)` and `pack(UU0)`, which are
  ill-typed since `UU0 : UU1` (acceptance V17, V19). The read level `ω`,
  where `Tag(A)` and `pack(A)` happen to exist, is refused too: telling the
  two apart would mean checking the signature again at the instance.
- **Lowering.** A constructor type that needs a level above `ℓ` cannot be
  derived at `U(ℓ)`, since no instruction lowers a universe. Example:
  `Small(x < ω, A : U(x)) : U(0) { wrap(a : A); }` is rejected at `wrap`.
- **Level-dependent signatures.** `Wrap(x < ω) : U(x + 1) { wrap(B : U(x)); }`
  is rejected: `x` occurs in a constructor type. Its elements store types of
  level `x`, so its instances at different levels differ, and erasing the
  level would identify them (Q15).
- **Tier-1 constants with level parameters.**
  `Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); }` is admitted, but it
  is not tier-parametric. G0's normal form absorbs `x` into `ω` in
  `max(x, ω)`, which is valid only while `x` is finite, and its instances read
  finite levels only (Q16).
- **Undetermined level parameters.** A level parameter that ends no
  parameter's type is rejected (1.1).
- **The former is not a term.** A declared type used as a function, such as
  `Trunc` unapplied, is the elaborator's eta-expansion
  `fun (U < UU0, A : U) => Trunc(A)`: a G0 generic definition of type
  `Π (x < ω). Π (A : U(x)). U(x)`, in `U(ω)`. The instance inside it carries
  no level.

### 2.4 Level substitution

- Instance nodes carry no level argument of their own, but their parameter
  terms may mention levels. Level substitution is G0's ordinary recursive
  substitution (G0 2.8), through every subterm: parameters, constructor
  arguments, motives and clauses. So `(λ (x < ω). Trunc(U(x))) {0}` reduces
  by `Beta` to `Trunc(U(0))`, and an eliminator whose motive lands in
  `U(x + 1)` becomes one into `U(1)` (acceptance V16).
- Formation reads an instance's levels from its parameters' judgements
  (3.1), so the reading is itself substituted: a parameter judgement
  `U(x) : U(x + 1)` becomes `U(0) : U(1)`, and the read level becomes `1`.
  Level substitution therefore commutes with formation when the substituted
  levels stay within the signature's bound. G0's substitution is at finite
  levels, which every signature accepts.
- No reduction rule reads a level (3.3–3.7), so G0's Lemma 5 extends:
  reduction commutes with level substitution.
- The eliminator's motive may land in `U(l')` for any `l'`, including a
  level variable and a UU-tier constant. The eliminator is therefore a node,
  not a level-quantified constant: a constant would bind the motive's level
  below `ω` (5.6).

### 2.5 Dimension substitution and stability

- A constructor at interval formulas `c_k(…) @ r_1 … @ r_d` substitutes
  dimensions into the formulas only. At a face where some `r_l` becomes an
  endpoint, the path step (or weak head reduction) replaces the application
  by the boundary piece of the constructor's type, with the other formulas
  kept. Because the boundary is typed as an iterated path type, the result
  is the same in whichever order faces are reached (1.4).
- Every generated reduction rule of section 3 commutes with substitution of
  interval formulas and endpoints for free dimensions (Lemma H2, 4.3).

## 3. Generated rules

### 3.1 Formation

An instance `S(a⃗) : U(ℓ[ρ])` is formed from judgements `a_i : P_i[ρ, a_<i]`,
one per term parameter, in order:

- each level parameter reads its level `ρ(x)` at its determining occurrence:
  the universe at the end of the corresponding parameter judgement's type;
- every parameter judgement's type must then be exactly `P_i` with `ρ` and
  the earlier parameters substituted, up to alpha equality. When two
  occurrences of a level parameter would read different levels, the
  judgement is refused, and the driver lifts the lower parameter first;
- the term records the signature and the term parameters only. It carries no
  level.

The read levels must be finite. With Q16's extension, a tier-parametric
signature's may be of any tier (2.3). A derivation that lifts a parameter
first reads a higher `ρ`, and types the same term in a higher universe.

### 3.2 Constructors and boundary reduction

- At an instance `I = S(a⃗)`, the constructor `c_k` is the term `Con(k; I)`, of
  type `T_k[s := I, p⃗ := a⃗, c_m := Con(m; I)]`. No level is substituted, since
  `T_k` mentions no level parameter (1.1).
- A saturated application `Con(k; I)(u⃗, e⃗)`, written `c_k(a⃗)(u⃗, e⃗)` below, is
  canonical. With `d_k ≥ 1` it is a path, and `(c_k … ) @ r_1 … @ r_d` with no
  `r_l` an endpoint is canonical.
- **Boundary reduction.** `(c_k …) @ 0` and `(c_k …) @ 1` reduce to the
  endpoints of its type: by the existing `Path` step, which reads the path
  application's type annotation, and by weak head reduction, which reads the
  signature. This is the design's "a constructor evaluated on a face of its
  dimensions reduces to its boundary".
- Eta for paths gives `c_k … ≡ ⟨i⟩ (c_k …) @ i` as for any path.

### 3.3 Kan structure of a data sort

A data sort has `d_k = 0` for every constructor and modifier `type`. It has
no formal composition.

```text
comp^i S(a⃗(i)) [φ ↦ u] u_0
  ⟶  c_k(a⃗(1))(comp^i Θ_k(a⃗(i)) [φ ↦ θ_u] θ_0)
      when whnf(u_0) = c_k(a⃗(0))(θ_0) and whnf(u) = c_k(a⃗(i))(θ_u) on every nonempty face
comp^i S(a⃗(i)) [φ ↦ u] u_0  is neutral otherwise
```

- `a⃗(i)` is the parameter line; levels do not vary (G0 2.11).
- `Θ_k(a⃗)` is the argument telescope of `c_k` at the parameters: data then
  positions. Composition in a telescope is iterated Σ composition: each
  component is composed in its type, after filling the earlier components
  along `i` and substituting them. A position's type is a `Π` over its arity
  into `S`, composed by the `Π` rule with its backward filling. This is how
  `composition_compute.c` and `inductive_composition.c` compute sums and W
  types today.
- Transport along a parameter line is the case `φ ↦ u_0` on the constancy
  face, and needs no separate rule.
- No rule turns a neutral tube into a constructor because its base is one.

### 3.4 Kan structure of a higher sort

A higher sort has a constructor with `d_k ≥ 1` or modifier `set` or `prop`.

- **Formal homogeneous composition.** `hcomp^i S(a⃗) [φ ↦ u] u_0 : S(a⃗)`,
  at fixed parameters, is canonical. On a face that holds it reduces to that
  tube at `i = 1` (the `Face` step); tubes on the empty face are dropped. It
  never pushes into a constructor.
- **General composition** reduces to formal composition after transport, as
  `ck_pushout_composition` does today:

  ```text
  comp^i S(a⃗(i)) [φ ↦ u] u_0
    ⟶  hcomp^j S(a⃗(1)) [φ ↦ transp^k S(a⃗(j ∨ k)) (j = 1) u(j)] (transp^i S(a⃗(i)) 0 u_0)
  ```

- **Transport** `transp^i S(a⃗(i)) φ u_0`, with `a⃗` constant on `φ`, computes
  by the weak head of `u_0`. Section 3.5 gives the rules. When `φ` holds, it
  reduces to `u_0` (the `Face` step).

### 3.5 Transport along parameters with boundary correction

Write `A(i) := S(a⃗(i))`. For a line `w(i) : A(i)` define the squeeze, which
joins the transport of `w(0)` to `w(1)` and is fixed on `φ`:

```text
squeeze^i_A φ w  :=  transp^h A(i ∨ h) (φ ∨ (i = 1)) w(i)          at i = 0: transp^h A(h) φ w(0); at i = 1: w(1)
```

`transp^i A(i) φ u_0` reduces by cases on `whnf(u_0)`:

1. **Point constructor** `c_k(a⃗(0))(θ_0)`, `d_k = 0`. Let `θ(i)` be the
   transport filler of the telescope: `θ(i) := fill^i Θ_k(a⃗(i)) [φ ↦ θ_0] θ_0`,
   so `θ(0) = θ_0` and `θ` is constant on `φ`. Then
   `transp^i A(i) φ u_0 ⟶ c_k(a⃗(1))(θ(1))`.
2. **Constructor at dimensions** `(c_k(a⃗(0))(θ_0)) @ r_1 … @ r_d`, no `r_l` an
   endpoint. With `θ` as above, let `v := (c_k(a⃗(1))(θ(1))) @ r⃗`. For each
   face `(l, ε)`, let `b_{l,ε}(i)` be the boundary piece of `c_k` on
   `i_l = ε`, at parameters `a⃗(i)` and arguments `θ(i)`, with the other
   formulas `r⃗` substituted. Then

   ```text
   transp^i A(i) φ u_0
     ⟶  hcomp^h A(1) [ φ ↦ u_0,
                       (r_l = ε) ↦ (squeeze^i_A φ b_{l,ε})[i := 1 - h]   for each l ≤ d, ε ∈ {0, 1} ]
                     v
   ```

   - At `h = 0` each wall is `b_{l,ε}(1)`, which is `v` on its face; on `φ`
     the base is `u_0`, since `a⃗` and `θ` are constant there.
   - At `h = 1` the wall on `r_l = ε` is `transp^i A(i) φ b_{l,ε}(0)`, the
     transport of `u_0` restricted to that face. So transport commutes with
     restriction to the constructor's faces.
   - Where two walls meet, their pieces agree by the cube boundary's typing
     (1.4), so the squeezes agree. On `φ ∧ (r_l = ε)` the squeeze is constant
     and equals `u_0` there.
   - For `d = 1` this is the pushout rule in `hit_composition.c`.
3. **Formal composition** `hcomp^j A(0) [ψ ↦ w] w_0`. Transport commutes:
   `⟶ hcomp^j A(1) [ψ ↦ transp^i A(i) φ w(j)] (transp^i A(i) φ w_0)`.
4. **Otherwise** the transport is neutral.

### 3.6 The eliminator and clause types

**Motive and clauses.** For an instance `S(a⃗)`, a motive `M : Π (z : S(a⃗)). U(l')`
at any level `l'`, and clauses `m_1 … m_n` (squash constructors included),
the eliminator `elim_{M, m⃗} : Π (z : S(a⃗)). M(z)`.

**Displayed types.** For a cube `C` over `S` and `y : C`, its displayed type
`C̄(y)`:

```text
S̄(y)                  :=  M(y)
Path(i; C, E, E')‾(y) :=  PathP(i. C̄(y @ i), ⟦E⟧, ⟦E'⟧)
```

A position `q : Π (y⃗ : A⃗). C` has displayed type `q̄ : Π (y⃗ : A⃗). C̄(q(y⃗))`.

**Displayed boundary.** `⟦E⟧` replaces, in a constructor expression, each
position by its displayed variable and each earlier constructor by its
clause:

```text
⟦q_j(u⃗)⟧          :=  q̄_j(u⃗)
⟦c_m(u⃗, E⃗')⟧       :=  m_m(u⃗, E⃗', ⟦E⃗'⟧')
⟦E @ r⟧           :=  ⟦E⟧ @ r
⟦⟨i⟩ E⟧           :=  ⟨i⟩ ⟦E⟧
⟦E⟧'              :=  ⟦E⟧                          ⟦λ (y : A). E'⟧' := λ (y : A). ⟦E'⟧'
```

**Clause type.** With `c := c_k(a⃗)(t⃗, q⃗)`:

```text
ClauseType_k(M, m_1 … m_{k-1})  :=  Π (t⃗ : D⃗). Π (q⃗ : Q⃗). Π (q̄⃗ : Q̄⃗). R̄(c)
R̄(c)  :=  M(c)                                                  d_k = 0
R̄(c)  :=  PathP(i_1. … PathP(i_d. M(c @ i_1 … @ i_d), ⟦·⟧, ⟦·⟧) …, ⟦·⟧, ⟦·⟧)   d_k ≥ 1
```

with the displayed boundary pieces at the endpoints, in the nesting of `R`.
Only `m_1 … m_{k-1}` occur, so the clause types form a telescope, and the
kernel checks the clauses in order.

**Partial eliminator.** This is the design's "clause types from running the
partial eliminator", specialised to constructor expressions. On them,
running the eliminator with the clauses as variables is exactly the
substitution `⟦·⟧`, so the kernel computes clause types by substitution, with
no reduction. Lemma H1 (4.3) shows the two agree: after
`q̄ := λ y⃗. elim(q(y⃗))`, pointwise along a cube, `⟦E⟧` is convertible to
`elim(E)` by `Iota` steps.

**Automatic clauses** (L2.2b) are the elaborator's: the kernel requires every
clause, the squash clause included.

### 3.7 Computation rules

| Rule | Reduction | Step |
| --- | --- | --- |
| Iota, point | `elim_{M,m⃗}(c_k(a⃗)(t⃗, q⃗)) ⟶ m_k(t⃗, q⃗, q̄⃗)` with `q̄_j := λ y⃗. elim^{C_j}(q_j(y⃗))` | `Iota` |
| Iota, dimensions | `elim_{M,m⃗}((c_k(a⃗)(t⃗, q⃗)) @ r_1 … @ r_d) ⟶ m_k(t⃗, q⃗, q̄⃗) @ r_1 … @ r_d` | `Iota` |
| Boundary | `(c_k(a⃗)(t⃗, q⃗)) @ ε ⟶` the endpoint of its type | `Path`, `Whnf` |
| Elimination of `hcomp` | `elim(hcomp^j S [ψ ↦ w] w_0) ⟶ comp^j M(hfill^j) [ψ ↦ elim(w(j))] (elim(w_0))` | `Whnf` |
| Data-sort composition | 3.3 | `Whnf` |
| Higher-sort composition | 3.4 | `Whnf` |
| Transport | 3.5 | `Whnf`; `Face` when `φ` holds |
| `hcomp` on a face that holds | the tube at `1` | `Face` |

- `elim^{C}` lifts the eliminator along a cube: `elim^{S}(y) := elim(y)` and
  `elim^{Path(i; C, E, E')}(y) := ⟨i⟩ elim^{C}(y @ i)`.
- `hfill^j := hcomp^k S [ψ ↦ w(j ∧ k), (j = 0) ↦ w_0] w_0`, the homogeneous
  filler, as `ck_pushout_eliminate_hcomp` builds it.
- The path annotations that `Iota` attaches to `m_k(…) @ r` are the clause
  type's nested `PathP` types, read off the eliminator's signature.
- Confluence at a boundary: `elim((c_k …) @ 0)` reduces by `Iota` to
  `m_k(…) @ 0`, then by the path step to the clause type's endpoint, which is
  `⟦β⟧`; or by the boundary rule to `elim(β)`. The two agree by Lemma H1.

### 3.8 Canonical forms

A closed element of a data sort instance, in a context of dimensions only,
reduces to a saturated constructor. A closed element of a higher sort
reduces to a constructor at non-endpoint formulas, or to an `hcomp` whose
base and tubes reduce to such forms. Section 4.4 argues this.

## 4. Soundness, consistency and canonicity note

### 4.1 Baseline

G0 fixes the trust base (G0 3.1 and 3.6): De Morgan CCHM with Π, Σ, Path and
Glue, a cumulative hierarchy over the ordinals below ω², natural numbers,
unit, empty type, sums, W types and pushouts. Its consistency and
canonicity with these formers is **assumed**; in particular no published
canonicity proof covers the kernel's pushouts. H1 adds one schema of
declarations to this base. The claims below are relative to it.

### 4.2 Semantic construction

This follows the design's proposed route (design §4), restricted to one sort
and no indices.

1. **Levels.** A level-parametric signature's constructor types mention no
   level parameter, so the construction below takes only the parameters'
   values `⟦a⃗⟧` as input. The levels `ρ` read at an instance only name a
   universe `U_α` that contains the result. Each such `α` is large enough:
   for finite `ρ` by G0's substitution into the admission derivation, and,
   with Q16's extension, for a tier-parametric signature at any `ρ` by the
   induction of 2.3. So one presheaf interprets the instance at every `ρ`, and
   cumulativity by subsumption relates the universes (D9). Every other H1
   obligation is argued at fixed parameter values.
2. **Carrier.** For fixed parameters `a⃗` in a context `Γ`, define the
   presheaf `⟦S(a⃗)⟧` over cubes as the least family of sets closed under:
   - a constructor `c_k` applied to an element of its argument telescope at
     that cube, when `d_k = 0`;
   - a constructor `c_k` applied to its arguments and to `d_k` interval
     elements, when none of them is an endpoint;
   - for a higher sort, a formal composition whose base and tubes are
     elements.

   Restriction maps act on arguments and formulas. A constructor whose
   formulas restrict to an endpoint is sent to its boundary piece, which is an
   earlier constructor expression, defined already by the order of
   constructors. The carrier therefore contains only reduced forms, as in
   Coquand–Huber–Mörtberg.
3. **Well-definedness of restriction.** Two faces of a constructor can both
   hold after restriction; the resulting pieces agree, by the cube boundary's
   typing (1.4), whose interpretation is an equality of elements.
4. **Strict positivity.** The generating clauses mention the carrier only
   as the codomain of arities, and at higher cubes for cube positions. The
   arities are interpreted before the carrier. So the definition is an
   ordinary (possibly infinitary) inductive definition in the metatheory,
   indexed over cubes.
5. **Fibrancy.** A data sort's composition is defined by recursion on the
   base's constructor (3.3), as for CCHM's natural numbers. A higher sort's
   homogeneous composition is the formal generator; its uniformity holds
   because restriction commutes with every generator. Transport along a
   parameter line is defined by recursion on the base (3.5); heterogeneous
   composition is the decomposition of 3.4.
6. **Eliminator.** Defined by structural recursion on generators, following
   3.7. It commutes with restriction, so it is a section, and the
   computation rules hold strictly.
7. **Consistency.** Relative to the baseline model, since the carriers are
   presheaves of the same kind as the baseline's pushouts.

### 4.3 Departures from published work, and their arguments

| # | Departure | Argument | Status |
| --- | --- | --- | --- |
| D1 | A general schema, where Coquand–Huber–Mörtberg treat examples | Steps 2–6 of 4.2 are uniform in the signature. The only signature-specific facts used are the constructor order (for restriction), the cube boundary's typing (for overlaps) and positivity (for the inductive definition). | Argued. **Open obligation:** the model construction written out for the whole schema |
| D2 | Data sorts have no formal composition | Composition by recursion on constructors is CCHM's treatment of natural numbers and the kernel's of sums and W types. Adding a formal `hcomp` that also pushes would break confluence: `elim` of a pushed and of a formal composition differ (clause of compositions against composition of clauses). | A conditional outline, found valid in review; standard for the three hand-coded types |
| D3 | Transport with boundary correction for `d ≥ 1` | 3.5 generalises the pushout rule. The walls agree on overlaps because boundary pieces agree on corners, and the result restricts to the transport of each boundary piece. | The local wall calculation was found valid in review. Its stability under substitution belongs to Lemma H2, which is open |
| D4 | Cube positions (paths as arguments), needed by `set` squash | In step 2 a cube position is an element of the carrier at a higher cube with its boundary: still strictly positive. | Argued. **Open obligation:** well-foundedness of the definition when positions live at higher cubes, written out |
| D5 | Infinitary positions in higher sorts | Step 4's inductive definition allows infinitary generating clauses; the metatheory needs the corresponding well-founded trees, which ZFC provides. | Argued. **Open obligation:** the infinitary inductive definition over cubes, with restriction, written out |
| D6 | Path-valued constructors | A presentation of dimension arguments: `c @ r` is the constructor at `r`. It changes no rule of the model. | A conditional outline, found valid in review |
| D7 | Motives in any universe, including UU tiers | The eliminator is defined in the model at fixed parameter values, and a motive's universe plays no role in its definition. | A conditional outline, found valid in review |
| D8 | Level-generic signatures | No reduction rule reads a level. Level substitution recurses through parameter terms, motives and clauses, and commutes with formation's reading of levels from parameter judgements (2.4). | Argued; corrected after the second review, which found the first statement ignored levels inside parameter terms. Relies on G0 |
| D9 | Level-erased instances | The constructor types mention no level parameter, so the carrier, its Kan structure and its eliminator are built from `⟦a⃗⟧` alone (4.2, step 1). Cumulative universes are nested by subsumption, so one presheaf lies in every `U_α` that is large enough. At finite read levels, G0's substitution into the admission derivation shows each is. With Q16's extension, a tier-parametric signature is instantiated at tier-1 levels too. Its admission derivation uses no finiteness of a level parameter, which the kernel checks on the derivation itself, and 2.3's induction replays it at every ordinal assignment. This is the condition under which Timany and Sozeau make instances of a Coq inductive cumulative. | Argued at finite levels. Two reviews found bounds hidden in referenced types, first through a signature's parameter type and then through a parameter-free signature's constructor. The extension now rests on a check of the derivation, whose sufficiency is proved in outline (2.3). To be reviewed |

**Lemma H1 (clause typing is the partial eliminator).** For a constructor
expression `E` over positions `q⃗` and earlier constructors, and the
substitution `σ := [q̄ := λ y⃗. elim^{C}(q(y⃗))]`, `⟦E⟧σ ≡ elim^{C}(E)` by `Iota`
steps. Proof: induction on `E`. For `q_j(u⃗)`, both sides are
`elim(q_j(u⃗))`. For `c_m(u⃗, E⃗')`, the right side takes one `Iota` step to
`m_m(u⃗, E⃗', elim(E⃗'))`, which is the left side by induction. Path
application commutes with both sides. For `⟨i⟩ E`, the right side is
`⟨i⟩ elim^{C}((⟨i⟩ E) @ i)`, which a `Path` step takes to `⟨i⟩ elim^{C}(E)`,
the left side by induction. Status: proved here in outline; found valid in
review as a conditional outline.

**Lemma H2 (stability).** Every rule of 3.3–3.7 commutes with substitution
of interval formulas for dimensions, and of level expressions for level
variables. Argument: the redex patterns mention constructor heads, `hcomp`,
transport and path application, which substitution preserves. The
side conditions that do change under substitution are "a formula is an
endpoint" and "a face holds"; when one becomes true, the boundary and face
rules apply, and the correction walls of 3.5 are built so that the result
restricts to the boundary (3.5, case 2). Data-sort composition gains a redex
under substitution only when a neutral tube becomes a constructor, which
is a new reduction, not a changed one. Level substitution acts on instance
terms through their parameters, motives and clauses, as on any term. No
reduction rule reads a level, so it commutes with every rule (2.4). Status:
argued. **Open obligation:** the full case analysis, rule by rule,
including the corrected transport of 3.5 under substitution of formulas
into `r⃗` and `φ`.

### 4.4 Canonicity

**Claim.** Let `t` be a term in a context of dimension variables only, of a
closed data type in the sense of invariant 10, using no assumption. Then `t`
reduces to a canonical value. For declared data sorts, the value is a
saturated constructor. For higher sorts, it is a constructor at
non-endpoint formulas, or an `hcomp` of such.

**Argument.** Extend Huber's computability predicates:

- For a closed instance `S(a⃗)`, a term is computable when its weak head is
  a saturated constructor, at non-endpoint formulas for `d_k ≥ 1`, whose data
  arguments are computable at their types and whose positions are computable
  pointwise; or, for a higher sort, an `hcomp` whose tubes and base are
  computable. Restricted to any face, it must stay computable. This is an
  inductive definition, strictly positive by 1.3, and the arities'
  predicates are defined before it by the induction on types.
- The fundamental lemma gains the cases of formation, constructors,
  boundary reduction (stable by the cube boundary's typing), the eliminator
  (by induction on the computability of the scrutinee: a constructor gives a
  clause applied to computable arguments, and `hcomp` gives a composition in
  the motive, computable by the motive's own case), transport (by induction
  on the base, using the argument types' transport and a computable
  correction `hcomp`), and composition (3.4).
- For a data sort, the tubes of a composition in a dimension context are
  computable, so their weak heads are constructors. They agree with the base
  at `i = 0` on their faces, so they are the base's constructor, and the
  composition pushes. This is Huber's argument for natural numbers.
- Eliminating a higher sort into a data type turns `hcomp` into composition
  in the data type, which pushes. So a closed natural number reached through
  any H1 declaration normalizes to a numeral, as the governing requirement
  asks.

**Status.** Argued, by extension of Huber's predicates, as G0 3.5 argues for
level quantification. It is not written out, and it inherits the assumed
canonicity of the baseline (4.1).

**Computability tracking.** Declarations are not assumptions. A result that
uses a declared type has no new non-computing dependency; it carries the
`kernel extension: H1` marker until review (5.7). `computable` accepts the
marker.

### 4.5 What is proved, argued and assumed

| Claim | Status |
| --- | --- |
| Positivity and shape of admitted signatures are decided syntactically | Specified here (1.2–1.5); K2.2 implements the check |
| Overlap agreement of cube boundaries follows from typing | Proved here: it is the typing of the iterated path type (1.4) |
| Clause typing agrees with the partial eliminator | Proved here in outline (Lemma H1) |
| Reduction is stable under dimension and level substitution | Argued (Lemma H2); the full case analysis is an **open obligation** |
| The model of 4.2 for the whole schema | Argued from Coquand–Huber–Mörtberg's construction (D1–D9); the construction written out is an **open obligation** (D1) |
| Well-foundedness of the carrier with cube and infinitary positions | Argued (D4, D5); written out is an **open obligation** |
| Transport with boundary correction for `d ≥ 2` | The local wall calculation is checked (D3); its stability is Lemma H2's open obligation; property tests in section 10 |
| Level-erased instances are sound at finite levels | Argued (D9), from G0's level substitution |
| With Q16's extension, tier-parametric signatures are sound at every tier | Proved here in outline, by induction on the checked admission derivation (2.3). The classification of each instruction into the cases of that induction is a review item of K2.2 |
| Confluence of the generated rules with the existing ones | Argued at boundaries (3.7); the full critical-pair check is an **open obligation** |
| Canonicity for H1 | Argued (4.4), relative to the assumed baseline |
| Consistency and canonicity of the baseline, pushouts included | **Assumed**, as in G0 3.6 |
| Normalization, for decidable conversion | **Not established**; the kernel relies on budgets, as today |

### 4.6 Literature

- Coquand, Huber, Mörtberg, *On Higher Inductive Types in Cubical Type
  Theory*, LICS 2018. The cubical-set semantics of spheres, the torus,
  suspensions, pushouts and propositional truncation; formal homogeneous
  composition; transport along parameters with boundary correction. The
  kernel's pushouts follow it. To our reading they treat these examples and
  describe the pattern, without a general schema and its soundness proof.
- Cavallo, Harper, *Higher Inductive Types in Cubical Computational Type
  Theory*, POPL 2019. To our reading: a general schema of indexed cubical
  inductive types whose boundaries are constructor terms, with a
  computational semantics and canonicity, set in Cartesian cubical
  computational type theory with coercion and formal coercion along
  indices. It supports this schema's shape without covering the kernel's De
  Morgan rules.
- Vezzosi, Mörtberg, Abel, *Cubical Agda: A Dependently Typed Programming
  Language with Univalence and Higher Inductive Types*, ICFP 2019 (JFP 2021).
  User-declared higher inductive types with parameters in De Morgan cubical
  type theory, on Coquand–Huber–Mörtberg's pattern. An implementation, not a
  soundness proof of the schema.
- Huber, *Canonicity for Cubical Type Theory*, J. Automated Reasoning 63,
  2019. The computability predicates that 4.4 extends.
- Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory*, TYPES 2015 (2018).
  The base theory and its model.
- Lumsdaine, Shulman, *Semantics of Higher Inductive Types*, Math. Proc.
  Cambridge Phil. Soc. 169, 2020. A general class of higher inductive types,
  including infinitary ones, in model categories. It supports the coherence
  of the class, in a different setting.
- Kaposi, Kovács, *Signatures and Induction Principles for Higher
  Inductive-Inductive Types*, LMCS 16, 2020. Signatures for the whole H
  family; H1's signatures are a subclass.
- Timany, Sozeau, *Cumulative Inductive Types in Coq*, FSCD 2018. Instances
  of an inductive at different levels related when the levels only bound
  parameters: the condition D9 relies on.
- The Univalent Foundations Program, *Homotopy Type Theory*, 2013, §3.5 and
  Exercise 3.10: excluded middle at `U(ℓ + 1)` makes the propositions of
  `U(ℓ)` and `U(ℓ + 1)` equivalent. The ledger's `LEM`-dependent remedies use
  it (8.4).

## 5. K2.2: instruction families

Each family is reviewed and merged separately with its rejection tests,
then integrated (work plan stage 2). Nothing is added to the term checker or
the JavaScript reference checker.

### 5.1 Node kinds and tables

Tags 1–49 keep their numbers. New kinds are appended:

| Tag | Kind | Payload and children |
| --- | --- | --- |
| 50 | `CC_SORT` | payload: signature index; child 0: the term parameters, as a list. An instance `S(a⃗)`, with no level. |
| 51 | `CC_CON` | payload: constructor number; child 0: the instance. The constructor `Con(k; I)`, a function of its data and positions. |
| 52 | `CC_ELIM` | payload: signature index; child 0: motive; child 1: clause list. A function on the sort. |
| 53 | `CC_LIST` | child 0: an item; child 1: the next cell, or 0. Parameter and clause lists. |

- `CC_HCOMP` and `CC_TRANS` keep their layout. Their family may be any higher
  sort instance, not only a pushout.
- **Signature table.** Each entry records: its state (open or admitted); the
  former's type; the level and parameter binder symbols; each level
  parameter's determining occurrence; the sort symbol and level `ℓ`; the
  h-level modifier; and, per constructor, its symbol, its type `T_k` over the
  admission symbols, the split between data and positions, each position's
  arity length and cube depth, and `d_k`.
- **Rollback** removes every signature opened or admitted since the
  checkpoint, as it removes definitions.
- **Commit keeps admitted signatures.** `cc_kernel_commit_checkpoint` keeps
  new definitions: it roots their values and types, compacts the rest, and
  relocates the survivors (`kernel/src/checkpoint.c`). A signature admitted
  since the checkpoint is kept the same way: its former type, parameter types
  and constructor types are roots of the compaction, and its recorded
  handles are relocated with the definitions'. Commit refuses while a
  signature is open, since the judgements it depends on are truncated.
- An admitted signature is never modified.

### 5.2 Family F1: admission

- `SignatureBegin(former, modifier, sort symbol)`: from a closed judgement
  `⊢ F : U(…)` whose term `F` is `Π (x⃗ < ω). Π (p⃗ : P⃗). U(ℓ)`, open a
  signature. The binder symbols of `F` name the admission context's level and
  parameter entries, and the sort symbol names `s : U(ℓ)`. Returns a
  signature judgement (a new judgement kind, like a composition system).
- `SignatureConstructor(signature, type, symbol)`: from `Γ ⊢ T_k : U(ℓ)`, where
  every entry of `Γ` is a level or parameter entry of the signature (by symbol,
  at an alpha-equal type), the sort entry, or an earlier constructor's entry
  at its recorded type: check the shape and positivity of 1.2–1.5, check that
  `T_k` mentions no level parameter (1.1), and record `c_k`. The universe
  must be exactly `U(ℓ)`, compared by level normal form;
  the driver lifts below it. The check reads the syntax as written, with no
  reduction: a data type written `(λ (X : U(0)). Nat)(s)` mentions `s` and is
  rejected. The driver presents `T_k` with such redexes contracted.
- `SignatureBegin` also checks the former type: every level parameter has a
  determining occurrence (1.1).
- `SignatureClose(signature)`: append the generated squash constructors for
  the modifier, mark it admitted, and return its index. Later instructions
  name an admitted signature by its index, as `Lookup` names a definition.
- With Q16's extension, `SignatureBegin` also requires the former judgement
  to end in its closing prenex, and `SignatureClose` records whether the
  signature is tier-parametric. It walks the judgements 2.3 lists, below
  that prenex, with the three rules of 2.3, and consults the recorded flag
  of each signature the derivation uses. The walk visits each judgement
  once.

The admission context's entries are ordinary entries, made by `Level` and
`Extend`, and the constructor types are derived by ordinary instructions. A
judgement in that context is open in `s` and the constructor entries, so
`Define`, which admits closed judgements only, can never publish one.

**Rejections, each a test:** a former type not of the stated form; a
constructor judgement with a foreign entry, or an entry at another type; a
universe other than `U(ℓ)`; each positivity and shape violation of 1.3 and
1.4, a composition in an endpoint included; data after a position; an
arity mentioning a position; a self or forward reference
(1.5); a level parameter in a constructor type; an undetermined level
parameter; admission while the H1 extension is disabled (5.7);
`SignatureClose` twice; any use of an open signature. With Q16's
extension, tests also check the recorded tier-parametric flag: set for
`Pair`, `Plus`, `Tree`, `Push`, `Trunc` and `Quotient`; clear for `Mixed`,
`Outer`, `Outer2`, `Big` and a signature whose constructor type uses a
definition `F(A : UU0) : U0`.

### 5.3 Family F2: instances and constructors

- `SortBegin(signature)` starts an instance, and `SortParameter(instance, a)`
  adds the next parameter judgement. After the last, the judgement is
  `S(a⃗) : U(ℓ[ρ])`, with `ρ` read as 3.1 describes.
- `Construct(instance, k)` gives `Con(k; I) : T_k[s := I, p⃗ := a⃗, c_m := Con(m; I)]`.
- Applications use `Apply`. Constructors at dimensions use `PathApply` and
  `PathAt`.

**Rejections:** a parameter judgement whose type is not the telescope's
under `ρ`; two occurrences of a level parameter that read different levels;
a read level of tier 1 or above, unless Q16's extension is adopted and
the signature is tier-parametric; a constructor number out of range; a reference to an open
or rolled-back signature.

### 5.4 Family F3: boundary reduction

The existing `Path` step reduces `(c_k …) @ ε` through the application's type
annotation. `Whnf` and `Normalize` reduce it by the signature.

**Tests:** the endpoint of `loop`, `push` and `merid`; the four corners of
`surf` in `Torus`, in both orders; a constructor at `i ∧ j` restricted to
`j = 0`.

### 5.5 Family F4: Kan structure

- `HComp` accepts a system whose family's weak head is a higher sort instance
  and does not use its dimension. It refuses data sorts: they have no formal
  composition (Q1).
- `Trans` accepts higher sort instances, with its existing conditions.
- `Whnf` and `Normalize` implement 3.3–3.5. `Face` handles `hcomp` and
  transport on a face that holds, unchanged.
- The code generalises `inductive_composition.c` (data sorts) and
  `hit_composition.c` (higher sorts) from their fixed formers to signatures.

**Rejections and tests:** `HComp` at a data sort; transport of a data sort by
`Trans`; a composition with a neutral tube in a data sort stays neutral; a
closed transport of `merid(a)` along a nonconstant parameter line reduces to
the corrected `hcomp` of 3.5; the same for the 2-dimensional `set` squash.

### 5.6 Family F5: elimination

- `Eliminator(motive)`: from `M : Π (z : S(a⃗)). U(l')`, where `S(a⃗)` is a
  saturated instance of an admitted sort, open an eliminator judgement.
- `EliminatorClause(eliminator, clause)`: check the next clause against
  `ClauseType_k(M, m_1 … m_{k-1})` (3.6), syntactically, as `NatElim` checks
  its cases.
- `EliminatorClose(eliminator)`: when every constructor, squash included, has
  its clause, give `elim_{M, m⃗} : Π (z : S(a⃗)). M(z)`.
- `Iota` computes a saturated eliminator application on a saturated
  constructor, at dimensions or not (3.7). `Whnf` computes it on `hcomp`.

**Rejections, each a test:** a motive over a non-sort, or over an open
signature; a clause of the wrong type; a path clause whose endpoints are not
the displayed boundary (the "clause that misses its point clauses" of the
design); closing with a missing clause; an extra clause; a squash clause
whose type is not the displayed squash boundary.

### 5.7 Family F6: extension gate and marker

- `cc_kernel_set_extensions(k, flags)` with `CC_EXTENSION_H1`, off by
  default. With it off, `SignatureBegin` refuses. Every other instruction
  works on already admitted signatures, so rollback and inspection are
  unaffected.
- The flag is on in the experimental mode that the work plan describes: the
  tests, the CLI's `--experimental=h1`, and the workbench's matching option.
  Review of section 4 turns it on by default in a separate change.
- The marker is the elaborator's (6.4); the kernel records only which
  signatures were admitted with the flag.

### 5.8 ABI and resources

- `CC_KERNEL_ABI_VERSION` becomes 3: new kinds, and `CC_HCOMP`/`CC_TRANS` with
  new families. The WASM bridge and `kernel-cli` refuse a mismatch.
- The exported function list gains the new instructions and
  `cc_kernel_set_extensions`.
- Limits: constructors per signature, arguments per constructor, arity
  length, cube depth and `d_k` are bounded by checked constants, and every
  check walks types iteratively or within the step budget. Oversized
  signatures are rejected, never truncated.

## 6. K2.3: driver, bridges and serialization

### 6.1 Deriving

- **Admission.** From L2.1's normal form, the driver issues `Level` and
  `Extend` for the parameters and `s`, derives each `T_k` by its ordinary
  derivation, lifts it to `U(ℓ)` when needed, then `SignatureConstructor`,
  and adds the entry `c_k` for the next one. It issues `SignatureClose` last.
  Admission runs inside a declaration transaction.
- **Terms.** Instances derive through `SortBegin` and one `SortParameter` per
  parameter; constructors through `Construct`, `Apply`, `PathApply` and
  `PathAt`. An eliminator derives through `Eliminator`, one
  `EliminatorClause` per clause, `EliminatorClose` and `Apply`. The driver
  makes each clause's type agree with `ClauseType_k` by its usual conversion
  search.
- **Levels at instances.** Where two occurrences of a level parameter would
  read different levels, the driver lifts the lower parameter judgement
  first. It never adds a level to an instance term.
- **Conversion search.** Instances and constructors are rigid heads: equal
  heads compare parameters and arguments by congruence, and different
  constructors are different. An eliminator applied to a constructor takes an `Iota`
  step. A constructor at an endpoint takes a `Path` step. Composition,
  transport and `hcomp` elimination go through `Whnf`, as pushouts do. The
  K1.4 guide answers "different" for distinct constructor heads and "unknown"
  for `hcomp` and transport heads.

### 6.2 Bridges and serialization

- `web/cubical-syntax.mjs`, `web/cubical-kernel.mjs` and
  `lib/cubical/native.mjs` encode and decode the new kinds and the ABI
  version.
- The JavaScript side keeps a record of each admitted signature (its normal
  form in source terms, and its kernel index), so that inspection, workers
  and replay after rollback need no kernel query.
- The renderers (`web/cubical-notation.mjs`, `web/cubical-source-text.mjs`,
  `web/math-notation.mjs`) print sorts, constructors at dimensions and
  eliminators with their clauses.

### 6.3 Transactions and caches

- A failed declaration rolls back its signature, and the JavaScript record
  with it. Driver caches keyed by term handles are dropped on rollback, as
  today.
- Import changes invalidate the signatures they admitted, and everything
  derived from them.

### 6.4 The `kernel extension: H1` marker

- A declaration whose checked term or type mentions a sort, constructor or
  eliminator of a signature admitted in experimental mode carries the marker.
  It propagates through definitions, as non-computing dependencies do, and
  is tracked separately from them.
- `computable def` accepts it. `inspect`, the CLI and the workbench list it
  apart from assumptions. The migration verifier compares it too.
- Tests: direct use; use through a definition; `computable` with the marker
  accepted; `computable` with the marker and `LEM` rejected, naming `LEM`;
  the marker absent once H1 is on by default.

### 6.5 Inspection

The inspector shows a signature's normal form (data, positions with arities
and cubes, dimensions, boundary), the generated eliminator with each clause
type, and each clause's displayed boundary, as the design's section 5 asks.

## 7. K2.4: representation map and differential contract

### 7.1 The declared counterparts

| Native | Declared | Notes |
| --- | --- | --- |
| `Nat`, `zero`, `succ(n)` | `N : U(0)`; `zero`; `succ(n : s)` | |
| `NatRec(M, z, s, n)` | `elim_{M, [z, s]}(n)` | the native step is `Π (n). Π (h : M(n)). M(succ(n))`, the clause type |
| `Sum(A, B)`, `inl`, `inr` | `Plus(A, B)`; `inl(a : A)`, `inr(b : B)` | no level, as native |
| `SumRec(M, l, r, v)` | `elim_{M, [l, r]}(v)` | |
| `W(x : L). B`, `sup(l, c)` | `Tree(L, λ x. B)`; `sup(l : L, c : Π (b : B(l)). s)` | the arity is `(λ x. B)(l)`, one `Beta` from `B[l/x]` |
| `WRec(M, step, v)` | `elim_{M, [step]}(v)` | same clause shape up to that `Beta` |
| `Pushout(C, A, B, m)` and its points and paths | `Push(C, A, B, m)`; `inl`, `inr`, `push(c) : Path(s, inl(fst(m)(c)), inr(snd(m)(c)))` | one maps parameter, as native; `push^r(c)` is `push(c) @ r` |
| `PushElim(M, l, r, b)` | `λ (z). elim_{M, [l, r, b]}(z)` | native is unapplied; `App(PushElim, z)` maps to the saturated eliminator |
| `HComp`, `Trans` at a pushout | the same nodes at `Push` | |

`Unit`, `Void` and their eliminators are not in K2.4's oracle. They may be
declared for comparison; retiring them is a separate decision (Q11).

### 7.2 The translation τ

- τ is a map on terms. Native formers carry no level, and neither do
  declared instances (3.1), so τ adds no level and involves no coercion or
  lifting: `τ(Sum(A, B)) = Plus(τ(A), τ(B))`. τ is the identity on every
  other node.
- **Native and declared forms are not convertible.** `Nat` and `N` are
  different types. No conversion rule, no `Lift` and no coercion relates
  them, and a term mixing them is a type error. Migration is a rewrite by
  τ, checked by the strict migration verifier.
- **Native equalities across universes, at finite levels.** A native term
  used at several universes is one term, and so is its image. In the
  example of 2.3, `small : Nat or Nat` built at `U0` and passed to
  `sum_id(U1, Nat, …)` translates to `small : Plus(N, N)` passed where
  `sum_id`'s parameter type `A or A` has become `Plus(A, A)` with `A := N`.
  The two types are the same term, `Plus(N, N)`, so the application checks,
  as native. A native `Lift` translates to a `Lift` of the image, with the
  same levels.

What τ guarantees depends on Q16, because a native former may occur at an
argument in a tier-1 universe. Call a declaration *finite-tier* when
neither it nor anything it uses, transitively, contains a native sum, W
type or pushout whose instance would read a tier-1 level.

- **With the extension**, the four declared counterparts are
  tier-parametric: their derivations use only their parameters, universes
  at their level parameters, `Π`, `Σ`, projections and path types. τ is
  then purely syntactic and total. It commutes with binders, substitution,
  level substitution and interval substitution everywhere. A native use at
  a tier-1 argument has an image: `def big_sum(A, B : UU0) : UU0 := A or B;`
  becomes `Plus(A, B)`, reading `ω`, in `UU0`.
- **Without it**, the recommended first release, an instance cannot read a
  tier-1 level. τ then keeps each native sum, W type or pushout whose
  instance would read one, and maps every other occurrence; `Nat` has no
  parameters and always maps. Which occurrences stay native depends on the
  levels in the derivation. So τ commutes with substitution only on
  finite-tier declarations, where every level read stays finite before and
  after substitution, and its guarantees are stated for them only:
  - on finite-tier declarations, τ preserves typing and conversion, native
    equalities across universes and `Lift`, as above;
  - a declaration that is not finite-tier keeps its tier-1 occurrences
    native. A *mixed-tier call*, which passes a finite-tier term where a
    native tier-1 type is expected, has no image. For example:

    ```text
    def big_id(A : UU0, x : A or A) : A or A := x;
    def small : Nat or Nat := left(0);
    def call := big_id(Nat, small);
    ```

    `call` checks natively. After τ, `big_id`'s parameter type stays the
    native `A or A`, which becomes `Nat or Nat` with `Nat` mapped to `N`,
    while `small` has type `Plus(N, N)`. The application fails, and the
    migration verifier reports it; it does not migrate the declaration in
    part (X8);
  - no archive or library declaration uses a tier-1 universe as a type:
    all 43 archive mentions of `UU0`, and the library's 4, are universe
    binders `U < UU0`. So every existing declaration is finite-tier, and
    no mixed-tier call exists.

Under either option, X1–X3 test the preservation rule by rule, and X4, X6,
X7 and X8 test it on the archive and on the examples above.

### 7.3 Differential fixtures

| ID | Comparison | Pass condition |
| --- | --- | --- |
| X1 | Every `Nat`, sum, W and pushout case of `kernel/tests/test_instructions.c`, replayed through τ with the declared signatures | Same verdict; accepted types related by τ, up to the W arity's `Beta` |
| X2 | Weak head and normal forms of the terms those cases derive, and of each archive definition's value | `τ(nf(t))` is alpha-equal to `nf(τ(t))`, up to that `Beta` |
| X3 | Composition, homogeneous composition and transport at each type, including pushout bridges | Reducts related by τ |
| X4 | The archive, elaborated with declared forms for the four types (a driver option) | 0 gaps; every stored definition derives again; each declaration's assumptions unchanged; canonicity fixture and `evaluate` results equal |
| X5 | Cost of X4 against the native run: archive check time, re-derivation time, kernel steps, arena peak | Recorded with revision, machine and limits |
| X6 | Native terms used at two finite universes: `sum_id(U1, Nat, small)` of 2.3, and the same with W, pushout and `Nat`-valued generic definitions instantiated at `U2` | Under both options, native and image both check; the image is one instance term at both universes |
| X7 | Native formers at UU-tier arguments: `big_sum`, and a W type and a pushout over types in `UU0` | Without Q16's extension, τ leaves them native and they check unchanged; with it, native and image both check and the image lives in `UU0` |
| X8 | A mixed-tier call: `big_id(Nat, small)` of 7.2, and the same through a W type and a pushout | Without Q16's extension, the image fails to check and the migration verifier rejects the declaration, naming the call; with it, native and image both check |

### 7.4 Retirement criterion

The hand-coded instructions retire in one change when:

1. X1–X4 and X6–X8 pass;
2. X5's gap is recorded, and either accepted by the maintainer or closed by
   specialised reduction paths for hot signatures (Q14);
3. the archive is migrated by τ under the strict verifier, with every
   public type equal after τ and every assumption list unchanged. Without
   Q16's extension, this requires every archive declaration to be
   finite-tier (7.2), which they all are today; a declaration that is not
   is left on native formers and reported, not migrated in part.

What the change removes depends on Q16:

- *With the extension*, it removes `Nat`, `Zero`, `Succ`, `NatElim`, `Sum`,
  `Inject`, `SumElim`, `W`, `Sup`, `WElim`, `Pushout`, `PushPoint`,
  `PushPath` and `PushElim`, and their node kinds. The tags stay reserved,
  and the ABI version changes.
- *Without it*, it removes the `Nat` instructions only. The sum, W and
  pushout instructions stay for arguments at tier-1 levels, and the
  elaborator emits the declared forms everywhere else. They stay trusted
  code, and X1–X3 stay as their regression tests. A native and a declared
  sum of the same components are then different types, so τ's guarantees
  cover finite-tier declarations only, and a mixed-tier call has no image
  (7.2, X8). Nothing does that today. Adopting the extension later retires
  the three formers without changing any finite-level term.

`Unit` and `Void` stay in both cases (Q11).

## 8. K2.5: truncation and resizing (G2)

### 8.1 Native truncation and quotients

```text
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
inductive Quotient(U, V < UU0, A : U, R : A -> A -> V) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}
```

- `Trunc(A) : U(x)` for `A : U(x)`, universe-preserving by 2.1, at every
  finite level. `Trunc` is tier-parametric, so with Q16's extension this
  holds at every tier too (2.3). The instance carries no level of its own.
- `Quotient(A, R) : U(max(x, y))` for `A : U(x)` and `R : A → A → U(y)`: its
  level accounts for the carrier and the relation. A small quotient stays
  small, without the archive's predicate encoding.
- The eliminator into any universe replaces `TruncateElim`, which the archive
  restricts to propositions in the argument's universe. The largest group of
  the archive's resizing, 22 of 47 declarations, works around that
  restriction (8.3, 8.4).
- Truncation readout by `evaluate` (L2.9b) reads the witness off `point(w)`
  under formal compositions. It is a closed evaluation tool, not an
  eliminator into `A`.

### 8.2 Policy

1. **No resizing in the rebuilt foundation.** The rebuilt library states
   each result at the universe it needs. Implicit downward resizing is
   rejected: for `A : U(1)`, `Trunc(A) : U(0)` is not derivable (acceptance
   G1).
2. **A resizing assumption only by name.** If a rebuilt result genuinely
   needs resizing, it uses an assumption named `PropResizing`, reported as a
   non-computing dependency like `LEM`. The ledger below finds no such need
   in the archive.
3. **Resizing from `LEM` where `LEM` is already present.** Excluded middle at
   `U(ℓ + 1)` makes every proposition of `U(ℓ + 1)` equivalent to one of
   `U(ℓ)` (HoTT book, Exercise 3.10). A declaration that already depends on
   `LEM` may resize through it. That adds no assumption, and the declaration
   never computed anyway. It resizes propositions only. A type that carries
   a witness, such as `StrictlyAbove(A, le, x)`, a Σ type over `A : U1`, is
   not resized; its truncation, a proposition, may be.
4. **Legacy assumptions stay for the archive.** `Truncate`, `TruncateIntro`,
   `TruncateProp`, `TruncateElim`, `LEM` and `Choice` keep their generic
   signatures (G0 Q5) while any archived module uses them. The archive keeps
   checking unchanged.
5. **`LEM` and `Choice` are restated over `Trunc`** when the rebuilt library
   adopts it. They remain non-computing assumptions.
6. **The ordinary migration check stays strict.** Intentional changes of
   public universes, hypotheses or assumption lists are allowed only through
   the ledger of 8.5.

### 8.3 Measurements

Measured on 2026-09-27 at `d44239e`, checking all 365 archive modules. Each
declaration's non-computing dependencies are read from the checked program,
as `inspect` prints them.

| Measure | Count |
| --- | --- |
| Archive declarations | 3,804, all checked |
| Depending on a truncation assumption | 1,266 |
| of which also `LEM` | 455 |
| of which also `Choice` | 3 |
| of which truncation only | 810 |
| With no assumption | 2,538 |
| Modules with a truncation-dependent declaration | 215 |

These agree with the kernel roadmap's count of 2026-09-25 (1,266, 455 and 3).
Every `LEM` or `Choice` dependency also depends on `Truncate`, because their
statements mention it.

**Direct uses.** Six archive modules name the truncation assumptions. Two of
them define wrappers that the rest use:

| Wrapper module | Definitions | Universes | Users |
| --- | --- | --- | --- |
| `truncation` | `Mere`, `merely`, `mere_is_prop`, `mere_eliminate`, `mere_map` | `Truncate(U0, A)`: already universe-preserving | 77 modules, itself included |
| `field_logic` | `FieldExists`, `field_exists_intro`, `field_exists_prop`, `field_exists_elim`, `field_exists_map`, `FieldOr` | `Truncate(U1, A) : U0`: the archive's one resizing wrapper | 35 modules, itself included |

The other four (`independent_extension`, `linear_span`, `span_subspace`,
`vector_subspaces`) use `Truncate(U0, …)` directly and need no resizing.

**Resizing, measured.** Changing `Truncate`'s type in
`web/cubical-assumptions.mjs` to the universe-preserving `Π (A : U(x)). U(x)`
and checking the archive again fails 47 declarations in 20 modules, and no
others. Eight fail directly; 39 fail only through them.

| Root | Module | Why it fails | Dependents | `LEM`; `Choice` |
| --- | --- | --- | --- | --- |
| `small_mere_eliminate` | `field_logic` | Its proof eliminates `Truncate(U0, A)` into `FieldExists(P) : U0` for `P : U1`, which needs `FieldExists(P)` small | 21, in 10 other modules | 5; 0 |
| `predicate_union_upper`, `predicate_union_least` | `predicate_chains` | `PredicateUnion(I : U1, A, P, x) := FieldExists(exists i : I. P(i, x))` is a predicate `A → U0` only by resizing: the union of a large family | 0 | 0; 0 |
| `directed_union_independent` | `independent_unions` | Uses `PredicateUnion` as a small predicate | 5 | 0; 0 |
| `tower_induction_large` | `bourbaki_tower` | `TowerMember` is `FieldExists(forall P : A → U0. …)`: impredicative, since it quantifies over all small predicates on `A : U1`. `FieldExists(P(y))` must be a small predicate | 8 | 7; 0 |
| `no_maximal_strict_successor` | `zorn_chain_complete` | `FieldExists(StrictlyAbove(A, le, x))`, a proposition about `A : U1`, used at `U0` | 2 | 3; 2 |
| `CauchyQuotient`, `cauchy_same_equivalence` | `cauchy_quotient` | `EventualClose` truncates a small proposition, over `Nat` and `Q : U0`, with `FieldExists`, whose universe argument is fixed at `U1`. So `CauchySame` becomes a relation into `U1`, where the predicate-encoded `SetQuotient` needs `U0` | 3 | 0; 0 |

The dependents column counts declarations whose first failed dependency leads
to that root; the `LEM` and `Choice` column counts the root's whole group. Of
the 47, 32 depend on truncation only, 15 also on `LEM`, and 2 also on
`Choice`.

The rebuilt `library/` needs no resizing: its 38 declarations, 9 of them
truncation-dependent, all check with the universe-preserving signature.

### 8.4 The ledger's remedies

The 47 declarations fall into seven groups by remedy. None needs a resizing
assumption.

A remedy that only raises a universe does not work where a large object
must itself be small. Two groups have that shape. The Bourbaki–Witt tower
quantifies over all small predicates on `A : U1`. Quantifying over
`A → U1` instead puts membership in `U2`, and the tower's uses then need
`A → U2`, with no fixed point. Likewise, the union of a large chain of
small independent sets is large, and a poset of larger sets has larger
chains. Those groups take a different remedy.

| Group | Declarations | Remedy | Public change | Assumptions |
| --- | --- | --- | --- | --- |
| 1 | `small_mere_eliminate` and its 21 dependents | Eliminate `Trunc(A)` directly into `P : U1`: the native eliminator's motive may land in any universe | None | None added |
| 2 | `CauchyQuotient`, `cauchy_same_equivalence` and 3 dependents | Truncate the small proposition in `EventualClose` at its own universe, as `truncation.Mere` does. `CauchySame` stays a relation into `U0` | None | None added |
| 3 | `predicate_union_upper`, `predicate_union_least`, `directed_union_independent`, `chain_union_independent` | State inclusion, unions and independence for predicates at a universe variable, `A → U` with `U < UU0`, with the union one universe up. These lemmas only relate a union to its members | `PredicateUnion(I, A, P) : A → U1`; the lemmas generic over the predicates' universe | None added |
| 4 | `IndependentUnion`, `independent_union_upper`, `independent_union_least`, `independent_chain_complete` | `IndependentSubset(K, V)` is a Σ type whose witness is a small predicate `P : V → U0`. These declarations build that witness for a union, `v ↦ ∃ i : I. P_i(v)`, whose values are truncated propositions in `U1`. The witness type stays as it is. What must be small is each value, a proposition. Take, as an explicit hypothesis, a `U0` proposition equivalent to each. Their one consumer, `vector_space_has_basis`, already depends on `LEM` and `Choice`, and discharges it by resizing those propositions through `LEM` (8.2, item 3) | One added hypothesis each | None added; `LEM` stays in the consumer only |
| 5 | `tower_induction_large`, `tower_relative_induction` | Wait for H2. Define the tower as an indexed inductive family `Tower : A → prop`, generated by the step and chain-supremum closure. Its eliminator into any universe proves both, predicatively, with no resizing and no assumption | `TowerMember : A → U1`, since the index type `A : U1` counts (G0 2.12). `tower_member_prop`, `tower_contains`, `tower_step`, `tower_sup`, `TowerStable` and `tower_stable_prop` in `bourbaki_tower` are restated over `Tower`. The two wait for H2 | None added |
| 6 | `bourbaki_witt`, `tower_is_chain`, `tower_is_stable`, `tower_separation`, `tower_stable_step`, `tower_stable_sup`, `no_strict_successor_function` | They use the tower as a small chain, since `ChainComplete` supplies suprema of small chains only. Tower membership is a truncation, so each value is a proposition in `U1`. They already depend on `LEM`: resize those propositions through it. Where they use `tower_relative_induction`, its motive is a family of propositions (`FieldProp(P(x))`); resize it the same way and use the small induction `tower_contains`, so they do not wait for group 5. `no_strict_successor_function` keeps its hypothesis `forall x : A. StrictlyAbove(A, le, x)`: a family of witness types, which is not resized | None | None added |
| 7 | `no_maximal_strict_successor`, `zorn_chain_complete`, `vector_space_has_basis` | No resizing is needed. They fail because `double_negation` is stated for `P : U0` and uses `LEM(U0)`, while the propositions they apply it to, `FieldExists(StrictlyAbove(A, le, x))` and `FieldExists(exists x : A. OrderMaximal(A, le, x))`, are now truncations in `U1`. Apply double-negation elimination at `U1` instead, through the generic `LEM(U1, …)`. The witness family `StrictlyAbove(A, le) : A → U1` stays as it is, since `Choice(U1, …)` needs it as a family of sets; so does the witness type `exists x : A. OrderMaximal(A, le, x)`. `vector_space_has_basis` also discharges group 4's hypothesis, resizing propositions through `LEM` | The truncated propositions live in `U1`; their text is unchanged | None added |

In total, of the 47:

| Remedy | Declarations |
| --- | --- |
| A new proof only | 22 |
| Truncation at the proposition's own universe | 5 |
| Generic restatement, the union one universe up | 4 |
| An explicit smallness hypothesis | 4 |
| Resizing propositions through the `LEM` they already use | 7 |
| Double negation at `U1` through the `LEM` they already use | 3 |
| Waiting for H2's indexed families | 2 |

Group 5 is the only place where H1 alone does not suffice.

Group 7's remedy was checked on the archive. A `double_negation_large` at
`U1`, proved from `LEM(U1, …)` and `TruncateElim`, replaced
`double_negation` in `no_maximal_strict_successor` and `zorn_chain_complete`.
With the universe-preserving `Truncate`, `no_maximal_strict_successor` then
checks, with the assumptions it had before. `zorn_chain_complete` and
`vector_space_has_basis` then fail only through groups 6 and 4. This was a
local experiment; the archive is unchanged.

### 8.5 Ledger format and verifier (K2.5 implementation)

- A reviewed ledger file lists each intentional change: module, declaration,
  old public type, new public type, hypotheses added, assumptions removed,
  assumptions retained, and the remedy group of 8.4.
- When a module migrates from the legacy assumptions to `Trunc`, the
  migration verifier accepts a changed public type or assumption list only
  for a declaration listed with exactly that change. Every other change
  fails, as today.
- Removing `Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim`
  from a declaration's dependencies is recorded, not assumed: the verifier
  checks that the new list is the old one minus those four.
- The legacy assumptions are removed from `web/cubical-assumptions.mjs` only
  when no module that the tests check uses them.

## 9. L2.1: the lowering contract

L2.1 turns `inductive` declarations
([proposal](inductive-language-features.md), design §5) into the normal
form. It is untrusted; the kernel checks the result.

- **Header.** `inductive T(U < UU0, …, A : U, …) : m` gives the former type,
  with `m` among `type` (the default), `set` and `prop`. The level `ℓ` is
  the least level of 2.1, from the inferred types of the data and arities.
- **Constructors.** An argument whose type mentions `T` or a position is a
  position, and must be a cube over `T` (1.2); otherwise it is rejected,
  naming the argument. The rest are data, moved ahead of the positions in
  their source order.
- **Results.** `: T` or no result type is a point constructor. `: x = y` is
  a path constructor with that boundary. A square uses `PathP`, or the
  `cell` syntax of L2.8. The endpoints must be constructor expressions.
- **Errors** name the offending argument: `T` in negative position, a use
  before declaration, a composition in a boundary, or a boundary face that
  disagrees, shown with both sides.
- **Uses.** `Trunc(U, A)`, with an explicit universe argument as in L1.1,
  checks `A : U` and elaborates to the instance `Trunc(A)`, which carries no
  level. A header whose constructor types would mention a universe parameter
  is rejected as level-dependent (Q15), naming the argument.
- **Generated names.** `T.squash` for the modifier's constructor; the
  eliminator is reached through `match` (L2.2), and `T.rec` and
  `T.ind_prop` are L2.3's.

## 10. Acceptance cases

Tests name cases by ID, as `H1.A3`. "Kernel" cases are issued directly in
`kernel/tests/test_instructions.c`; "source" cases go through the elaborator
and the driver, with L2.1. All run with the H1 extension on, except T1.

### 10.1 Admission

| ID | Case | Verdict | Reason |
| --- | --- | --- | --- |
| A1 | `N`, `List`, `W`, `Push`, `Susp`, `S1` of 1.8 | Accept | Normal form |
| A2 | `Torus`, and `S2` with outer endpoints `⟨j⟩ base` | Accept | Two dimensions; corners agree by typing; path abstraction in endpoints (1.4) |
| A3 | `Trunc` (`prop`) and `Quotient` (`set`) | Accept | Generated squash constructors of 1.6 |
| A4 | `bad(f : s → Nat) : s` | Reject | `s` in data |
| A5 | `bad(f : (s → Nat) → s) : s` | Reject | `s` in an arity |
| A6 | `bad(g : Nat → (s → s)) : s` | Reject | `s` under a function inside a cube |
| A7 | `c(n : Nat) : Path(s, c(n), c(n))` | Reject | Self reference |
| A8 | a boundary naming a later constructor | Reject | Forward reference |
| A9 | `c(x : s) : Path(s, hcomp(…), x)` | Reject | Composition in a boundary (Q3) |
| A10 | a square whose inner endpoints do not meet the outer ones at a corner | Reject | The path type cannot be formed |
| A11 | kernel: `c : Π (x : s). Π (n : Nat). s`; source: `c(x : T, n : Nat)` | Reject; Accept as `c(n : Nat, x : T)` | The kernel requires data first; L2.1 reorders (1.2) |
| A12 | a data argument `(λ (z : s). zero)(x)` in a boundary | Reject | A data term may not mention `s` or a position |
| A13 | `SignatureConstructor` with a foreign entry, or with `s` at another universe | Reject | Admission context |
| A14 | `SignatureClose` twice; `Construct` on an open signature | Reject | Signature state |
| A15 | infinitary: `Cantor { leaf; node(f : Nat → s); squash … : set }` | Accept | D5 |
| A16 | a positional argument of path type given as `⟨i⟩ c_1 @ i` | Accept | Path abstraction as a positional argument (1.4) |

### 10.2 Universes and substitution

| ID | Case | Verdict | Reason |
| --- | --- | --- | --- |
| V1 | `x < ω, A : U(x) ⊢ Trunc(A) : U(x)`; the same at `U(x + 1)` by `Lift` | Accept; Accept | Universe-preserving |
| V2 | `Box(A) : U(0)` for `A : U(x)`, every `x` (2.2) | Accept | Phantom parameter |
| V3 | `Pair(A, B) : U(max(x, y))`; `: U(x)` | Accept; Reject | Stored data |
| V4 | `Tree(L, B) : U(max(x, y))` | Accept | Arity counts |
| V5 | `Quotient(A, R) : U(max(x, y))`; `: U(x)` | Accept; Reject | The relation counts |
| V6 | `Small(x < ω, A : U(x)) : U(0) { wrap(a : A); }` | Reject | Lowering |
| V7 | source: `sum_id`, `small` and `lifted` of 2.3 with a declared sum; the same with `point(a)` passed to a generic definition at `U1` | Accept both | One instance term at every universe (Q8) |
| V8 | `Trunc(A)` and `Pair(A, B)` for `A, B : UU0` | Reject; with Q16's extension, Accept, in `UU0` | A tier-1 read level; tier-parametric signatures under the extension (2.3) |
| V9 | the elaborator's `fun (U < UU0, A : U) => Trunc(A) : Π (x < ω). Π (A : U(x)). U(x)`, in `U(ω)` | Accept | A declared type used as a function |
| V10 | `Big(A : UU0) { wrap(a : A); } : UU0`; its eliminator into `UU1` | Accept | Fixed tier-1 signature; any motive universe |
| V11 | instantiating a generic definition that mentions `Trunc(A)` at `x + 1`, and reducing `elim` on `point` | Accept | Level substitution leaves the instance unchanged (2.4) |
| V12 | `Wrap(x < ω) : U(x + 1) { wrap(B : U(x)); }` | Reject | Level-dependent (Q15) |
| V13 | `Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); }`; `Mixed(A, B)` for `A : U(3)`; for `A : UU0` | Accept, not tier-parametric; Accept; Reject | A tier-1 constant bounds the instances to finite levels (Q16) |
| V14 | a level parameter that ends no parameter's type | Reject | Undetermined (1.1) |
| V15 | `Both(x < ω, A, B : U(x)) { mk(a : A, b : B); }` at `A : U(0)` and `B : U(1)`; the same after lifting `A` to `U(1)` | Reject; Accept | Conflicting reads of one level parameter (3.1) |
| V16 | `(λ (x < ω). Trunc(U(x))) {0}` and its `Beta` reduct `Trunc(U(0))`; `point(Nat)` at both; an eliminator of `Trunc(U(x))` with motive into `U(x + 1)`, instantiated at `0` | Accept; convertible; Accept; the motive lands in `U(1)` | Level substitution recurses through parameters and motives (2.4) |
| V17 | `Tag(A : UU0) : U0 { here; }` and `Outer(x < ω, A : U(x)) : U0 { wrap(t : Tag(A)); }`; `Outer(Nat)`; `Outer(UU0)`; `Outer(A)` for `A : UU0` | Accept, and not tier-parametric under the extension (rules 2 and 3); Accept; Reject; Reject | A bound hidden in a referenced signature's parameter type (2.3) |
| V18 | a signature whose constructor type uses a definition `F(A : UU0) : U0`, as in `wrap(t : F(A))`, at `A : UU0` | Reject at the instance; not tier-parametric under the extension (rule 2) | A bound hidden in a definition's type (2.3) |
| V19 | `Big : UU1 { pack(B : UU0); }` and `Outer2(x < ω, A : U(x), F : Big → U0) : U0 { wrap(t : F(pack(A))); }`; `Outer2(Nat, F)`; `Outer2(UU0, F)`; `Outer2(A, F)` for `A : UU0` | Accept both, neither tier-parametric under the extension (rules 2 and 3); Accept; Reject; Reject | A bound hidden in a parameter-free signature's constructor type (2.3) |

### 10.3 Constructors and boundaries

| ID | Case | Verdict |
| --- | --- | --- |
| N1 | `loop @ 0 ≡ base`, `loop @ 1 ≡ base` by `Path` steps and by `Whnf` | Accept |
| N2 | `push(c) @ 0 ≡ inl(fst(m)(c))` | Accept |
| N3 | in `Torus`, `surf @ i @ 0 ≡ p @ i`, `surf @ 0 @ j ≡ q @ j`, and each corner `≡ b` in both orders | Accept |
| N4 | `loop @ (i ∧ j)` restricted to `j = 0` `≡ base` | Accept |
| N5 | `loop ≡ ⟨i⟩ loop @ i` | Accept (path eta) |
| N6 | `base ≡ loop @ i` | Reject |

### 10.4 Kan structure

| ID | Case | Verdict or value |
| --- | --- | --- |
| K1 | composition in `N` with `succ` base and tubes pushes, as native | Reduces to `succ(comp …)` |
| K2 | composition in `Plus` with an `inl` base and a neutral tube | Neutral |
| K3 | `HComp` at `N` | Reject: no formal composition for data sorts |
| K4 | `hcomp` in `S1` with a tube on a face that holds | `Face` gives the tube at 1 |
| K5 | transport of `point(a)` in `Trunc(A(i))` along a line of types | `point(transp a)` |
| K6 | transport of `merid(a) @ r` in `Susp(A(i))` along `ua` of a closed equivalence | The `hcomp` of 3.5; its faces reduce to the transported poles |
| K7 | transport of the `set` squash of `Quotient` along a line in the carrier | The 2-dimensional correction of 3.5, with walls agreeing at the corners |
| K8 | transport of an `hcomp` | Commutes (3.5, case 3) |
| K9 | composition in `S1` along a constant line | `hcomp` of the transported base |
| K10 | property test: for random closed constructor terms of `Susp`, `Torus` and `Quotient` and random parameter lines, `(transp u)[r_l = ε] ≡ transp(u[r_l = ε])` | Holds (Lemma H2) |
| K11 | property test: transport along a constant line then at `φ = 1` is the identity | Holds (`Face`) |

### 10.5 Elimination

| ID | Case | Verdict or value |
| --- | --- | --- |
| E1 | the circle's code by `S1`'s eliminator into `U(0)`, with `ua` of the successor equivalence | `winding(loop) = 1` by `rfl` |
| E2 | `code_meridian`: `cong(rec, merid(a))` for a declared `Susp` recursion | `= h(a)` by `rfl` |
| E3 | `Trunc`'s eliminator into a family of propositions, with the squash clause | Accept; computes on `point` |
| E4 | `Quotient`'s dependent eliminator into a family of sets | Accept; computes on `class` and on `glue(a, b, r) @ i` |
| E5 | eliminator on an `hcomp` | Reduces to composition in the motive |
| E6 | a clause of the wrong type | Reject |
| E7 | a `loop` clause whose endpoints are not the `base` clause | Reject |
| E8 | a missing clause; an extra clause; a `prop` sort eliminated without its squash clause | Reject all |
| E9 | a motive over `Trunc(A)` used on `Trunc(B)` for a different `B` | Reject |
| E10 | a motive into `UU0` for `S1` | Accept |

### 10.6 Trust controls

| ID | Case | Verdict |
| --- | --- | --- |
| T1 | `SignatureBegin` with the extension off | Reject |
| T2 | a definition using `S1` carries `kernel extension: H1`; one using that definition carries it too | Accept, marker listed |
| T3 | `computable def` using `S1` | Accept |
| T4 | `computable def` using `S1` and `LEM` | Reject, naming `LEM` only |
| T5 | rollback after admission: the signature, its instances and its JavaScript record are gone; a later admission reuses nothing | Accept |
| T6 | commit after admission: the signature survives, its recorded types are relocated, and instances formed after the commit check and compute | Accept |
| T7 | commit while a signature is open | Refused |

### 10.7 Truncation policy

| ID | Case | Verdict |
| --- | --- | --- |
| G1 | `Trunc(A) : U(0)` for `A : U(1)` | Reject: no downward resizing |
| G2 | `small_mere_eliminate`'s statement proved with `Trunc`'s eliminator into `U(1)` | Accept, with no assumption |
| G5 | `CauchySame` with `EventualClose` truncating at `U0` | A relation into `U0`, with no assumption (8.4, group 2) |
| G6 | propositional resizing from `LEM` at `U1`, as 8.2 item 3 uses it, of a proposition; the same applied to `StrictlyAbove(A, le, x)`, which carries a witness | Accept, depending on `LEM` only; Reject |
| G7 | `no_maximal_strict_successor` with double negation at `U1` (8.4, group 7) | Accept, with its previous assumptions |
| G3 | the archive with its legacy assumptions after H1 lands | Unchanged: 3,804 declarations, 0 gaps |
| G4 | the migration verifier on a ledger-listed change, and on the same change unlisted | Accept; Reject |

### 10.8 Release fixtures

The work plan's H1 release fixtures, each in the canonicity fixture or its
support module where it computes:

- the declared `N`, `List`, `Tree` and `Push` compared with the native forms
  (X1–X4, X6–X8);
- a declared circle with winding number 1, by `rfl` and by `evaluate` (E1);
- `code_meridian` by `rfl` (E2);
- `Trunc` and `Quotient` with checked dependent elimination (E3, E4);
- the rejections of A4–A12 and E6–E8. Nonstructural recursion and missing
  h-level proofs are L2.2's rejections, not the kernel's.

### 10.9 Resources and malformed input

| ID | Input | Verdict |
| --- | --- | --- |
| R1 | malformed `CC_SORT`, `CC_CON`, `CC_ELIM` or `CC_LIST` nodes; indices out of range | Reject; inspection stays inert |
| R2 | a signature at the constructor or argument limit, and one above it | Accept; Reject |
| R3 | a constructor with cube depth 8 and arity 64 | Accept within budget |
| R4 | a client with ABI version 2 | Refused |
| R5 | an encode and decode round trip of every new kind | Identical handles |

## 11. Open questions

| Question | Recommendation |
| --- | --- |
| Q1. Formal composition for data sorts | None |
| Q2. Heterogeneous formal composition along parameter lines | No; Coquand–Huber–Mörtberg's split |
| Q3. What boundaries may contain | Constructor expressions only |
| Q4. Partial boundaries | Not in H1 |
| Q5. How constructors take dimensions | Path-valued constructors |
| Q6. The eliminator's form | A function node with every clause |
| Q7. Who computes the sort's level | Declared, checked as a bound; the elaborator declares the least |
| Q8. Level irrelevance across instances | Yes, by level-erased instances of level-parametric signatures, at finite levels; tier-1 levels are Q16's (revised twice) |
| Q9. Cube and infinitary positions in higher sorts | Admit both |
| Q10. Are signatures generative | Yes |
| Q11. `Unit` and `Void` | Keep native |
| Q12. Resizing | No resizing assumption; the seven remedy groups of 8.4 (revised) |
| Q13. Where the experimental gate lives | In the kernel |
| Q14. Specialised reduction after retirement | Decide from X5 |
| Q15. Level-dependent signatures | Excluded from H1 (new) |
| Q16. Instances at tier-1 levels | Finite levels only in the first release; the tier-parametric extension later (revised twice) |
| Q17. Declarations that assert a large proposition is small | A hypothesis, `LEM` where present, or H2's inductive tower (new) |

**Q1. Formal composition for data sorts.** The design gives every sort one
formal composition that pushes through constructors when it can. A formal
element that also pushes is not confluent with its eliminator, and whether
it pushes changes under substitution (4.3, D2). *Recommended:* data sorts
have no formal composition; composition pushes through equal heads and is
otherwise neutral, exactly as `Nat`, sums and W types compute today, which
keeps K2.4's comparison exact.

**Q2. Heterogeneous formal composition along parameters.** The design's
`fcomp` runs along a line of parameters and indices. With parameters only,
the eliminator's motive is over the sort at fixed parameters, so an `fcomp`
joining two parameter values could not be eliminated. *Recommended:* H1 uses
formal `hcomp` at fixed parameters and computes transport, as
Coquand–Huber–Mörtberg and the kernel's pushouts do. The heterogeneous form
returns in H2 along index lines, where the motive ranges over indices.

**Q3. What boundaries may contain.** The design allows formal compositions
in boundaries. No H1 example needs them. With constructor expressions only,
clause types follow by substitution (Lemma H1), and the correction walls of
3.5 need no composition in the boundary. *Recommended:* constructor
expressions only; revisit with a concrete use.

**Q4. Partial boundaries.** A boundary on some faces only, such as
`c(i) [i = 0 ↦ a]`, would need cubical extension types in the kernel, which
it lacks. *Recommended:* cube boundaries only. Every example of 1.8 has one.

**Q5. How constructors take dimensions.** The alternative is a node carrying
`d` interval formulas, as `PushPath` carries one. *Recommended:* path-valued
constructors. Boundary reduction is then the existing path step, overlap
agreement is typing, and the driver reuses its path handling.

**Q6. The eliminator's form.** Native `NatRec` is saturated with its value;
`PushElim` is a function. *Recommended:* a function node carrying the motive
and every clause, applied by `Apply`, with `Iota` on the saturated form. A
level-quantified constant cannot serve, because the motive's universe must
range over UU tiers too (2.4).

**Q7. Who computes the sort's level.** The kernel cannot infer principal
levels, so it cannot check a maximum. *Recommended:* the former's type
declares `ℓ`; the kernel checks that every constructor type lives in `U(ℓ)`,
which bounds every data type and arity; the elaborator declares the least
level. The alternative, a kernel-computed level, would need principal-level
inference in the kernel.

**Q8. Level irrelevance across instances.** G0 decided that instances of a
generic type at different levels are distinct (G0 Q1), and asked to
revisit at H1. The first draft kept that. Review showed it cannot stand for
the types K2.4 replaces. The native formers carry no level, and a generic
definition instantiated at `U1` accepts a sum built at `U0` (2.3). Distinct
declared instances could not translate that without coercions that break
definitional equalities. *Recommended:* yes, by construction. Instances of
a level-parametric signature carry no level of their own, so they are one
term at every universe. Their read levels stay within the finite range the
admission checked. Tier-1 levels are refused in the first release. Q16's
extension would let tier-parametric signatures read them, with a check on
the admission derivation, because a bound can hide in a referenced
signature, definition or constructor (2.3, `Outer` and `Outer2`). D9 argues soundness, which is Timany and Sozeau's
condition for cumulative inductive types. G0 Q1's rule stays for generic
definitions and assumptions, which are not signatures.

**Q9. Cube and infinitary positions.** The `set` squash needs path
positions, and W-like constructors in higher sorts need infinitary ones.
*Recommended:* admit both (D4, D5).

**Q10. Are signatures generative.** Two textually identical declarations
could be one type or two. *Recommended:* generative: each admission is a new
sort, as each definition is a new constant. Identification is a theorem.

**Q11. `Unit` and `Void`.** They are not in K2.4's oracle list.
*Recommended:* keep them native. Declaring them for comparison is allowed,
and retiring them is a later, separate decision.

**Q12. Resizing.** The first draft proposed raising universes for the tower
and the unions. Review showed the tower's remedy cannot close: quantifying
over `A → U1` puts membership in `U2`. The union of independent sets has
the same shape. The measured roots now have the seven remedy groups of 8.4,
none a resizing assumption. *Recommended:* no resizing assumption in the
rebuilt foundation. Apply 8.4 when those areas are rebuilt. `PropResizing`
stays unused unless a rebuilt result proves to need it.

**Q13. Where the experimental gate lives.** In the elaborator only, or in the
kernel too. *Recommended:* in the kernel, so no client can admit a signature
by accident before review.

**Q14. Specialised reduction after retirement.** Generic reduction may be
slower than the hand-coded rules (design open question 4). *Recommended:*
decide from X5's measurements; specialised paths, if any, must be observably
identical to the generic rules and tested against them.

**Q15. Level-dependent signatures.** A signature whose constructor types
mention a level parameter, such as `wrap(B : U(x))`, stores types of that
level. Its instances at different levels are different types, so they
would need explicit level arguments and G0 Q1's distinct instances. No H1
example, and none of K2.4's types, is level-dependent. *Recommended:*
exclude them from H1. Stating such a type at fixed levels remains possible.
Revisit with a concrete use, together with how explicit and erased
instances would coexist.

**Q16. Instances at tier-1 levels.** Admission checks a signature at finite
levels only, so reading a tier-1 level needs more. Two syntactic criteria
have failed review. The first allowed every signature without a tier-1
constant, and `Outer` hid a bound in `Tag(A : UU0)`. The second allowed a
syntactic class, and `Outer2` hid one in the constructor of the
parameter-free `Big`. Both bounds hide in a type the signature uses, not
in its text. The options:

- **The extension (2.3).** Tier-parametric signatures read every tier. The
  kernel checks the admission derivation itself: no level-quantification
  instruction, no tier-1 level in any judgement, and only tier-parametric
  signatures used. Sufficiency is proved in outline by induction on the
  derivation. It costs a walk of each admission derivation, a flag per
  signature, and a review item for every instruction family: its
  classification into the induction's cases.
- **The conservative alternative.** No tier-parametric class. Instances
  read finite levels only. The native sums, W types and pushouts stay for
  arguments at tier-1 levels, and K2.4 retires only the `Nat` instructions;
  the elaborator emits declared forms at finite levels (7.2, 7.4). It
  costs three hand-coded formers kept as trusted code, with their
  differential tests as regressions, and a native and a declared sum of the
  same components are different types. That difference shows only when a
  definition with a parameter typed at a tier-1 universe is applied to
  small types. Today it costs nothing observable: no archive or library
  declaration uses a tier-1 universe as a type.

*Recommended:* the conservative alternative for H1's first release, with the
extension kept specified as a later proposal. It adds no trusted check,
and nothing today needs tier-1 instances. It is forward-compatible: adopting
the extension later only accepts more instances and retires the three
formers, without changing any finite-level term. The extension becomes
worth its review when a rebuilt result needs a declared type at `UU0`,
for example through the E2 proposal. A tier-1 constant stays allowed in
any signature under either option; it makes the signature bounded
(`Mixed`, V13).

**Q17. Declarations that assert a large proposition is small.** Groups 4
and 5 of 8.4 state that the union of a large family, or the impredicatively
defined tower, is small. No universe choice makes that true predicatively.
*Recommended:* for the tower, the predicative construction: an indexed
inductive family at H2, with the two declarations waiting for it. For the
unions, an explicit smallness hypothesis, discharged from `LEM` by the one
consumer that already uses it. The alternative for both, proving the
statement from `LEM` directly, would add `LEM` to declarations that do not
use it today.
