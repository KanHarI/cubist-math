# One-sort signatures (H1): rules, soundness note and truncation policy

Status: approved on 2026-09-27 for experimental implementation; reviewed
against `02a57ef` on 2026-09-28 by the
[work-plan audit](audits/2026-09-28-audit.md). Written on 2026-09-27 as
work-plan items K2.1 (the H1 fragment and its soundness note) and K2.5
(G2's truncation and resizing policy, with its migration ledger). It is the
contract that K2.2 (instructions), K2.3 (driver and bridges), K2.4
(differential fixtures) and L2.1 (the `inductive` declaration) implement,
on the `h1-signatures` branch. Its statuses are distinct:

- **Decided:** every question of section 11, on 2026-09-27.
- **Approved for implementation:** the fragment of sections 1–3 and the
  families of section 5, in the experimental mode of 5.7 only. Implemented
  there: K2.2's six families (ABI 3), K2.3 (section 6), L2.1
  (section 9) and L2.2a's first `match` slice; every result carries the
  `kernel extension: H1` marker.
- **Review pending:** the obligations of 4.5. Implementation and passing
  tests do not discharge them.
- **Migration pending:** K2.4's fixtures and tooling (section 7) and K2.5's
  ledger verifier (8.5).

**Release checklist for finite-level H1.** The experimental option is
removed, and default admission granted, only when every item has evidence
and a review decision:

1. D1, D4 and D5 written out and reviewed (4.2, 4.3);
2. Lemma H2's full case analysis, and the critical-pair check of 3.7;
3. canonicity (4.4) reviewed, relative to the assumed baseline of 4.1;
4. the acceptance matrix of 10.10 complete, K10 and K11 included. Every
   case is traced but K1 with tubes, K6 along `ua`, K10 and K11, and the
   cases that wait for L2.2b (E4, E11), K2.5 (G2, G4–G7) and K2.4a
   (X1–X8); `tests/acceptance-matrix.test.mjs` checks the matrix against
   the tests;
5. a recorded run of the whole suite at a pinned revision, repeated at
   the release's own. The first was CI run 36472206548, at `bef00e3` on
   2026-09-28, where all seven jobs passed; the verifier's marker
   comparison (6.4) and the inspection of 6.5 were delivered the same day;
6. K2.4a's differential fixtures X1–X4 and X6–X8. The work plan's
   isolation correction I1.2a, on which 4.1's baseline relies, was
   delivered on 2026-09-28.

Not on the checklist: the classification of each instruction into the
cases (i)–(v) of 2.3. It belongs to the deferred tier-parametric proposal
(Q16), not to the finite-level fragment. Normalization and decidable
conversion are not claimed (4.5); a canonicity fixture is not a proof of
them.

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

## Decisions

The user decided every open question on 2026-09-27, and section 11
records each as decided. Q8, Q15, Q16 and Q18 were decided as below;
Q1–Q7, Q9–Q14 and Q17 were accepted as recommended.

- **Q16: finite levels only.** The conservative first release. Instances
  read and carry finite levels. The native sum, W and pushout instructions
  stay for arguments at tier-1 levels, and K2.4 retires only the `Nat`
  instructions. The tier-parametric extension of 2.3 is a later proposal,
  not a pending choice.
- **Q8: per universe parameter.** An erased parameter only bounds parameter
  types, and instances are one term at every universe (D9). A recorded
  parameter occurs in a constructor type or cannot be read; instances
  carry it, and are distinct at different levels, as standard universe
  polymorphism (D8). Admission classifies each parameter by an occurrence
  check, and the kernel checks the classification (1.1, 5.2).
- **Q15: level-dependent signatures are admitted,** with the parameter
  recorded. `inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }`
  checks.
- **Header universes** (9). The result position after the colon accepts a
  universe wherever it accepts `type`, as in `inductive Flag : U1 { … }`,
  `: next(U)`, or `: prop U` together with an h-level. A written universe
  is the declared level, checked as an upper bound; without one, the least
  level is inferred. When in doubt, the user writes the universe.
- **Q18: truncation levels in HoTT's numbering.** A sort may be truncated
  at any level `n ≥ -1`, written `trunc(n)`; `prop` is `trunc(-1)`, `set` is
  `trunc(0)`, and `type` is untruncated (1.6). The header words `type`,
  `set`, `prop` and `trunc` are contextual: keywords only in the result
  position, ordinary names elsewhere (9).

## 0. Relation to the adopted design and to G0

The design fixes one signature format for H1–H4. For H1 this document makes
seven choices precise. Each is a question in section 11, decided as
recommended.

| Design statement | H1 as specified here | Why |
| --- | --- | --- |
| One heterogeneous formal composition `fcomp` per sort, along a line of parameters and indices | Higher sorts get a formal homogeneous `hcomp` at fixed parameters; transport along a parameter line computes by recursion on its argument; general composition is `hcomp` after transport (Q1, Q2) | An eliminator's motive is over the sort at fixed parameters, so a formal element joining two parameter values could not be eliminated. This is Coquand–Huber–Mörtberg's split, which the kernel already implements for pushouts. |
| `fcomp` pushes through constructors of sorts without path constructors | Data sorts get no formal composition at all; composition pushes through equal constructor heads and is otherwise neutral (Q1) | A formal element that also pushes breaks confluence and stability under substitution. This is how the hand-coded `Nat`, sums and W types compute. |
| Boundaries may mention earlier constructors and formal compositions | Boundaries are constructor expressions: positions and earlier constructors at interval formulas, with no compositions (Q3) | Displayed boundaries then follow by substitution; every H1 example needs no more. |
| Boundaries are systems on faces of the constructor's dimensions | Boundaries are cube boundaries: a piece on both faces of every dimension (Q4) | A cube boundary is an iterated path type, which the kernel already has. Partial boundaries would need extension types. |
| Constructors take dimension arguments | A constructor with dimensions is a function into an iterated path type, applied at interval formulas by path application (Q5) | Boundary reduction is then the kernel's existing path step, and overlap agreement is typing. |
| A sort's level is the maximum of its data and arity levels | The former's type declares the level; the kernel checks that every constructor type lives in that universe, and the elaborator declares the least such level (Q7) | The instruction kernel does not infer principal levels. |
| G0 2.12: generated constants are level-abstracted, as `Trunc : Π (x < ω). Π (A : U(x)). U(x)`; G0 Q1: instances at different levels are distinct | Per universe parameter (Q8, decided). An *erased* parameter, which only bounds parameter types, is read from the parameters' judgements, so instances are one term at every universe. A *recorded* parameter, which occurs in a constructor type or cannot be read, is carried by instances, and instances at different levels are distinct, as G0 Q1 decided. Every level is finite (Q16, decided) | The native formers are level-erased, and the archive relies on it (7.2). A sort built from its parameters alone does not depend on the universe it is viewed in (D9). A sort that stores types of its own level does, and is standard universe polymorphism (D8). |

Everything else follows the design: one signature format, positions as
cubes, a generated squash constructor for each truncation level, clause typing
through the partial eliminator, computation on every constructor and on
formal compositions, and staged trust.

## Decisions in brief

- **Fragment.** One sort, uniform parameters (level and term), no indices.
  Constructors are checked in order. Each takes data, then positions, and has
  zero or more dimensions with a cube boundary. The sort is untruncated
  (`type`) or truncated at a level `n ≥ -1` in HoTT's numbering (`trunc(n)`,
  with `prop` and `set` for -1 and 0); a truncated sort appends one
  generated squash constructor.
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
- **Erased and recorded universe parameters** (Q8, Q15, decided). A level
  parameter that only bounds parameter types is erased: instances read it
  from their parameters' judgements, so one term serves every universe, as
  native sums do. A level parameter that occurs in a constructor type, or
  cannot be read, is recorded: instances carry it, and instances at
  different recorded levels are distinct. Every level is finite (Q16,
  decided); letting tier-parametric signatures read every tier is a later
  proposal.
- **Trust.** Admission requires the kernel's H1 extension flag until review.
  Results carry `kernel extension: H1` transitively; it is visible, and it is
  not a non-computing dependency.
- **Differential oracle (K2.4).** `Nat`, sums, W types and pushouts are
  declared as signatures and compared with the hand-coded instructions by a
  level-free translation. As Q16 decided, the `Nat` instructions retire,
  and the sum, W and pushout instructions stay only for arguments at tier-1
  levels. Native and declared forms are different
  types; no conversion relates them.
- **Truncation (K2.5, G2).** `Trunc` is universe-preserving and has no
  resizing. The archive keeps its legacy assumptions. Measured on the archive,
  a universe-preserving truncation breaks 47 of 3,804 declarations, from 8
  roots. No remedy needs a resizing assumption: two declarations wait for
  H2's inductive families, four take an explicit smallness hypothesis that
  their one consumer discharges from `LEM`, and the rest need restatement or
  nothing (section 8).

## Notation

A trailing `s` on a variable marks a sequence: `xs` is `x_1 … x_n`, `as` is
`a_1 … a_n`, and `q̄s` is `q̄_1 … q̄_n`.

| Symbol | Meaning |
| --- | --- |
| `S` | the sort being declared; also its instance `S(as)` at parameters `as` |
| `xs` | the signature's level parameters: erased ones, which each instance reads from its parameters' judgements, and recorded ones `xs_r`, which it carries |
| `ρ` | an instance's levels, one per level parameter: given for recorded ones, read for erased ones |
| `ℓs_r` | an instance's recorded levels; `S{ℓs_r}(as)` is the instance, written `S(as)` when there are none |
| `ps : Ps` | the signature's term parameters, a telescope over `xs` |
| `ℓ` | the sort's level, a level expression over `xs` |
| `c_1 … c_n` | constructors, in order; `c_k` also names the constructor at an instance |
| `ts : Ds` | a constructor's data telescope |
| `qs : Qs` | a constructor's positions |
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

- The telescope starts with level parameters `xs`, then term parameters
  `ps : Ps`, each type well formed over the ones before. At admission the
  telescope is presented as G0's prenex level binders `xs < ω` (G0 Q8).
- **Erased and recorded universe parameters** (Q8, decided). Admission
  classifies each level parameter by a syntactic occurrence check:
  - *Erased*: it occurs in no constructor type `T_k`, and it has a
    determining occurrence (below). It only bounds parameter types, so each
    instance reads it from its parameters' judgements, and the instance
    term does not carry it. `Trunc`, `List`, `W`, `Pushout`, `Quotient` and
    the K2.4 counterparts have only erased parameters.
  - *Recorded*: it occurs in some constructor type, or it has no
    determining occurrence, as when it occurs only in the result universe.
    Each instance carries it as an explicit level argument, and instances
    at different recorded levels are distinct types, as G0 Q1 decided for
    generic definitions. `Pointed(U < UU0) : next(U) { pt(X : U, x : X); }`
    has a recorded parameter: `X : U` is data.

  The driver proposes the classification, and the kernel records it and
  checks it (5.2). The kernel never accepts as erased a parameter that
  occurs in a constructor type: the instance term would then be one type
  at every level, containing types of its own level, which is the
  self-containing universe behind Girard's paradox (2.3, V24).
- **Determined.** An erased parameter occurs as the whole universe at the
  end of some parameter's type, as in `A : U(x)` or `B : L → U(y)`;
  `U(x + 1)` and `U(max(x, y))` do not count. Each instance reads the level
  there, from that parameter's judgement, as a level expression (3.1).
- **Finite levels** (Q16, decided). Instances read and carry finite levels
  only, the range admission checked, whether erased or recorded. A later
  proposal would let *tier-parametric* signatures, whose admission never
  uses the finiteness of an erased parameter, read levels of every tier
  (2.3). A signature may also be stated at fixed levels of any tier, with
  no level parameters.
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
E ::= q_j(us)                          a position applied to data terms at its arity
   |  c_m(us, Es')                       an earlier constructor, data terms then positional arguments
   |  E @ r                            path application at an interval formula
   |  ⟨i⟩ E                            path abstraction: a cube of one more dimension
E' ::= E  |  λ (y : A). E'             positional arguments, under the arity's binders
```

- `us` are *data terms*: any terms that mention no `s`, constructor or
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
- **Carried types.** The type a path abstraction carries (its family) and
  the type a path application carries (the applied path's type, whose
  endpoints the path step exposes) are cubes over `s` as well, their
  endpoints constructor expressions. An endpoint hides nothing in them: a
  path whose type was converted to `Path(s, (λ (y : s). y)(base), base)`
  is refused at application. The driver presents these types with redexes
  contracted, as it does `T_k`.
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

The modifier is a truncation level in HoTT's numbering: `trunc(n)` for an
integer `n ≥ -1`, or untruncated (Q18). `prop` is `trunc(-1)`, `set` is
`trunc(0)` and `type` is untruncated; `trunc(1)` makes a groupoid.

`type` adds nothing. `trunc(n)` appends one generated constructor after the
user constructors. Write `B_0 := s` and `B_{k+1}(y, z) := Path(B_k, y, z)`
for `y, z : B_k`, a type of `k`-dimensional cells between the previous pair.
The squash of level `n` takes a pair of parallel cells at every depth from
`0` to `n + 1`, and makes the last pair equal:

```text
trunc(n):  squash : Π (y_0, z_0 : B_0). Π (y_1, z_1 : B_1(y_0, z_0)). …
                      Π (y_{n+1}, z_{n+1} : B_{n+1}(y_n, z_n)). B_{n+2}(y_{n+1}, z_{n+1})
prop:      squash : Π (y, z : s). Path(i; s, y, z)
set:       squash : Π (y, z : s). Π (u, v : Path(s, y, z)). Path(i; Path(j; s, y, z), u, v)
```

The squash of `trunc(1)` takes `y, z : s`, `u, v : y = z` and `r, t : u = v`,
and has three dimensions.

Each is an ordinary constructor of the normal form: its positions are cubes
of depth `0` to `n + 1`, and it has `n + 2` dimensions with a cube boundary.
A user constructor cannot mention it, since it comes last.

The elaborator knows its meaning for automatic clauses (L2.2b). The squash
clause of an eliminator is an `(n + 2)`-dimensional cube in the motive, and
it is generated from a proof that the motive's fibres have truncation level
`n`. The library's h-level definitions (HoTT roadmap D0a) count from `IsProp`
at 0, so the elaborator asks for level `n + 1` there. Written by hand, a
squash clause is practical for `prop` and `set` only. A first implementation
may therefore admit `prop` and `set`, and enable the other levels together
with automatic clauses; the rules are the same for every `n`.

### 1.7 What H1 excludes

- Indices, and constructors that choose result indices: H2.
- Several sorts, and companion sorts: H3 when every sort is `set` or `prop`,
  otherwise H4.
- Non-uniform parameters: an index in disguise, H2.
- Arities that depend on positions (design open question 1).
- Partial boundaries, and boundaries with compositions (Q3, Q4).
- Instances at tier-1 levels (Q16, decided). The later tier-parametric
  proposal would allow them for erased parameters of tier-parametric
  signatures.
- Induction-recursion (design open question 2).

### 1.8 Examples in normal form

Level parameters are written `x`, `y`, `z`; `U(x)` is the universe. `Path(S, a, b)`
abbreviates `Path(i; S, a, b)` when `i` is not used. The former type is the
signature's presentation at admission. Every level parameter is erased,
and instances carry no level for it (3.1), except in `Pointed`, whose `x`
occurs in a constructor type and is recorded.

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
| `Quotient`, `set`: set-truncated | `Π (x, y < ω). Π (A : U(x)). Π (R : A → A → U(y)). U(max(x, y))` | `class : Π (a : A). s`; `glue : Π (a, b : A). Π (r : R(a, b)). Path(s, class(a), class(b))`; generated `squash` |
| `Pointed`, from `inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }` | `Π (x < ω). U(x + 1)`, `x` recorded | `pt : Π (X : U(x)). Π (p : X). s` |

In `Torus`, the inner path over `j` runs from `p @ i` to `p @ i`, and the
outer endpoints are `q`. They agree at the four corners, `b`, by the typing
of the path types: `q : Path(s, b, b)` must have the type
`Path(j; s, p @ 0, p @ 0)`, which the path step reduces to it. In `S2`, the
outer endpoints `⟨j⟩ base` are path abstractions (1.4). In `Pushout`,
`fst(m)(c)` is a data term.

## 2. Universes and substitution

### 2.1 The sort's level

- The former's type `Π (xs < ω). Π (ps : Ps). U(ℓ)` declares `ℓ`.
- Every constructor type `T_k` must be derived at `U(ℓ)` in the admission
  context, where `s : U(ℓ)`. By inversion of the formation rules, every data
  type and every arity in `T_k` then lives in `U(ℓ)`: the instruction kernel
  forms `Π` at the maximum of its parts and raises only by `Lift`, which never
  lowers. The generated squash types live in `U(ℓ)` because they mention only
  `s`.
- Parameters count only through those types (G0 Q6). A parameter that no data
  type or arity mentions contributes nothing.
- The kernel checks `ℓ` as an upper bound. The header may state `ℓ` as a
  universe after the colon; otherwise the elaborator declares the least
  level: the maximum of the inferred levels of the data types and arities,
  and `0` when there are none (Q7, 9).
- An instance lives in `U(ℓ[ρ])`, where `ρ` holds its recorded levels and
  the erased levels read from its parameters' judgements (3.1). `Trunc(A)`
  for `A : U(x)` lives in `U(x)`, and `Pointed{x}` in `U(x + 1)`.

### 2.2 Fixtures by case

| Case | Declaration | Level |
| --- | --- | --- |
| Phantom parameter | `Box(x < ω, A : U(x)) { mk(n : Nat); }` | `U(0)` at every `x` |
| Stored data | `Pair(x, y < ω, A : U(x), B : U(y)) { mk(a : A, b : B); }` | `U(max(x, y))` |
| Arity | `W(x, y < ω, L : U(x), B : L → U(y))` | `U(max(x, y))`: `B(l)` is an arity |
| Relation | `Quotient(x, y < ω, A : U(x), R : A → A → U(y))`, the set-truncated quotient | `U(max(x, y))`: `r : R(a, b)` is data of `glue` |
| Large parameter only | `Tag(A : U(1)) { here; }` | `U(0)` |
| Stored type, recorded level | `Pointed(x < ω) : U(x + 1) { pt(X : U(x), p : X); }` | `U(x + 1)`; `x` is recorded |
| Mixed | `Tagged(x, y < ω, A : U(x)) : U(max(x, y + 1)) { tag(a : A, B : U(y)); }` | `U(max(x, y + 1))`; `x` erased, `y` recorded |
| Stored type, fixed level | `Pointed1 : U1 { pt(X : U0, x : X); }` | `U(1)`, as written |
| Tier 1 through parameters | `Pair(A, B)` for `A, B : UU0` | Refused (Q16); the later tier-parametric proposal would give `UU0` |
| Tier 1 at fixed levels | `Big(A : UU0) { wrap(a : A); }` | `UU0` |

Indices, the fifth case the work plan lists, arrive with H2; the rule then
counts index types too (G0 2.12).

### 2.3 Instances and rejections

- **Erased parameters: one term at every universe.** `Trunc(A)` is one
  term. It is typed at `U(ℓ[ρ])` for the levels `ρ` read from `A`'s
  judgement, and a derivation
  that first lifts `A` types it higher; cumulativity relates the two. So
  `point(a)`, built where `A : U(0)`, is a term of `Trunc(A)` where a generic
  definition sees `A : U(1)`. The native sums behave this way today:

  ```text
  def sum_id(U < UU0, A : U, x : A or A) : A or A := x;
  def small : Nat or Nat := left(0);
  def lifted : Nat or Nat := sum_id(U1, Nat, small);
  ```

  checks, and its translation (7.2) must check too. For erased parameters
  this replaces G0 Q1's distinct instances (Q8).
- **Recorded parameters: explicit and distinct.** An instance carries each
  recorded level. At the source, `Pointed(U0)` is the instance with
  recorded level `0`; `Pointed` used as a function is the level λ
  `fun (U < UU0) => Pointed(U)`, which G0's `LevelApply` and `Beta`
  instantiate. The level is supplied at formation under `LevelApply`'s
  conditions: finite, substituted by G0's capture-avoiding substitution,
  and compared by normal form (3.1). `Pointed(U0) : U1` and
  `Pointed(U1) : U2` are distinct types, following G0 Q1: a `Pointed(U0)`
  value is not a `Pointed(U1)` value. A map between them is written by
  `match`, as in

  ```text
  def lift(p : Pointed(U0)) : Pointed(U1) := match p { pt(X, x) => pt(X, x); };
  ```

  where `X : U0` is used at `U1` by cumulativity. This is standard universe
  polymorphism: at each assignment of its recorded levels the signature is
  an ordinary fixed-level signature, by G0's decomposition (G0 3.2), and
  its soundness needs no argument beyond G0's.
- **Instances within the admission's bound.** Admission derives the
  constructor types with level entries `x < ω`, so the derivation holds at
  every finite assignment, by G0's level substitution (G0 Lemma 4). An
  instance therefore reads finite levels: tier-0 level expressions, which may
  mention level variables. A read level of tier 1 or above is refused, and
  so is a recorded level of tier 1 or above, by `LevelApply`'s own
  condition. This is H1's rule (Q16, decided).
- **Later proposal: tier-parametric signatures** (Q16, decided against for
  H1). The native formers accept arguments at every tier. A signature's
  erased parameters could too, if its admission never relied on their
  being finite. Q16 decided that H1 leaves this out, and it is kept
  specified here for a later decision, when a rebuilt result needs a
  declared type at `UU0`. Recorded parameters stay finite in any case, by
  `LevelApply`'s condition.

  *Criterion.* A signature is tier-parametric when it has no recorded
  parameter, and its admission is derivable without using the bound
  `x < ω` of any level parameter, so that every level side condition of
  the derivation holds when the level parameters range over all ordinals
  below ω². G0's rules use the bound in
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
  item of this proposal, for each K2.2 family, if it is adopted; an
  instruction added later must be classified before the check admits it.
  It is not on finite-level H1's release checklist (header).

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
- **Level-dependent signatures are admitted, with the parameter recorded**
  (Q15, decided). `Wrap(x < ω) : U(x + 1) { wrap(B : U(x)); }` is admitted,
  and `x` is recorded because it occurs in a constructor type.
- **Never erase a level that a constructor type mentions.** A driver that
  proposes such a parameter as erased is refused at the constructor
  (acceptance V24). Take
  `Holder(x < ω, A : U(x)) : U(x + 1) { hold(B : U(x)); }` with `x` proposed
  erased, since `A : U(x)` determines it. Then `Holder(Unit)` would be one
  term at every level. At `x = 1` it would contain `hold(B)` for every
  `B : U(1)`, and `Holder(Unit)` itself lives in `U(1)` when read at
  `x = 0`. So `hold(Holder(Unit)) : Holder(Unit)`: a type containing its
  own code. That is the self-containing universe behind Girard's paradox.
  Recorded, `Holder{0}(Unit) : U(1)` and `Holder{1}(Unit) : U(2)` are
  distinct, and no such element exists.
- **Lowering with a recorded level.**
  `Pointed(x < ω) : U(x) { pt(X : U(x), p : X); }`, from the source
  `inductive Pointed(U < UU0) : U { … }`, is rejected at `pt`. The data
  `X : U(x)` lives in `U(x + 1)`, above the declared level.
- **Tier-1 constants with level parameters.**
  `Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); }` is admitted, but it
  is not tier-parametric. G0's normal form absorbs `x` into `ω` in
  `max(x, ω)`, which is valid only while `x` is finite, and its instances read
  finite levels only (Q16).
- **Undetermined level parameters.** A level parameter that ends no
  parameter's type cannot be read from the parameters, so it is recorded
  (1.1, V30). Proposing it as erased is rejected (V14).
- **The former is not a term.** A declared type used as a function, such as
  `Trunc` unapplied, is the elaborator's eta-expansion
  `fun (U < UU0, A : U) => Trunc(A)`: a G0 generic definition of type
  `Π (x < ω). Π (A : U(x)). U(x)`, in `U(ω)`. The instance inside it carries
  no level.

### 2.4 Level substitution

- An instance carries its recorded levels and nothing for its erased ones,
  and its parameter terms may mention levels too. Level substitution is
  G0's ordinary recursive substitution (G0 2.8), through every subterm:
  recorded levels, parameters, constructor arguments, motives and clauses.
  `Pointed{x}` at `x := 0` is `Pointed{0}`. So `(λ (x < ω). Trunc(U(x))) {0}` reduces
  by `Beta` to `Trunc(U(0))`, and an eliminator whose motive lands in
  `U(x + 1)` becomes one into `U(1)` (acceptance V16).
- Formation reads an instance's erased levels from its parameters'
  judgements (3.1), so the reading is itself substituted: a parameter judgement
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

An instance `S{ℓs_r}(as) : U(ℓ[ρ])` is formed from one finite level per recorded
parameter, `ℓs_r`, and judgements `a_i : P_i[ρ, a_<i]`, one per term
parameter, in order:

- each recorded parameter takes its given level, under `LevelApply`'s
  conditions: finite, with its variables level entries of the context;
- each erased parameter reads its level `ρ(x)` at its determining
  occurrence: the universe at the end of the corresponding parameter
  judgement's type;
- every parameter judgement's type must then be exactly `P_i` with `ρ` and
  the earlier parameters substituted, up to alpha equality. When two
  occurrences of an erased parameter would read different levels, the
  judgement is refused, and the driver lifts the lower parameter first;
- the term records the signature, the recorded levels and the term
  parameters. It carries nothing for the erased parameters. Signatures
  with no recorded parameter, such as `Trunc`, have instances written
  `S(as)`.

Every level, read or given, must be finite (Q16, decided). A derivation that
lifts a parameter first reads a higher erased level, and types the same term
in a higher universe. Two instances with recorded levels of different normal
forms are different terms, so different types.

### 3.2 Constructors and boundary reduction

- At an instance `I = S{ℓs_r}(as)`, the constructor `c_k` is the term
  `Con(k; I)`, of type `T_k[s := I, xs_r := ℓs_r, ps := as, c_m := Con(m; I)]`.
  Only the recorded levels are substituted: `T_k` mentions no erased
  parameter (1.1). So `pt` at `Pointed{0}` has type
  `Π (X : U(0)). Π (p : X). Pointed{0}`.
- A saturated application `Con(k; I)(us, es)`, written `c_k(as)(us, es)` below, is
  canonical. With `d_k ≥ 1` it is a path, and `(c_k … ) @ r_1 … @ r_d` with no
  `r_l` an endpoint is canonical.
- **Boundary reduction.** `(c_k …) @ 0` and `(c_k …) @ 1` reduce to the
  endpoints of its type: by the existing `Path` step and by weak head
  reduction, both of which read the path application's type annotation.
  `PathApply` and `PathAt` record the applied path's type there, and at a
  constructor that type is the constructor type at the instance, so the
  annotation's endpoints are the signature's boundary, substituted. Every
  path application the kernel builds carries its annotation, a literal path
  type: `Replace` puts only a path type in that place, and substitution and
  the other steps keep the node a path type. The families that build terms,
  F4's transport and F5's `Iota`, keep that invariant, and no separate rule
  reads the signature. This is the design's "a constructor
  evaluated on a face of its dimensions reduces to its boundary".
- Eta for paths gives `c_k … ≡ ⟨i⟩ (c_k …) @ i` as for any path.

### 3.3 Kan structure of a data sort

A data sort has `d_k = 0` for every constructor and modifier `type`. It has
no formal composition.

```text
comp^i S(as(i)) [φ ↦ u] u_0
  ⟶  c_k(as(1))(comp^i Θ_k(as(i)) [φ ↦ θ_u] θ_0)
      when whnf(u_0) = c_k(as(0))(θ_0) and whnf(u) = c_k(as(i))(θ_u) on every nonempty face
comp^i S(as(i)) [φ ↦ u] u_0  is neutral otherwise
```

- `as(i)` is the parameter line; levels do not vary (G0 2.11).
- `Θ_k(as)` is the argument telescope of `c_k` at the parameters: data then
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

A higher sort has a constructor with `d_k ≥ 1`, or a truncation modifier
(`trunc(n)`, `prop` or `set`).

- **Formal homogeneous composition.** `hcomp^i S(as) [φ ↦ u] u_0 : S(as)`,
  at fixed parameters, is canonical. On a face that holds it reduces to that
  tube at `i = 1` (the `Face` step); tubes on the empty face are dropped. It
  never pushes into a constructor.
- **General composition** reduces to formal composition after transport, as
  `ck_pushout_composition` does today:

  ```text
  comp^i S(as(i)) [φ ↦ u] u_0
    ⟶  hcomp^j S(as(1)) [φ ↦ transp^k S(as(j ∨ k)) (j = 1) u(j)] (transp^i S(as(i)) 0 u_0)
  ```

- **Transport** `transp^i S(as(i)) φ u_0`, with `as` constant on `φ`, computes
  by the weak head of `u_0`. Section 3.5 gives the rules. When `φ` holds, it
  reduces to `u_0` (the `Face` step).

### 3.5 Transport along parameters with boundary correction

Write `A(i) := S(as(i))`. For a line `w(i) : A(i)` define the squeeze, which
joins the transport of `w(0)` to `w(1)` and is fixed on `φ`:

```text
squeeze^i_A φ w  :=  transp^h A(i ∨ h) (φ ∨ (i = 1)) w(i)          at i = 0: transp^h A(h) φ w(0); at i = 1: w(1)
```

`transp^i A(i) φ u_0` reduces by cases on `whnf(u_0)`:

1. **Point constructor** `c_k(as(0))(θ_0)`, `d_k = 0`. Let `θ(i)` be the
   transport filler of the telescope: `θ(i) := fill^i Θ_k(as(i)) [φ ↦ θ_0] θ_0`,
   so `θ(0) = θ_0` and `θ` is constant on `φ`. Then
   `transp^i A(i) φ u_0 ⟶ c_k(as(1))(θ(1))`.
2. **Constructor at dimensions** `(c_k(as(0))(θ_0)) @ r_1 … @ r_d`, no `r_l` an
   endpoint. With `θ` as above, let `v := (c_k(as(1))(θ(1))) @ rs`. For each
   face `(l, ε)`, let `b_{l,ε}(i)` be the boundary piece of `c_k` on
   `i_l = ε`, at parameters `as(i)` and arguments `θ(i)`, with the other
   formulas `rs` substituted. Then

   ```text
   transp^i A(i) φ u_0
     ⟶  hcomp^h A(1) [ φ ↦ u_0,
                       (r_l = ε) ↦ (squeeze^i_A φ b_{l,ε})[i := 1 - h]   for each l ≤ d, ε ∈ {0, 1} ]
                     v
   ```

   - At `h = 0` each wall is `b_{l,ε}(1)`, which is `v` on its face; on `φ`
     the base is `u_0`, since `as` and `θ` are constant there.
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

**Motive and clauses.** For an instance `S(as)`, a motive `M : Π (z : S(as)). U(l')`
at any level `l'`, and clauses `m_1 … m_n` (squash constructors included),
the eliminator `elim_{M, ms} : Π (z : S(as)). M(z)`.

**Displayed types.** For a cube `C` over `S` and `y : C`, its displayed type
`C̄(y)`:

```text
S̄(y)                  :=  M(y)
Path(i; C, E, E')‾(y) :=  PathP(i. C̄(y @ i), ⟦E⟧, ⟦E'⟧)
```

A position `q : Π (ys : As). C` has displayed type `q̄ : Π (ys : As). C̄(q(ys))`.

**Displayed boundary.** `⟦E⟧` replaces, in a constructor expression, each
position by its displayed variable and each earlier constructor by its
clause:

```text
⟦q_j(us)⟧          :=  q̄_j(us)
⟦c_m(us, Es')⟧       :=  m_m(us, Es', ⟦Es'⟧')
⟦E @ r⟧           :=  ⟦E⟧ @ r
⟦⟨i⟩ E⟧           :=  ⟨i⟩ ⟦E⟧
⟦E⟧'              :=  ⟦E⟧                          ⟦λ (y : A). E'⟧' := λ (y : A). ⟦E'⟧'
```

**Clause type.** With `c := c_k(as)(ts, qs)`:

```text
ClauseType_k(M, m_1 … m_{k-1})  :=  Π (ts : Ds). Π (qs : Qs). Π (q̄s : Q̄s). R̄(c)
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
`q̄ := λ ys. elim(q(ys))`, pointwise along a cube, `⟦E⟧` is convertible to
`elim(E)` by `Iota` steps.

**Automatic clauses** (L2.2b) are the elaborator's: the kernel requires every
clause, the squash clause included.

### 3.7 Computation rules

| Rule | Reduction | Step |
| --- | --- | --- |
| Iota, point | `elim_{M,ms}(c_k(as)(ts, qs)) ⟶ m_k(ts, qs, q̄s)` with `q̄_j := λ ys. elim^{C_j}(q_j(ys))` | `Iota` |
| Iota, dimensions | `elim_{M,ms}((c_k(as)(ts, qs)) @ r_1 … @ r_d) ⟶ m_k(ts, qs, q̄s) @ r_1 … @ r_d` | `Iota` |
| Boundary | `(c_k(as)(ts, qs)) @ ε ⟶` the endpoint of its type | `Path`, `Whnf` |
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

1. **Levels.** Recorded levels are fixed by the instance. By G0's
   decomposition (G0 3.2) the signature is interpreted separately at each
   assignment of them, as an ordinary fixed-level signature. Erased levels
   occur in no constructor type, so at fixed recorded levels the
   construction below takes only the parameters' values `⟦as⟧` as input.
   The erased levels read at an instance only name a universe `U_α` that
   contains the result, and each such `α` is large enough, by G0's
   substitution into the admission derivation at finite levels. So one
   presheaf interprets the instance at every erased reading, and
   cumulativity by subsumption relates the universes (D9). Every other H1
   obligation is argued at fixed parameter values and recorded levels.
2. **Carrier.** For fixed parameters `as` in a context `Γ`, define the
   presheaf `⟦S(as)⟧` over cubes as the least family of sets closed under:
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
| D4 | Cube positions (paths as arguments), needed by the squash of every level `n ≥ 0`, at cube depth up to `n + 1` | In step 2 a cube position is an element of the carrier at a higher cube with its boundary: still strictly positive. | Argued. **Open obligation:** well-foundedness of the definition when positions live at higher cubes of every depth, written out |
| D5 | Infinitary positions in higher sorts | Step 4's inductive definition allows infinitary generating clauses; the metatheory needs the corresponding well-founded trees, which ZFC provides. | Argued. **Open obligation:** the infinitary inductive definition over cubes, with restriction, written out |
| D6 | Path-valued constructors | A presentation of dimension arguments: `c @ r` is the constructor at `r`. It changes no rule of the model. | A conditional outline, found valid in review |
| D7 | Motives in any universe, including UU tiers | The eliminator is defined in the model at fixed parameter values, and a motive's universe plays no role in its definition. | A conditional outline, found valid in review |
| D8 | Level-generic signatures, and recorded parameters | No reduction rule reads a level. Level substitution recurses through recorded levels, parameter terms, motives and clauses, and commutes with formation's reading of erased levels from parameter judgements (2.4). A recorded parameter is standard universe polymorphism: at each assignment of recorded levels the signature is an ordinary fixed-level signature (G0 3.2), and instances at different levels are distinct, as G0 Q1 decided for definitions. | Argued; relies on G0 and needs no new argument. Corrected after the second review for levels inside parameter terms |
| D9 | Erased universe parameters | An erased parameter occurs in no constructor type, so at fixed recorded levels the carrier, its Kan structure and its eliminator are built from `⟦as⟧` alone (4.2, step 1). Cumulative universes are nested by subsumption, so one presheaf lies in every `U_α` that is large enough. At finite read levels, G0's substitution into the admission derivation shows each is. This is the condition under which Timany and Sozeau make instances of a Coq inductive cumulative. The kernel refuses an erased parameter that occurs in a constructor type (V24). The later tier-parametric proposal would extend this to tier-1 readings (2.3). | Argued at finite levels, which is all Q16 admits. To be reviewed |

**Lemma H1 (clause typing is the partial eliminator).** For a constructor
expression `E` over positions `qs` and earlier constructors, and the
substitution `σ := [q̄ := λ ys. elim^{C}(q(ys))]`, `⟦E⟧σ ≡ elim^{C}(E)` by `Iota`
steps. Proof: induction on `E`. For `q_j(us)`, both sides are
`elim(q_j(us))`. For `c_m(us, Es')`, the right side takes one `Iota` step to
`m_m(us, Es', elim(Es'))`, which is the left side by induction. Path
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
into `rs` and `φ`.

### 4.4 Canonicity

**Claim.** Let `t` be a term in a context of dimension variables only, of a
closed data type in the sense of invariant 10, using no assumption. Then `t`
reduces to a canonical value. For declared data sorts, the value is a
saturated constructor. For higher sorts, it is a constructor at
non-endpoint formulas, or an `hcomp` of such.

**Argument.** Extend Huber's computability predicates:

- For a closed instance `S(as)`, a term is computable when its weak head is
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
| Erased universe parameters are sound at finite levels | Argued (D9), from G0's level substitution |
| Recorded universe parameters are sound | Standard universe polymorphism, by G0's decomposition (D8); no new argument |
| The kernel's classification check refuses an erased parameter in a constructor type | Specified (5.2); a rejection test (V24) |
| The later tier-parametric proposal would be sound at every tier | Proved here in outline, by induction on the checked admission derivation (2.3). Not part of H1 (Q16, decided) |
| Confluence of the generated rules with the existing ones | Argued at boundaries (3.7); the full critical-pair check is an **open obligation** |
| Canonicity for H1 | Argued (4.4), relative to the assumed baseline |
| Consistency and canonicity of the baseline, pushouts included | **Assumed**, as in G0 3.6 |
| Normalization, for decidable conversion | **Not established**; the kernel relies on budgets, as today |
| The baseline's isolation of instruction acceptance from untrusted conversion queries | **Corrected** on 2026-09-28 (work-plan I1.2a). The audit's finding 1: the reducers behind `Whnf` and `Normalize` called `ck_convertible`, and a successful public conversion query entered the memo that folded alpha equality read, so one `Apply` was refused, then accepted, with no equality judgement among its premises. Valid beta equality, so no false equality. Now the folded comparison reads only its own results, reduction decides eta by syntax, and conversion refuses to run inside an instruction (`kernel/tests/test_isolation.c`) |

**Status on 2026-09-28.** No open obligation above has been discharged
since the approval of 2026-09-27; the isolation defect is an implementation
fix, not one of them. The implementation's tests are evidence for the
specified behaviour, not for these claims, and the header's release
checklist maps each to its evidence and review decision.

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
| 50 | `CC_SORT` | payload: signature index; child 0: the term parameters, as a list; child 1: the recorded levels, as a list of level nodes, or 0. An instance `S{ℓs_r}(as)`, with nothing for its erased parameters. |
| 51 | `CC_CON` | payload: constructor number; child 0: the instance. The constructor `Con(k; I)`, a function of its data and positions. |
| 52 | `CC_ELIM` | payload: signature index; child 0: motive; child 1: clause list. A function on the sort. |
| 53 | `CC_LIST` | child 0: an item; child 1: the next cell, or 0. Parameter, level and clause lists. |

- `CC_HCOMP` and `CC_TRANS` keep their layout. Their family may be any higher
  sort instance, not only a pushout.
- **Signature table.** Each entry records: its state (open or admitted); the
  former's type; the level and parameter binder symbols; each level
  parameter's classification, erased or recorded, and each erased one's
  determining occurrence; the sort symbol and level `ℓ`; the
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
  signature opened or extended since the checkpoint is still open, since
  its latest judgement is truncated; one left open from before the
  checkpoint, and untouched since, keeps its judgement.
- An admitted signature is never modified.

### 5.2 Family F1: admission

- `SignatureBegin(former, modifier, sort symbol, classification)`, where the
  modifier is a truncation level `n ≥ -1` or untruncated, encoded as 0 for
  an untruncated sort and `n + 2` for `trunc(n)`, and the classification is
  a mask whose bit `j` marks universe parameter `j` recorded: from a
  closed judgement `⊢ F : U(…)` whose term `F` is
  `Π (xs < ω). Π (ps : Ps). U(ℓ)`, open a signature. The binder symbols of `F`
  name the admission context's level and parameter entries, and the sort
  symbol names `s : U(ℓ)`. The classification marks each level parameter
  erased or recorded; the driver proposes it by the occurrence check of 1.1.
  Returns a signature judgement (a new judgement kind, like a composition
  system).
- `SignatureBegin` and `SignatureConstructor` are never answered from the
  derivation cache, since their results depend on the table and the
  extension gate: two identical `SignatureBegin`s open two signatures (Q10),
  and repeating a `SignatureConstructor` finds its premise no longer the
  latest. The sort and constructor symbols they accept are reserved from
  the kernel's fresh-symbol supply, so the squash's generated names never
  take them.
- `SignatureConstructor(signature, type, symbol)`: from `Γ ⊢ T_k : U(ℓ)`, where
  every entry of `Γ` is a level or parameter entry of the signature (by symbol,
  at an alpha-equal type), the sort entry, or an earlier constructor's entry
  at its recorded type: check the shape and positivity of 1.2–1.5, check
  that `T_k` mentions no erased parameter (1.1), and record `c_k`. A
  recorded parameter may occur in `T_k`. The universe
  must be exactly `U(ℓ)`, compared by level normal form;
  the driver lifts below it. The check reads the syntax as written, with no
  reduction: a data type written `(λ (X : U(0)). Nat)(s)` mentions `s` and is
  rejected. The driver presents `T_k` with such redexes contracted.
- `SignatureBegin` also checks the former type: every erased parameter has
  a determining occurrence (1.1). A recorded parameter needs none.
- `SignatureClose(signature)`: append the generated squash constructor of
  1.6 for the modifier's truncation level, if any, mark it admitted, and
  return its index. Later instructions
  name an admitted signature by its index, as `Lookup` names a definition.
- The later tier-parametric proposal would add, at `SignatureBegin`, that
  the former judgement end in its closing prenex, and at `SignatureClose`,
  a recorded tier-parametric flag from the walk of 2.3. H1 does not include
  it (Q16, decided).

The admission context's entries are ordinary entries, made by `Level` and
`Extend`, and the constructor types are derived by ordinary instructions. A
judgement in that context is open in `s` and the constructor entries, so
`Define`, which admits closed judgements only, can never publish one.

**Rejections, each a test:** a former type not of the stated form; a
constructor judgement with a foreign entry, or an entry at another type; a
universe other than `U(ℓ)`; each positivity and shape violation of 1.3 and
1.4, a composition in an endpoint included; data after a position; an
arity mentioning a position; a self or forward reference
(1.5); an erased parameter in a constructor type (`Holder`, V24); an
erased parameter with no determining occurrence; admission while the H1
extension is disabled (5.7); `SignatureClose` twice; any use of an open
signature. Tests also check the recorded classification: every parameter
erased for `Pair`, `Plus`, `Tree`, `Push`, `Trunc` and `Quotient`;
recorded for `Pointed`; one of each for `Tagged`.

### 5.3 Family F2: instances and constructors

- `SortBegin(signature)` starts an instance. `SortLevel(instance, ℓ)`
  supplies the next recorded level, under `LevelApply`'s conditions, and
  `SortParameter(instance, a)` adds the next parameter judgement. After the
  last, the judgement is `S{ℓs_r}(as) : U(ℓ[ρ])`, with `ρ` formed as 3.1
  describes.
- `Construct(instance, k)` gives
  `Con(k; I) : T_k[s := I, xs_r := ℓs_r, ps := as, c_m := Con(m; I)]`.
- Applications use `Apply`. Constructors at dimensions use `PathApply` and
  `PathAt`.

**Rejections:** a recorded level that is not finite, or that mentions a
variable not in the context; a missing or extra recorded level; a parameter
judgement whose type is not the telescope's under `ρ`; two occurrences of
an erased parameter that read different levels; a read level of tier 1 or
above (Q16, decided); a constructor number out of range; a reference to an
open or rolled-back signature.

### 5.4 Family F3: boundary reduction

The existing `Path` step, `Whnf` and `Normalize` reduce `(c_k …) @ ε` through
the application's type annotation, which is the constructor type at the
instance (3.2). F3 adds no rule: it tests that these reductions reach the
signature's boundaries, on faces reached in either order.

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
transport of `merid(a)` along a nonconstant parameter line reduces to
the corrected `hcomp` of 3.5; the same for the 2-dimensional `set` squash
and the 3-dimensional squash of `trunc(1)`. The kernel tests take the line
`e @ i` of a path of types `e : A = B`, and check on every face of the
constructor's dimensions that restricting the transport and restricting its
`hcomp` normalize alike. A closed nonconstant line needs univalence, which
the driver's tests of K2.3 build.

**Implementation.** A constructor's argument telescope is composed and
transported as nested Σ types `Σ (x_1 : A_1). … Σ (x_n : A_n). Unit`, so the
existing Σ and Π rules do the dependent filling of 3.3 and 3.5. The general
composition of a higher sort is the pushout's, transport then `hcomp`, which
was already uniform in its family; transport commuting with `hcomp` is
shared with pushouts.

### 5.6 Family F5: elimination

- `Eliminator(motive)`: from `M : Π (z : S(as)). U(l')`, where `S(as)` is a
  saturated instance of an admitted sort, open an eliminator judgement.
- `EliminatorClause(eliminator, clause)`: check the next clause against
  `ClauseType_k(M, m_1 … m_{k-1})` (3.6), syntactically, as `NatElim` checks
  its cases.
- `EliminatorClose(eliminator)`: when every constructor, squash included, has
  its clause, give `elim_{M, ms} : Π (z : S(as)). M(z)`.
- `Iota` computes a saturated eliminator application on a saturated
  constructor, at dimensions or not (3.7). `Whnf` computes it on `hcomp`.

- The eliminator in progress is a judgement of a new kind, 6, whose type is
  the next clause's `ClauseType_k`, and, with every clause given, the
  eliminator's type: the driver reads what to prove next. It is an ordinary
  derivation, cached like any other; `Step` and `Replace` refuse it.

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
- **Terms.** Instances derive through `SortBegin`, one `SortLevel` per
  recorded level and one `SortParameter` per parameter; constructors through `Construct`, `Apply`, `PathApply` and
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

**Implementation.** Admission is `admitSignature` in
`web/cubical-signatures.mjs`: from a normal form over cubical syntax it
issues the instructions above, and registers the signature by name, with
its constructor names, the generated squash named `squash`. The driver
(`web/cubical-instruction-driver.mjs`) derives the three node kinds:

- An instance converts each parameter to exactly the telescope's type,
  because `SortParameter` compares types up to bound names only. It obtains
  that type by applying a fresh entry of the former's type to the levels and
  the earlier parameters, as an application's argument is checked. An
  erased level is read from every parameter whose telescope type ends in
  `U(x)`, each first reduced to that shape, and the largest reading is used,
  so the lower parameters are lifted to it.
- An eliminator converts each clause to the type the eliminator in progress
  carries, `ClauseType_k`.
- For the search, an instance is a rigid head whose recorded levels compare
  by normal form. A constructor and an eliminator are neutral heads rather
  than rigid ones: each is a function or a path, which eta relates to a
  lambda. The guide still answers "different" for constructors of different
  numbers, and for a constructor against a variable.

`tests/h1-driver.test.mjs` covers these, checking that the search takes
`Iota`, `Path` and `Whnf` steps where this section says it does.

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

**Implementation.** `web/cubical-syntax.mjs` encodes `Sort`, `Con` and
`Elim`, naming a signature as it was registered, and decodes them with
their names. The kernel wrapper's `signatures` map holds the records, and a
declaration's transaction removes those a rollback frees. The renderers
print an instance as its name applied to its recorded levels and
parameters, `Pointed(U0)` or `List(N)`, a constructor by its name, and an
eliminator as `N.elim(motive, clauses…)` until `match` gives it a source
form. `lib/cubical/native.mjs` and the JavaScript reference checker are not
extended, as the work plan decided.

### 6.3 Transactions and caches

- A failed declaration rolls back its signature, and the JavaScript record
  with it. Driver caches keyed by term handles are dropped on rollback, as
  today.
- Import changes invalidate the signatures they admitted, and everything
  derived from them.

**Implementation.** An `inductive` declaration runs in its declaration's
transaction, which removes the registry entry and the elaborator's marker
records that a rollback frees. Import invalidation holds by construction:
each check builds a new kernel session, and the REPL replays its entries
into the new one, so a signature admitted from an old import is never seen
again.

### 6.4 The `kernel extension: H1` marker

- A declaration whose checked term or type mentions a sort, constructor or
  eliminator of a signature admitted in experimental mode carries the marker.
  It propagates through definitions, as non-computing dependencies do, and
  is tracked separately from them.
- `computable def` accepts it. `inspect`, the CLI and the workbench list it
  apart from assumptions. The migration verifier must compare it too: the
  marker is not an axiom, so an `axioms` comparison cannot establish this
  contract.
- Tests: direct use; use through a definition; `computable` with the marker
  accepted; `computable` with the marker and `LEM` rejected, naming `LEM`;
  the marker absent once H1 is on by default.

**Implementation.** The elaborator computes each result's extensions beside
its assumptions (`extensionsOf` in `web/cubical-elaborator.mjs`): an
instance or eliminator of a signature the kernel admitted experimentally,
or a definition that carries the marker. The program reports them as
`extensions`, apart from `axioms`. The CLI's `inspect` prints
"kernel extension: H1", and the workbench shows it beside the axioms used.
`computable` reads only the assumptions. `tests/inductive-declarations.test.mjs`
covers the first four tests. The last waits for default admission.
The migration verifier (`tools/proof-migration.mjs`, with
`--experimental h1` in `tools/verify-proof-migration.mjs`) compares each
declaration's `extensions` apart from its `axioms`, and refuses a migration
that adds or removes the marker (`Kernel extensions changed: none -> H1`);
until K2.3 it compared `axioms` only (audit of 2026-09-28, finding 7). It
does not yet compare a module that declares a type: the edited copy's
signature is another one, since signatures are generative (Q10), so such a
declaration is refused by name. Comparing signatures, and mapping the edited
copy's onto the original's when their normal forms agree, is K2.4a's
tooling. `tests/proof-migration.test.mjs` covers both.

### 6.5 Inspection

The inspector shows a signature's normal form (data, positions with arities
and cubes, dimensions, boundary), the generated eliminator with each clause
type, and each clause's displayed boundary, as the design's section 5 asks.

**Implementation.** `CubicalProgram.signature` reads a signature back from
the kernel: its former, h-level, recorded universe parameters by their
declared names, and each constructor's normal form with its data, positions
and dimensions, with the sort and earlier constructors shown as themselves.
It also gives the eliminator's clause types for a motive `P` over the type
at its own parameters: the kernel computes each `ClauseType_k` as L2.2a's
`match` has it do, given a variable for each earlier clause, in a
transaction rolled back afterwards. The CLI's `inspect` prints this, and the
workbench's inspector shows it for a declared type, which has no checked
term, with the marker. A dependent path type prints as the source writes
it, `PathP(fun (i : Interval) => P(loop @ i), base_case, base_case)`.
`tests/inductive-declarations.test.mjs`, `tests/cli.test.mjs` and
`tests/cubical-inspector.browser.mjs` cover it. Each clause's boundary is
shown within its type, not yet drawn as a diagram.

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

- τ is a map on terms. Native formers carry no level, and the K2.4
  counterparts have only erased parameters, so their instances carry none
  either (3.1). τ adds no level and involves no coercion or lifting: `τ(Sum(A, B)) = Plus(τ(A), τ(B))`. τ is the identity on every
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

A native former may occur at an argument in a tier-1 universe, and Q16
decided that instances read finite levels only. Call a declaration
*finite-tier* when neither it nor anything it uses, transitively, contains
a native sum, W type or pushout whose instance would read a tier-1 level.
The K2.4 counterparts have only erased parameters, so τ never needs a
recorded level.

- τ keeps each native sum, W type or pushout whose instance would read a
  tier-1 level, and maps every other occurrence; `Nat` has no parameters
  and always maps. Which occurrences stay native depends on the levels in
  the derivation. So τ commutes with substitution only on finite-tier
  declarations, where every level read stays finite before and after
  substitution, and its guarantees are stated for them only:
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
- If the later tier-parametric proposal is adopted, the four counterparts
  qualify: their derivations use only their parameters, universes at their
  level parameters, `Π`, `Σ`, projections and path types. τ then becomes
  purely syntactic and total, commuting with binders, substitution, level
  substitution and interval substitution everywhere, and
  `def big_sum(A, B : UU0) : UU0 := A or B;` becomes `Plus(A, B)`, reading
  `ω`, in `UU0`.

X1–X3 test the preservation rule by rule, and X4 and X6–X8 test it on the
archive and on the examples above.

### 7.3 Differential fixtures

| ID | Comparison | Pass condition |
| --- | --- | --- |
| X1 | Every `Nat`, sum, W and pushout case of `kernel/tests/test_instructions.c`, replayed through τ with the declared signatures | Same verdict; accepted types related by τ, up to the W arity's `Beta` |
| X2 | Weak head and normal forms of the terms those cases derive, and of each archive definition's value | `τ(nf(t))` is alpha-equal to `nf(τ(t))`, up to that `Beta` |
| X3 | Composition, homogeneous composition and transport at each type, including pushout bridges | Reducts related by τ |
| X4 | The archive, elaborated with declared forms for the four types (a driver option) | 0 gaps; every stored definition derives again; each declaration's assumptions unchanged; canonicity fixture and `evaluate` results equal |
| X5 | Cost of X4 against the native run: archive check time, re-derivation time, kernel steps, arena peak | Recorded with revision, machine and limits |
| X6 | Native terms used at two finite universes: `sum_id(U1, Nat, small)` of 2.3, and the same with W, pushout and `Nat`-valued generic definitions instantiated at `U2` | Under both options, native and image both check; the image is one instance term at both universes |
| X7 | Native formers at UU-tier arguments: `big_sum`, and a W type and a pushout over types in `UU0` | τ leaves them native and they check unchanged (Q16). Under the later proposal, native and image would both check, the image in `UU0` |
| X8 | A mixed-tier call: `big_id(Nat, small)` of 7.2, and the same through a W type and a pushout | The image fails to check, and the migration verifier rejects the declaration, naming the call (Q16). Under the later proposal, native and image would both check |

### 7.4 Retirement criterion

The hand-coded instructions retire in one change when:

1. X1–X4 and X6–X8 pass;
2. X5's gap is recorded, and either accepted by the maintainer or closed by
   specialised reduction paths for hot signatures (Q14);
3. the archive is migrated by τ under the strict verifier, with every
   public type equal after τ and every assumption list unchanged. This
   requires every archive declaration to be finite-tier (7.2), which they
   all are today; a declaration that is not is left on native formers and
   reported, not migrated in part.

As Q16 decided, the change removes the `Nat` instructions only: `Nat`,
`Zero`, `Succ` and `NatElim`, and their node kinds, whose tags stay
reserved; the ABI version changes. The sum, W and pushout instructions stay
for arguments at tier-1 levels, and the elaborator emits the declared forms
everywhere else. They stay trusted code, and X1–X3 stay as their regression
tests. A native and a declared sum of the same components are then
different types, so τ's guarantees cover finite-tier declarations only, and
a mixed-tier call has no image (7.2, X8). Nothing does that today.

If the later tier-parametric proposal is adopted, a further change removes
`Sum`, `Inject`, `SumElim`, `W`, `Sup`, `WElim`, `Pushout`, `PushPoint`,
`PushPath` and `PushElim`, without changing any finite-level term.

`Unit` and `Void` stay (Q11).

**Status on 2026-09-28.** No X fixture, no τ driver option and no cost
record exists. The work plan schedules them as K2.4a, the `Nat` retirement
above as K2.4b, and the wider retirement of the previous paragraph as
K2.4c, deferred with the tier-parametric proposal. At the source boundary,
a program with a mixed-tier call keeps its native formers and the verifier
reports it; it is never migrated in part. The archive coverage run is
compatibility evidence for the native forms, not X4.

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
  finite level (Q16). Its universe parameter is erased, so the instance
  carries no level.
- `Quotient(A, R) : U(max(x, y))` for `A : U(x)` and `R : A → A → U(y)`: its
  level accounts for the carrier and the relation. A small quotient stays
  small, without the archive's predicate encoding.
- **`Quotient` is the set quotient: it is set-truncated.** Its `set`
  modifier appends the squash constructor of 1.6, so any two parallel
  paths in `Quotient(A, R)` are equal. It keeps the classes and the paths
  `glue` makes between them, and kills all higher structure: loops that
  `glue` creates collapse, and so do the higher paths of `A` itself. That
  is the classical quotient that constructions such as `G/N`, `R/I` and the
  rationals need. Quotienting by an action while keeping the stabilizers,
  or any other higher structure, uses a declaration without the modifier,
  such as the graph quotient: for `A = Unit` and `R(tt, tt) = Unit` the
  graph quotient is the circle, and `Quotient` is a point.
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

**Status on 2026-09-28.** Not implemented: there is no ledger file, the
verifier has no ledger support (fixture G4 has no test), and no migration
has been made; the archive keeps its legacy assumptions, as G3 requires.
The two tower declarations of group 5 wait for H2, so removing every legacy
assumption is not an H1 prerequisite.

## 9. L2.1: the lowering contract

L2.1 turns `inductive` declarations
([proposal](inductive-language-features.md), design §5) into the normal
form. It is untrusted; the kernel checks the result.

- **Header.** `inductive T(U < UU0, …, A : U, …) : R` gives the former type.
  The result position `R` after the colon is one of:

  ```text
  R  ::=  m  |  E  |  m E          m ::= type | set | prop | trunc(n)
  ```

  where `n` is an integer `≥ -1` in HoTT's numbering (1.6) and `E` is a
  universe expression, as L1.1 defines it: a constant of any
  tier, a universe parameter, `next(E)` or `max(E, F)`. Examples:
  `inductive Pointed1 : U1 { pt(X : U0, x : X); }`, and
  `inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }`. Indexed
  families at H2 take the same position at the end of their index type, as
  in `: Nat -> U1`.
  - **A written universe is the declared level `ℓ`.** The kernel checks it
    as an upper bound, as for any `ℓ` (2.1), so lowering is rejected, at the
    constructor, naming the argument: in
    `inductive Bad : U0 { mk(X : U0); }`, `mk`'s data `X : U0` lives in
    `U1`. A universe above the least level is allowed, and the sort then
    lives there: `inductive Flag : U1 { on; off; }` is a type in `U1`, not
    in `U0`. When in doubt, the user writes the universe.
  - **A modifier alone, `type`, `set`, `prop` or `trunc(n)`, or no
    annotation, infers the least level** of 2.1 from the inferred types of the data and arities, as
    today.
  - **An h-level and a universe together**, `m E`, give both: the modifier
    `m` and the declared level `E`. `type U1` means the same as `U1`. The
    generated squash constructors mention only the sort, so they live in any
    declared universe, and the data alone bound it. So
    `inductive Tr(U < UU0, A : U) : prop U { point(a : A); }` is `Trunc`
    with its universe written, while
    `inductive Small(A : U1) : prop U0 { point(a : A); }` is rejected as
    lowering at `point`: it would be the resizing that K2.5 excludes.
    `inductive Gpd(U < UU0, A : U) : trunc(1) U { point(a : A); }` is the
    groupoid truncation.
  - **Contextual words.** `type`, `set`, `prop` and `trunc` are keywords
    only as the first word of the result position, and ordinary names
    everywhere else. The archive uses `prop` 226 times, `set` 37 times and
    `type` 47 times as names, and the library 19, 1 and 3 times, so they are
    not reserved. In the result position they always mean the modifier, so a
    universe parameter may not be named `type`, `set`, `prop` or `trunc`; the
    error names the parameter. The highlighter marks them as keywords in that
    position only. `trunc(-2)`, or a level that is not an integer literal, is
    rejected with a message stating the allowed levels.
  - **Classifying universe parameters.** L2.1 proposes each universe
    parameter as erased or recorded by the occurrence check of 1.1, on the
    constructor types after lowering, and the kernel checks it (5.2). A
    written universe may mention the universe parameters. A parameter
    mentioned only there, and in no parameter type, cannot be read, so it is
    recorded: `inductive Lifted(U < UU0) : U { mk; }` has a recorded `U`.
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
- **Uses.** A universe argument, as in L1.1, is checked and then placed by
  the parameter's classification. `Trunc(U, A)` checks `A : U` and
  elaborates to the instance `Trunc(A)`, which carries nothing for the
  erased `U`. `Pointed(U0)` elaborates to the instance with recorded level
  `0`. `Pointed` used as a function elaborates to the level λ
  `fun (U < UU0) => Pointed(U)`.
- **Generated names.** `T.squash` for the modifier's constructor; the
  eliminator is reached through `match` (L2.2), and `T.rec` and
  `T.ind_prop` are L2.3's.

**Implementation.** `lib/cubical/inductive.mjs` lowers a declaration, and
`CubicalProgram` admits it only with the experimental option `h1`
(`--experimental=h1` in the CLI, "Declared types (H1)" in the workbench).
Otherwise the declaration fails, and the error names the option. Decisions
this section left open:

- **The sort while constructors are elaborated.** It is a variable, typed
  at the written universe or, without one, at `UU0`, which only the
  elaborator sees. No data type or arity mentions the sort, so none depends
  on that choice. The kernel derives every constructor type again at the
  real level.
- **Instances of constructors.** A constructor of a type with parameters or
  recorded levels takes its instance from the expected type, as a sum's
  injection does. Without one, it reads the instance from an argument of
  that type, which only a position can have: `cons(zero, xs)` for
  `xs : List(U0, N)`. Otherwise it asks for `typed(T(…), c(…))`. Inferring
  the instance from data arguments waits for L4.1a.
- **Types as written.** Argument and result types are checked by the kernel
  as written, then beta-reduced, level redexes included, before they are
  classified and admitted, so `l : typed(C, b) = b` has a constructor
  expression for a boundary. An argument that mentions the sort but is not a
  cube over it, or whose arity does, is refused by name before admission,
  and a refusal the kernel makes names its constructor. Binders written in a result, as
  in `s : M -> M`, are arguments of the constructor.
- **The former as a value.** Used alone, a type with parameters is its
  former, `fun (U < UU0) => Pointed(U)`, a lambda over its universes and
  parameters.
- **Uses keep the source's order.** `node(l, a, r)` is applied as the
  normal form's `node(a, l, r)`. A constructor whose order changed is
  applied to all its arguments. Partial application is refused, with a
  message saying why.
- **Uniformity.** Inside its declaration, the type is written applied to
  exactly its own parameters, `List(U, A)`. Any other argument is refused
  as an index.

`T.squash` names the generated constructor (L2.2a), and `trunc(-1)`, the
same as `prop`, is written with the minus sign of the path notation.

## 10. Acceptance cases

Tests name cases by ID: the kernel tests do so in comments, as `A3`, and
source tests should do the same, so that 10.10 can trace them. "Kernel"
cases are issued directly in `kernel/tests/test_signatures.c`; "source"
cases go through the elaborator and the driver, with L2.1. All run with the
H1 extension on, except T1.

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
| A17 | `Gpd(A)`, modifier `trunc(1)`, with `point : Π (a : A). s` | Accept | The generated squash of 1.6 has positions of cube depth 0 to 2 and three dimensions |

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
| V8 | `Trunc(A)` and `Pair(A, B)` for `A, B : UU0` | Reject | A tier-1 read level (Q16, decided) |
| V9 | the elaborator's `fun (U < UU0, A : U) => Trunc(A) : Π (x < ω). Π (A : U(x)). U(x)`, in `U(ω)` | Accept | A declared type used as a function |
| V10 | `Big(A : UU0) { wrap(a : A); } : UU0`; its eliminator into `UU1` | Accept | Fixed tier-1 signature; any motive universe |
| V11 | instantiating a generic definition that mentions `Trunc(A)` at `x + 1`, and reducing `elim` on `point` | Accept | Level substitution leaves the instance unchanged (2.4) |
| V12 | `Wrap(x < ω) : U(x + 1) { wrap(B : U(x)); }` | Accept, `x` recorded | Level-dependent (Q15, decided) |
| V13 | `Mixed(x < ω, A : U(x), B : UU0) { mk(a : A, b : B); }`; `Mixed(A, B)` for `A : U(3)`; for `A : UU0` | Accept, not tier-parametric; Accept; Reject | A tier-1 constant bounds the instances to finite levels (Q16) |
| V14 | a level parameter that ends no parameter's type, proposed as erased | Reject | An erased parameter needs a determining occurrence (1.1); left to the classification it is recorded (V30) |
| V15 | `Both(x < ω, A, B : U(x)) { mk(a : A, b : B); }` at `A : U(0)` and `B : U(1)`; the same after lifting `A` to `U(1)` | Reject; Accept | Conflicting reads of one level parameter (3.1) |
| V16 | `(λ (x < ω). Trunc(U(x))) {0}` and its `Beta` reduct `Trunc(U(0))`; `point(Nat)` at both; an eliminator of `Trunc(U(x))` with motive into `U(x + 1)`, instantiated at `0` | Accept; convertible; Accept; the motive lands in `U(1)` | Level substitution recurses through parameters and motives (2.4) |
| V17 | `Tag(A : UU0) : U0 { here; }` and `Outer(x < ω, A : U(x)) : U0 { wrap(t : Tag(A)); }`; `Outer(Nat)`; `Outer(UU0)`; `Outer(A)` for `A : UU0` | Accept, and not tier-parametric under the extension (rules 2 and 3); Accept; Reject; Reject | A bound hidden in a referenced signature's parameter type (2.3) |
| V18 | a signature whose constructor type uses a definition `F(A : UU0) : U0`, as in `wrap(t : F(A))`, at `A : UU0` | Reject at the instance; not tier-parametric under the extension (rule 2) | A bound hidden in a definition's type (2.3) |
| V19 | `Big : UU1 { pack(B : UU0); }` and `Outer2(x < ω, A : U(x), F : Big → U0) : U0 { wrap(t : F(pack(A))); }`; `Outer2(Nat, F)`; `Outer2(UU0, F)`; `Outer2(A, F)` for `A : UU0` | Accept both, neither tier-parametric under the extension (rules 2 and 3); Accept; Reject; Reject | A bound hidden in a parameter-free signature's constructor type (2.3) |
| V20 | source: `inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }`; `Pointed(U0) : U1`; `Pointed(U1) : U2`; `Pointed(U0)` and `Pointed(U1)` convertible | Accept, `U` recorded; Accept; Accept; Reject | Recorded parameter; distinct instances (Q8, Q15) |
| V21 | source: `def lift(p : Pointed(U0)) : Pointed(U1) := match p { pt(X, x) => pt(X, x); };` | Accept | A map between instances, with `X : U0` used at `U1` by cumulativity (needs L2.2's `match`; the kernel case is the eliminator into `Pointed{1}`) |
| V22 | source: `def same(p : Pointed(U0)) : Pointed(U1) := p;` | Reject | A `Pointed(U0)` value is not a `Pointed(U1)` value |
| V23 | source: `inductive Pointed(U < UU0) : U { pt(X : U, x : X); }` | Reject at `pt`, naming `X` | Lowering: `X : U` lives in `next(U)` |
| V24 | kernel: `Holder(x < ω, A : U(x)) : U(x + 1) { hold(B : U(x)); }` with `x` proposed erased; the same with `x` recorded | Reject at `hold`; Accept | An erased parameter in a constructor type would give a type containing its own code (2.3) |
| V25 | source: `inductive Tagged(U, V < UU0, A : U) : max(U, next(V)) { tag(a : A, B : V); }`; `Tagged(U0, U0, A)` for `A : U0`, and with `A` lifted to `U1`; `Tagged` at `V := U0` and `V := U1` | Accept, `U` erased and `V` recorded; one instance term in both; distinct | A mixed signature (Q8) |
| V26 | source: `inductive Pointed1 : U1 { pt(X : U0, x : X); }`; `pt(Nat, 3) : Pointed1` | Accept; Accept | A fixed-level signature storing a small type, with its universe written (9) |
| V27 | source: `inductive Bad : U0 { mk(X : U0); }` | Reject at `mk`, naming `X` | A written universe is checked as an upper bound (9) |
| V28 | source: `inductive Flag : U1 { on; off; }`; `Flag : U1`; `Flag : U0` | Accept; Accept; Reject | A written universe above the least level is where the sort lives (9) |
| V29 | source: `inductive Tr(U < UU0, A : U) : prop U { point(a : A); }`; `inductive Small(A : U1) : prop U0 { point(a : A); }` | Accept; Reject at `point` | An h-level with a written universe; lowering would be resizing (9, K2.5) |
| V30 | source: `inductive Lifted(U < UU0) : U { mk; }`; `Lifted(U0)` and `Lifted(U1)` convertible | Accept, `U` recorded; Reject | A parameter only in the written universe cannot be read, so it is recorded (9) |
| V31 | source: `inductive Gpd(U < UU0, A : U) : trunc(1) U { point(a : A); }`; `inductive T(prop < UU0) : prop { t; }`; `inductive B : trunc(-2) { b; }`; `def prop(x : Nat) : Nat := x;` | Accept; Reject naming the parameter; Reject stating the allowed levels; Accept | Q18 and the contextual words of 9 |

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
| E11 | `Gpd`'s eliminator into a family of groupoids, with the squash clause from h-level evidence (L2.2b) | Accept; computes on `point` |

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

**Progress.** The circle's winding number is checked in source, in
`docs/examples/h1/winding.cubist`, through declared integers, `match` and
univalence. It gives 1 for `loop`, 2 for `loop · loop` and -1 for its
inverse, by `rfl`, and closed `evaluate` directives read the normal forms.
`cong(code, loop)` is `ua(succ)` by `rfl`, the E2 fixture's
`code_meridian` in this form. `tests/declared-match.test.mjs` checks the
example with the experimental option. Its results carry the H1 marker and
no assumption. The native comparisons (X1–X8) are K2.4's, and `Quotient`'s
elimination waits for automatic set clauses (L2.2b).

### 10.9 Resources and malformed input

| ID | Input | Verdict |
| --- | --- | --- |
| R1 | malformed `CC_SORT`, `CC_CON`, `CC_ELIM` or `CC_LIST` nodes; indices out of range | Reject; inspection stays inert |
| R2 | a signature at the constructor or argument limit, and one above it | Accept; Reject |
| R3 | a constructor with cube depth 8 and arity 64 | Accept within budget |
| R4 | a client with ABI version 2 | Refused |
| R5 | an encode and decode round trip of every new kind | Identical handles |

### 10.10 Coverage of the acceptance cases

Status on 2026-09-29, to be kept current with each change to sections
5–10. *Traced* means a test names the case by its ID, in the layer its
entry gives: a kernel case in `kernel/tests/test_signatures.c`; a driver,
source or verifier case in `tests/h1-acceptance.test.mjs`,
`tests/h1-admission.test.mjs`, `tests/h1-driver.test.mjs`,
`tests/inductive-declarations.test.mjs`, `tests/declared-match.test.mjs`
or `tests/corpus.test.mjs`. *In part* marks a case whose rest is listed as
not traced, and *in substance* a test that differs from its case in a
detail the entry states. *Not traced* means no test covers it yet, and
*Missing* that none can exist yet, for the stated reason.
`tests/acceptance-matrix.test.mjs` checks this table against the cases
above and against the tests.

| Group | Traced | Not traced | Missing, and why |
| --- | --- | --- | --- |
| Admission A1–A17 | Kernel: A1 (`N`, `List`, `S1`, `Tree`, `Push` and `Susp` across its sections), A2–A17. Driver: A2, A8. Source: A4, A8, A11, and the uniformity refusal of 9 | — | — |
| Universes V1–V31 | Kernel: V1, V4, V7, V8, V13–V20, V24, V25. For V13 and V17–V19, H1's rule: each signature is admitted, and an instance that reads a level of tier 1 is refused; the tier-parametric flag of 2.3 is the later proposal's (Q16). Source: V2, V3, V5, V6, V9–V12, V21–V23, V29, and in substance V7 and V20 (an erased parameter read, a recorded one carried), V26–V28 (`Pointed1`, `Bad`, `Flag`), V30 (`Lifted`), V31 (the contextual words and `trunc(-1)`) | — | — |
| Boundaries N1–N6 | Kernel: N1–N4. Driver: N1, N3. Source: N5, N6 | — | — |
| Kan K1–K11 | Kernel: K1 in part (with no tubes, a composition pushes into `succ`), K2 in substance (in `N` rather than `Plus`), K3, K4 in substance (in `Susp` rather than `S1`), K5 in substance (the argument of `merid`, not a point constructor's), K6 in part (transport of `merid` along a line of types `e : A = B`, not along `ua`), K7, K8, K9 in substance (a higher sort's `comp` reduces to `hcomp`) | K1 with tubes; K6 along `ua` | K10, K11: no randomized H1 generator exists; the randomized level tests cover G0 |
| Elimination E1–E11 | Source: E1 (`docs/examples/h1/winding.cubist`), E2 (as `cong(code, loop)` equal to `ua(succ)` by `rfl`), E3 (`T.squash`), E8 (a missing clause, a duplicate clause, an unknown constructor). Kernel: E3 (the `prop` squash clause), E5–E7, E9, E10, and a motive over no declared type refused. Driver: E5 | — | E4 and E11: automatic set and groupoid clauses (L2.2b) |
| Trust T1–T7 | Kernel: T1, T5, T6, T7. Driver: T5, T6. Source: T1 (the option named when off), T2 (direct, through a definition, through an import), T3, T4. Verifier: the marker compared apart from assumptions (6.4) | — | — |
| Truncation policy G1–G7 | Source: G1 (`Tr(U1, U0)` is not in `U0`), G3 (the archive checks in full; the audit's coverage run counted 3,804 declarations and 0 gaps) | — | G2, G4, G5, G6, G7: the ledger verifier and the migrations (K2.5) |
| Resources R1–R5 | Kernel: R1 (a sort, constructor and eliminator whose indices are out of range, and a list whose next cell is no list, built as raw syntax: inspected, reduced or refused with an error, and refused by the term checker and the instructions), R2, R3; a former of the wrong shape and a truncation level above the maximum are refused. Driver: R1 in part (an operand that is not a 32-bit unsigned integer is refused), R5 (the codec round trip); `tests/h1-admission.test.mjs` checks ABI version 3. Source: R4 (a module of ABI version 2 refused by the loader) | — | — |
| Differential X1–X8 | — | — | All: K2.4a |

## 11. Open questions

Every question below was decided on 2026-09-27: Q8, Q15, Q16 and Q18 as
the Decisions section records, and the others as recommended.

| Question | Decision |
| --- | --- |
| Q1. Formal composition for data sorts | None |
| Q2. Heterogeneous formal composition along parameter lines | No; Coquand–Huber–Mörtberg's split |
| Q3. What boundaries may contain | Constructor expressions only |
| Q4. Partial boundaries | Not in H1 |
| Q5. How constructors take dimensions | Path-valued constructors |
| Q6. The eliminator's form | A function node with every clause |
| Q7. Who computes the sort's level | Declared, checked as a bound: written in the header, or the least, inferred by the elaborator |
| Q8. Level irrelevance across instances | Decided: per universe parameter; erased parameters are one term at every universe, recorded ones give distinct instances |
| Q9. Cube and infinitary positions in higher sorts | Admit both |
| Q10. Are signatures generative | Yes |
| Q11. `Unit` and `Void` | Keep native |
| Q12. Resizing | No resizing assumption; the seven remedy groups of 8.4 (revised) |
| Q13. Where the experimental gate lives | In the kernel |
| Q14. Specialised reduction after retirement | Decide from X5 |
| Q15. Level-dependent signatures | Decided: admitted, with the parameter recorded |
| Q16. Instances at tier-1 levels | Decided: finite levels only; native sum, W and pushout kept for tier-1 arguments; the tier-parametric extension a later proposal |
| Q17. Declarations that assert a large proposition is small | A hypothesis, `LEM` where present, or H2's inductive tower (new) |
| Q18. Truncation levels | Decided: `trunc(n)` for `n ≥ -1` in HoTT's numbering; `prop`, `set` and `type` for -1, 0 and untruncated |

**Q1. Formal composition for data sorts.** The design gives every sort one
formal composition that pushes through constructors when it can. A formal
element that also pushes is not confluent with its eliminator, and whether
it pushes changes under substitution (4.3, D2). *Decided, as recommended:* data sorts
have no formal composition; composition pushes through equal heads and is
otherwise neutral, exactly as `Nat`, sums and W types compute today, which
keeps K2.4's comparison exact.

**Q2. Heterogeneous formal composition along parameters.** The design's
`fcomp` runs along a line of parameters and indices. With parameters only,
the eliminator's motive is over the sort at fixed parameters, so an `fcomp`
joining two parameter values could not be eliminated. *Decided, as recommended:* H1 uses
formal `hcomp` at fixed parameters and computes transport, as
Coquand–Huber–Mörtberg and the kernel's pushouts do. The heterogeneous form
returns in H2 along index lines, where the motive ranges over indices.

**Q3. What boundaries may contain.** The design allows formal compositions
in boundaries. No H1 example needs them. With constructor expressions only,
clause types follow by substitution (Lemma H1), and the correction walls of
3.5 need no composition in the boundary. *Decided, as recommended:* constructor
expressions only; revisit with a concrete use.

**Q4. Partial boundaries.** A boundary on some faces only, such as
`c(i) [i = 0 ↦ a]`, would need cubical extension types in the kernel, which
it lacks. *Decided, as recommended:* cube boundaries only. Every example of 1.8 has one.

**Q5. How constructors take dimensions.** The alternative is a node carrying
`d` interval formulas, as `PushPath` carries one. *Decided, as recommended:* path-valued
constructors. Boundary reduction is then the existing path step, overlap
agreement is typing, and the driver reuses its path handling.

**Q6. The eliminator's form.** Native `NatRec` is saturated with its value;
`PushElim` is a function. *Decided, as recommended:* a function node carrying the motive
and every clause, applied by `Apply`, with `Iota` on the saturated form. A
level-quantified constant cannot serve, because the motive's universe must
range over UU tiers too (2.4).

**Q7. Who computes the sort's level.** The kernel cannot infer principal
levels, so it cannot check a maximum. *Decided, as recommended:* the former's type
declares `ℓ`; the kernel checks that every constructor type lives in `U(ℓ)`,
which bounds every data type and arity. The user may write it in the
header (9); otherwise the elaborator declares the least level. The
alternative, a kernel-computed level, would need principal-level inference
in the kernel.

**Q8. Level irrelevance across instances.** G0 decided that instances of a
generic type at different levels are distinct (G0 Q1), and asked to
revisit at H1. The native formers carry no level, and a generic definition
instantiated at `U1` accepts a sum built at `U0` (2.3), so distinct
instances cannot translate them faithfully. But a signature that stores a
type of its own level, such as `Pointed`, has genuinely different instances
at different levels. *Decided,* per universe parameter, as Coq's cumulative
inductive types decide by variance:

- *erased*: a parameter that occurs only in parameter types, and can be
  read from their judgements. Its instances are one term at every
  universe. This covers `Trunc`, `Plus`, `List`, `W`, `Pushout` and
  `Quotient`, and keeps K2.4's translation as it is. D9 argues soundness;
- *recorded*: a parameter that occurs in a constructor type, or cannot be
  read from the parameters. Instances carry it as an explicit level
  argument, and instances at different levels are distinct, following G0
  Q1. This is standard universe polymorphism and needs no new argument
  (D8).

Admission classifies each parameter by a syntactic occurrence check, and
the kernel records the classification and checks that no erased parameter
occurs in a constructor type (1.1, 5.2, V24). Every level is finite (Q16).
G0 Q1's rule stays unchanged for generic definitions and assumptions.

**Q9. Cube and infinitary positions.** The `set` squash needs path
positions, and W-like constructors in higher sorts need infinitary ones.
*Decided, as recommended:* admit both (D4, D5).

**Q10. Are signatures generative.** Two textually identical declarations
could be one type or two. *Decided, as recommended:* generative: each admission is a new
sort, as each definition is a new constant. Identification is a theorem.

**Q11. `Unit` and `Void`.** They are not in K2.4's oracle list.
*Decided, as recommended:* keep them native. Declaring them for comparison is allowed,
and retiring them is a later, separate decision.

**Q12. Resizing.** The first draft proposed raising universes for the tower
and the unions. Review showed the tower's remedy cannot close: quantifying
over `A → U1` puts membership in `U2`. The union of independent sets has
the same shape. The measured roots now have the seven remedy groups of 8.4,
none a resizing assumption. *Decided, as recommended:* no resizing assumption in the
rebuilt foundation. Apply 8.4 when those areas are rebuilt. `PropResizing`
stays unused unless a rebuilt result proves to need it.

**Q13. Where the experimental gate lives.** In the elaborator only, or in the
kernel too. *Decided, as recommended:* in the kernel, so no client can admit a signature
by accident before review.

**Q14. Specialised reduction after retirement.** Generic reduction may be
slower than the hand-coded rules (design open question 4). *Decided, as recommended:*
decide from X5's measurements; specialised paths, if any, must be observably
identical to the generic rules and tested against them.

**Q15. Level-dependent signatures.** A signature whose constructor types
mention a level parameter, such as `pt(X : U, x : X)`, stores types of that
level. The first drafts excluded them. *Decided:* reversed. They are
admitted, with that parameter recorded (Q8), so
`inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }` checks, with
`Pointed(U0) : U1` and `Pointed(U1) : U2` distinct (V20–V23). A header may
state such a universe after the colon, mentioning the universe parameters
(9).

**Q16. Instances at tier-1 levels.** Admission checks a signature at finite
levels only, so reading a tier-1 level needs more. Two syntactic criteria
failed review, because a bound can hide in a type the signature uses:
`Outer` over `Tag(A : UU0)`, and `Outer2` over the parameter-free
`Big : UU1 { pack(B : UU0); }`. Two options were set out: a
tier-parametric extension, with a kernel check of the admission
derivation (2.3), and a conservative first release. *Decided:* the
conservative first release.

- Instances read and carry finite levels only, erased and recorded alike.
- The native sums, W types and pushouts stay for arguments at tier-1
  levels. K2.4 retires only the `Nat` instructions, and the elaborator
  emits declared forms at finite levels (7.2, 7.4).
- Its cost: three hand-coded formers stay trusted code, with their
  differential tests as regressions. A native and a declared sum of the
  same components are different types, which shows only in a mixed-tier
  call (X8). No archive or library declaration uses a tier-1 universe as a
  type, so none shows today.
- The tier-parametric extension stays specified in 2.3 as a later proposal,
  for when a rebuilt result needs a declared type at `UU0`, for example
  through proposal E2. Adopting it later only accepts more instances, and
  changes no finite-level term. A tier-1 constant stays allowed in any
  signature, and bounds it to finite instances (`Mixed`, V13).

**Q17. Declarations that assert a large proposition is small.** Groups 4
and 5 of 8.4 state that the union of a large family, or the impredicatively
defined tower, is small. No universe choice makes that true predicatively.
*Decided, as recommended:* for the tower, the predicative construction: an indexed
inductive family at H2, with the two declarations waiting for it. For the
unions, an explicit smallness hypothesis, discharged from `LEM` by the one
consumer that already uses it. The alternative for both, proving the
statement from `LEM` directly, would add `LEM` to declarations that do not
use it today.

**Q18. Truncation levels.** 1.6 first generated only the `prop` and `set`
squash constructors, which are levels -1 and 0 of one pattern. *Decided:*
the modifier is `trunc(n)` for any integer `n ≥ -1`, in HoTT's numbering, so
`trunc(1)` is a groupoid; `prop`, `set` and `type` name levels -1, 0 and
untruncated. The kernel generates the squash for any `n`, and D4 must cover
positions of every cube depth. Levels from 1 up are usable once automatic
clauses exist (L2.2b), and a first implementation may enable them then. The
elaborator translates to the library's numbering, which counts from
`IsProp` at 0, by adding one.
