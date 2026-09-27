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
for its first stage, and it keeps the level contract of the
[G0 specification](historical/g0-universe-specification.md) (its sections
2.12 and 6, Q1 and Q6). The [work plan](work-plan.md) schedules the packages.
Where this document narrows or departs from the design, section 0 says so and
section 11 asks for a decision.

## 0. Relation to the adopted design

The design fixes one signature format for H1–H4. For H1 this document makes
six choices precise. Each is an open question in section 11 with a
recommendation.

| Design statement | H1 as specified here | Why |
| --- | --- | --- |
| One heterogeneous formal composition `fcomp` per sort, along a line of parameters and indices | Higher sorts get a formal homogeneous `hcomp` at fixed parameters; transport along a parameter line computes by recursion on its argument; general composition is `hcomp` after transport (Q1, Q2) | An eliminator's motive is over the sort at fixed parameters, so a formal element joining two parameter values could not be eliminated. This is Coquand–Huber–Mörtberg's split, which the kernel already implements for pushouts. |
| `fcomp` pushes through constructors of sorts without path constructors | Data sorts get no formal composition at all; composition pushes through equal constructor heads and is otherwise neutral (Q1) | A formal element that also pushes breaks confluence and stability under substitution. This is how the hand-coded `Nat`, sums and W types compute. |
| Boundaries may mention earlier constructors and formal compositions | Boundaries are constructor expressions: positions and earlier constructors at interval formulas, with no compositions (Q3) | Displayed boundaries then follow by substitution; every H1 example needs no more. |
| Boundaries are systems on faces of the constructor's dimensions | Boundaries are cube boundaries: a piece on both faces of every dimension (Q4) | A cube boundary is an iterated path type, which the kernel already has. Partial boundaries would need extension types. |
| Constructors take dimension arguments | A constructor with dimensions is a function into an iterated path type, applied at interval formulas by path application (Q5) | Boundary reduction is then the kernel's existing path step, and overlap agreement is typing. |
| A sort's level is the maximum of its data and arity levels | The former's type declares the level; the kernel checks that every constructor type lives in that universe, and the elaborator declares the least such level (Q7) | The instruction kernel does not infer principal levels. |

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
  those types. Lowering and mismatched level instances are rejected.
- **Trust.** Admission requires the kernel's H1 extension flag until review.
  Results carry `kernel extension: H1` transitively; it is visible, and it is
  not a non-computing dependency.
- **Differential oracle (K2.4).** `Nat`, sums, W types and pushouts are
  declared as signatures and compared with the hand-coded instructions by an
  explicit translation. Native and declared forms are different types; no
  conversion relates them.
- **Truncation (K2.5, G2).** `Trunc` is universe-preserving and has no
  resizing. The archive keeps its legacy assumptions. Measured on the archive,
  a universe-preserving truncation breaks 47 of 3,804 declarations, from 8
  roots; their remedies need no resizing assumption (section 8).

## Notation

| Symbol | Meaning |
| --- | --- |
| `S` | the sort being declared; also its instance `S {ℓ⃗} a⃗` when parameters are clear |
| `x⃗` | the signature's level parameters, each `x < ω` |
| `p⃗ : P⃗` | the signature's term parameters, a telescope over `x⃗` |
| `ℓ` | the sort's level, a level expression over `x⃗` |
| `c_1 … c_n` | constructors, in order; `c_k` also names the constant after admission |
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

- The telescope starts with level parameters `x⃗ < ω`, then term parameters
  `p⃗ : P⃗`, each type well formed over the ones before. This matches G0's
  prenex universe parameters (G0 Q8).
- Parameters are uniform: every occurrence of `S` inside the signature is at
  the declared parameters. A constructor cannot mention `S` at other
  arguments; that is an index, which is H2.
- A signature may also be stated at fixed levels, including UU-tier levels,
  with no level parameters. A level-generic signature ranges over small
  universes only, like generic definitions (G0 2.12, Q10).

### 1.2 Constructor normal form

The kernel accepts a constructor type `T_k` only in this shape. `s` is the
sort entry and `c_1 … c_{k-1}` are the entries of the earlier constructors
(section 5.3).

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
E' ::= E  |  λ (y : A). E'  |  ⟨i⟩ E'    positional arguments: under the arity's binders and a cube's dimensions
```

- `u⃗` are *data terms*: any terms that mention no `s`, constructor or
  position. They may mention parameters, data, arity variables, and
  dimensions of enclosing paths.
- `r` is any interval formula over the dimensions in scope: the enclosing
  paths' dimensions of the result or of the position's cube.
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
- Induction-recursion (design open question 2).

### 1.8 Examples in normal form

Level parameters are written `x`, `y`, `z`; `U(x)` is the universe. `Path(S, a, b)`
abbreviates `Path(i; S, a, b)` when `i` is not used.

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
`Path(j; s, p @ 0, p @ 0)`, which the path step reduces to it. In
`Pushout`, `fst(m)(c)` is a data term.

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
  and `0` when there are none (Q7). With G0's Q1 this keeps one instance in
  practice: `Trunc {0} A` for `A : U(0)`.

### 2.2 Fixtures by case

| Case | Declaration | Level |
| --- | --- | --- |
| Phantom parameter | `Box(x < ω, A : U(x)) { mk(n : Nat); }` | `U(0)` at every `x` |
| Stored data | `Pair(x, y < ω, A : U(x), B : U(y)) { mk(a : A, b : B); }` | `U(max(x, y))` |
| Arity | `W(x, y < ω, L : U(x), B : L → U(y))` | `U(max(x, y))`: `B(l)` is an arity |
| Relation | `Quotient(x, y < ω, A : U(x), R : A → A → U(y))` | `U(max(x, y))`: `r : R(a, b)` is data of `glue` |
| Large parameter only | `Tag(A : U(1)) { here; }` | `U(0)` |
| Tier 1 at fixed levels | `Big(A : UU0) { wrap(a : A); }` | `UU0` |

Indices, the fifth case the work plan lists, arrive with H2; the rule then
counts index types too (G0 2.12).

### 2.3 Rejections

- **Lowering.** A constructor type that needs a level above `ℓ` cannot be
  derived at `U(ℓ)`, since no instruction lowers a universe. Example:
  `Small(x < ω, A : U(x)) : U(0) { wrap(a : A); }` is rejected at `wrap`.
- **Mismatched instances.** `S {ℓ⃗} a⃗` and `S {ℓ⃗'} a⃗` are different types
  unless `ℓ⃗` and `ℓ⃗'` have equal normal forms (G0 Q1). So `point {0} A a` is
  not a term of `Trunc {1} A`, even for `A : U(0)`. Cumulativity lifts
  `Trunc {0} A : U(0)` to `U(1)` as a type; it does not identify the two
  instances.
- **Levels at the former.** `Trunc {ω}` is rejected by `LevelApply`, which
  requires a finite level. A signature at UU-tier levels is written at fixed
  levels (1.1).
- **The former's universe is not the sort's.** The former's type is a level
  quantification: `Π (x < ω). Π (A : U(x)). U(x)` lives in `U(ω)`. An instance
  `Trunc {x} A` lives in `U(x)`. G0 keeps these apart, and so does H1.

### 2.4 Level substitution

- A signature's recorded types mention `x⃗` free. The constants `S`, `c_k`
  are level quantifications over `x⃗`, and `LevelApply` substitutes finite
  levels with G0's capture-avoiding substitution (G0 2.8). No H1 rule reads a
  level, so Lemma 5 of G0 extends: reduction commutes with level
  instantiation of generated constants.
- The eliminator's motive may land in `U(l')` for any `l'`, including a
  level variable and a UU-tier constant. The eliminator is therefore a node,
  not a level-quantified constant: a constant would bind the motive's level
  below `ω` (5.2).

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

`Former(S) : Π (x⃗ < ω). Π (p⃗ : P⃗). U(ℓ)`. An instance `S {ℓ⃗} a⃗` is built by
`LevelApply` and `Apply` and lives in `U(ℓ[x⃗ := ℓ⃗])`.

### 3.2 Constructors and boundary reduction

- `c_k : Π (x⃗ < ω). Π (p⃗ : P⃗). T_k[s := S {x⃗} p⃗, c_m := c_m {x⃗} p⃗]`.
- A saturated application `c_k {ℓ⃗} a⃗ u⃗ e⃗` is canonical. With `d_k ≥ 1` it is a
  path, and `(c_k … ) @ r_1 … @ r_d` with no `r_l` an endpoint is canonical.
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
⟦λ (y : A). E'⟧'  :=  λ (y : A). ⟦E'⟧'           ⟦⟨i⟩ E'⟧' := ⟨i⟩ ⟦E'⟧'
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

1. **Level decomposition.** By G0's decomposition lemma (G0 3.2) a
   level-generic signature is interpreted separately at each assignment of
   levels. Every H1 obligation is therefore argued at fixed levels.
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
| D1 | A general schema, where Coquand–Huber–Mörtberg treat examples | Steps 2–6 of 4.2 are uniform in the signature. The only signature-specific facts used are the constructor order (for restriction), the cube boundary's typing (for overlaps) and positivity (for the inductive definition). | New argument; to be reviewed |
| D2 | Data sorts have no formal composition | Composition by recursion on constructors is CCHM's treatment of natural numbers and the kernel's of sums and W types. Adding a formal `hcomp` that also pushes would break confluence: `elim` of a pushed and of a formal composition differ (clause of compositions against composition of clauses). | Standard for the three hand-coded types; general case argued |
| D3 | Transport with boundary correction for `d ≥ 1` | 3.5 generalises the pushout rule. The walls agree on overlaps because boundary pieces agree on corners, and the result restricts to the transport of each boundary piece. | New for `d ≥ 2`; to be reviewed |
| D4 | Cube positions (paths as arguments), needed by `set` squash | In step 2 a cube position is an element of the carrier at a higher cube with its boundary: still strictly positive. | Argued |
| D5 | Infinitary positions in higher sorts | Step 4's inductive definition allows infinitary generating clauses; the metatheory needs the corresponding well-founded trees, which ZFC provides. | Argued |
| D6 | Path-valued constructors | A presentation of dimension arguments: `c @ r` is the constructor at `r`. It changes no rule of the model. | Argued |
| D7 | Motives in any universe, including UU tiers | The eliminator is defined in the model at each fixed level, and a motive's universe plays no role in its definition. | Argued |
| D8 | Level-generic signatures | G0's decomposition (G0 3.2, 2.12): no H1 rule reads a level. | Argued; relies on G0 |

**Lemma H1 (clause typing is the partial eliminator).** For a constructor
expression `E` over positions `q⃗` and earlier constructors, and the
substitution `σ := [q̄ := λ y⃗. elim^{C}(q(y⃗))]`, `⟦E⟧σ ≡ elim^{C}(E)` by `Iota`
steps. Proof: induction on `E`. For `q_j(u⃗)`, both sides are
`elim(q_j(u⃗))`. For `c_m(u⃗, E⃗')`, the right side takes one `Iota` step to
`m_m(u⃗, E⃗', elim(E⃗'))`, which is the left side by induction. Path
application commutes with both sides. Status: proved here in outline.

**Lemma H2 (stability).** Every rule of 3.3–3.7 commutes with substitution
of interval formulas for dimensions, and of level expressions for level
variables. Argument: the redex patterns mention constructor heads, `hcomp`,
transport and path application, which substitution preserves. The
side conditions that do change under substitution are "a formula is an
endpoint" and "a face holds"; when one becomes true, the boundary and face
rules apply, and the correction walls of 3.5 are built so that the result
restricts to the boundary (3.5, case 2). Data-sort composition gains a redex
under substitution only when a neutral tube becomes a constructor, which
is a new reduction, not a changed one. Status: argued; the full check is an
obligation.

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
| The model of 4.2 for the whole schema | Argued from Coquand–Huber–Mörtberg's construction (D1–D8); **not written out** |
| Transport with boundary correction for `d ≥ 2` | Argued (D3); **to be reviewed**, with the property tests of section 10 |
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

## 5. K2.2: instruction families

Each family is reviewed and merged separately with its rejection tests,
then integrated (work plan stage 2). Nothing is added to the term checker or
the JavaScript reference checker.

### 5.1 Node kinds and tables

Tags 1–49 keep their numbers. New kinds are appended:

| Tag | Kind | Payload and children |
| --- | --- | --- |
| 50 | `CC_SORT_REF` | payload: signature index; no children. The former constant. |
| 51 | `CC_CON_REF` | payload: constructor index in the kernel's constructor table; no children. A constructor constant. |
| 52 | `CC_ELIM` | payload: signature index; child 0: motive; child 1: clause list. A function on the sort. |
| 53 | `CC_CLAUSE` | child 0: a clause; child 1: the next cell, or 0. |

- `CC_HCOMP` and `CC_TRANS` keep their layout. Their family may be any higher
  sort instance, not only a pushout.
- **Signature table.** Each entry records: its state (open or admitted); the
  former's type; the level and parameter binder symbols; the sort symbol and
  level `ℓ`; the h-level modifier; and, per constructor, its symbol, its type
  `T_k` over the admission symbols, the split between data and positions,
  each position's arity length and cube depth, and `d_k`. The constructor
  table maps a constructor index to its signature and position.
- Tables are truncated with the syntax arena on rollback and on
  `commit_checkpoint`, as definitions are. An admitted signature is never
  modified.

### 5.2 Family F1: admission

- `SignatureBegin(former, modifier, sort symbol)`: from a closed judgement
  `⊢ F : U(…)` whose term `F` is `Π (x⃗ < ω). Π (p⃗ : P⃗). U(ℓ)`, open a
  signature. The binder symbols of `F` name the admission context's level and
  parameter entries, and the sort symbol names `s : U(ℓ)`. Returns a
  signature judgement (a new judgement kind, like a composition system).
- `SignatureConstructor(signature, type, symbol)`: from `Γ ⊢ T_k : U(ℓ)`, where
  every entry of `Γ` is a level or parameter entry of the signature (by symbol,
  at an alpha-equal type), the sort entry, or an earlier constructor's entry
  at its recorded type: check the shape and positivity of 1.2–1.5, and record
  `c_k`. The universe must be exactly `U(ℓ)`, compared by level normal form;
  the driver lifts below it. The check reads the syntax as written, with no
  reduction: a data type written `(λ (X : U(0)). Nat)(s)` mentions `s` and is
  rejected. The driver presents `T_k` with such redexes contracted.
- `SignatureClose(signature)`: append the generated squash constructors for
  the modifier, mark the signature admitted, and return
  `⊢ S : Π (x⃗ < ω). Π (p⃗ : P⃗). U(ℓ)`.
- `Former(sort reference)` and `Constructor(sort reference, k)` recall an
  admitted signature's constants, as `Lookup` recalls a definition.

The admission context's entries are ordinary entries, made by `Level` and
`Extend`, and the constructor types are derived by ordinary instructions. A
judgement in that context is open in `s` and the constructor entries, so
`Define`, which admits closed judgements only, can never publish one.

**Rejections, each a test:** a former type not of the stated form; a
constructor judgement with a foreign entry, or an entry at another type; a
universe other than `U(ℓ)`; each positivity and shape violation of 1.3 and
1.4, a composition in an endpoint included; data after a position; an
arity mentioning a position; a self or forward reference
(1.5); admission while the H1 extension is disabled (5.7); `SignatureClose`
twice; any use of an open signature's constants.

### 5.3 Family F2: formers and constructors

`Former` and `Constructor` give constants. Instances and applications use
`LevelApply` and `Apply`. Constructors at dimensions use `PathApply` and
`PathAt`. No other new instruction is needed.

**Rejections:** a constructor index out of range; a reference to an open or
rolled-back signature; applications at mismatched level instances (2.3).

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
- **Terms.** Instances, constructors and applications derive through
  `Former`, `Constructor`, `LevelApply`, `Apply`, `PathApply` and `PathAt`.
  An eliminator derives through `Eliminator`, one `EliminatorClause` per
  clause, `EliminatorClose` and `Apply`. The driver makes each clause's type
  agree with `ClauseType_k` by its usual conversion search.
- **Conversion search.** Former and constructor spines are rigid heads:
  equal heads compare arguments by congruence, and different constructors
  are different. An eliminator applied to a constructor takes an `Iota`
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
| `Sum(A, B)`, `inl`, `inr` | `Plus {x, y} A B`; `inl(a : A)`, `inr(b : B)` | `x`, `y` from the native premises' universes |
| `SumRec(M, l, r, v)` | `elim_{M, [l, r]}(v)` | |
| `W(x : L). B`, `sup(l, c)` | `Tree {x, y} L (λ x. B)`; `sup(l : L, c : Π (b : B(l)). s)` | the arity is `(λ x. B)(l)`, one `Beta` from `B[l/x]` |
| `WRec(M, step, v)` | `elim_{M, [step]}(v)` | same clause shape up to that `Beta` |
| `Pushout(C, A, B, m)` and its points and paths | `Push {x, y, z} C A B m`; `inl`, `inr`, `push(c) : Path(s, inl(fst(m)(c)), inr(snd(m)(c)))` | one maps parameter, as native; `push^r(c)` is `push(c) @ r` |
| `PushElim(M, l, r, b)` | `λ (z). elim_{M, [l, r, b]}(z)` | native is unapplied; `App(PushElim, z)` maps to the saturated eliminator |
| `HComp`, `Trans` at a pushout | the same nodes at `Push` | |

`Unit`, `Void` and their eliminators are not in K2.4's oracle. They may be
declared for comparison; retiring them is a separate decision (Q11).

### 7.2 The translation τ

- τ is defined on derivations, not raw syntax: the level arguments of a
  declared instance come from the universes of the native instruction's
  premises. A native `Sum(A, B)` derived from `A : U(0)`, `B : U(1)` maps to
  `Plus {0, 1} A B`.
- τ is the identity on every other node, and commutes with binders,
  substitution and interval substitution.
- **Native and declared forms are not convertible.** `Nat` and `N` are
  different types. No conversion rule, no `Lift` and no coercion relates
  them, and a term mixing them is a type error. Migration is a syntactic
  rewrite by τ, checked by the strict migration verifier.

### 7.3 Differential fixtures

| ID | Comparison | Pass condition |
| --- | --- | --- |
| X1 | Every `Nat`, sum, W and pushout case of `kernel/tests/test_instructions.c`, replayed through τ with the declared signatures | Same verdict; accepted types related by τ, up to the W arity's `Beta` |
| X2 | Weak head and normal forms of the terms those cases derive, and of each archive definition's value | `τ(nf(t))` is alpha-equal to `nf(τ(t))`, up to that `Beta` |
| X3 | Composition, homogeneous composition and transport at each type, including pushout bridges | Reducts related by τ |
| X4 | The archive, elaborated with declared forms for the four types (a driver option) | 0 gaps; every stored definition derives again; each declaration's assumptions unchanged; canonicity fixture and `evaluate` results equal |
| X5 | Cost of X4 against the native run: archive check time, re-derivation time, kernel steps, arena peak | Recorded with revision, machine and limits |

### 7.4 Retirement criterion

The hand-coded instructions retire in one change when:

1. X1–X4 pass;
2. X5's gap is recorded, and either accepted by the maintainer or closed by
   specialised reduction paths for hot signatures (Q14);
3. the archive is migrated by τ under the strict verifier, with every
   public type equal after τ and every assumption list unchanged.

The change removes `Nat`, `Zero`, `Succ`, `NatElim`, `Sum`, `Inject`,
`SumElim`, `W`, `Sup`, `WElim`, `Pushout`, `PushPoint`, `PushPath` and
`PushElim`, and their node kinds. The tags stay reserved, and the ABI version
changes. `Unit` and `Void` stay (Q11).

## 8. K2.5: truncation and resizing (G2)

### 8.1 Native truncation and quotients

```text
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
inductive Quotient(U, V < UU0, A : U, R : A -> A -> V) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}
```

- `Trunc : Π (x < ω). Π (A : U(x)). U(x)`, universe-preserving by 2.1.
- `Quotient {x, y} A R : U(max(x, y))`: its level accounts for the carrier
  and the relation. A small quotient stays small, without the archive's
  predicate encoding.
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
   rejected: `Trunc {1} A : U(0)` is not derivable (acceptance G1).
2. **A resizing assumption only by name.** If a rebuilt result genuinely
   needs resizing, it uses an assumption named `PropResizing`, reported as a
   non-computing dependency like `LEM`. The ledger below finds no such need
   in the archive.
3. **Legacy assumptions stay for the archive.** `Truncate`, `TruncateIntro`,
   `TruncateProp`, `TruncateElim`, `LEM` and `Choice` keep their generic
   signatures (G0 Q5) while any archived module uses them. The archive keeps
   checking unchanged.
4. **`LEM` and `Choice` are restated over `Trunc`** when the rebuilt library
   adopts it. They remain non-computing assumptions.
5. **The ordinary migration check stays strict.** Intentional changes of
   public universes or assumption lists are allowed only through the ledger
   of 8.5.

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
| `predicate_union_upper`, `predicate_union_least` | `predicate_chains` | `PredicateUnion(I : U1, A, P, x) := FieldExists(exists i : I. P(i, x))` is a predicate `A → U0` only by resizing | 0 | 0; 0 |
| `directed_union_independent` | `independent_unions` | Uses `PredicateUnion` as a small predicate | 5 | 0; 0 |
| `tower_induction_large` | `bourbaki_tower` | `TowerMember` is `FieldExists(forall P : A → U0. …)`, impredicative, and `FieldExists(P(y))` must be a small predicate | 8 | 7; 0 |
| `no_maximal_strict_successor` | `zorn_chain_complete` | `FieldExists(StrictlyAbove(A, le, x))` for `A : U1` used at `U0` | 2 | 3; 2 |
| `CauchyQuotient`, `cauchy_same_equivalence` | `cauchy_quotient` | `CauchySame` must be a relation into `U0` for the predicate-encoded `SetQuotient` | 3 | 0; 0 |

The dependents column counts declarations whose first failed dependency leads
to that root; the `LEM` and `Choice` column counts the root's whole group. Of
the 47, 32 depend on truncation only, 15 also on `LEM`, and 2 also on
`Choice`.

The rebuilt `library/` needs no resizing: its 38 declarations, 9 of them
truncation-dependent, all check with the universe-preserving signature.

### 8.4 The ledger's remedies

None needs a resizing assumption.

| Root | Public change | Remedy |
| --- | --- | --- |
| `small_mere_eliminate` | None: its statement is unchanged | Eliminate `Trunc(A)` directly into `P : U1`: the native eliminator's motive may land in any universe. Its 21 dependents are unaffected. |
| `PredicateUnion` group | `PredicateUnion(I, A, P) : A → U1` | State inclusion, independence and chains for predicates at a universe variable, `A → U` with `U < UU0`, which G0 makes a single definition |
| `TowerMember` group | `TowerMember : A → U1` | State tower membership and its induction at `U1`, or define the tower as an inductive predicate once H2 admits indexed families |
| `no_maximal_strict_successor` | Its hypothesis and result at `U1` | State at `U1`; `LEM` is generic over small universes (G0 D1) |
| `CauchyQuotient` group | `CauchySame` into `U1`; the quotient stays at `U1` | Use the native `Quotient`, whose level `max(0, 1) = 1` equals the predicate encoding's |

### 8.5 Ledger format and verifier (K2.5 implementation)

- A reviewed ledger file lists each intentional change: module, declaration,
  old public type, new public type, assumptions removed, assumptions
  retained, and the remedy.
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
| A2 | `Torus` and `S2` | Accept | Two dimensions; corners agree by typing |
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
| A14 | `SignatureClose` twice; `Constructor` on an open signature | Reject | Signature state |
| A15 | infinitary: `Cantor { leaf; node(f : Nat → s); squash … : set }` | Accept | D5 |

### 10.2 Universes and substitution

| ID | Case | Verdict | Reason |
| --- | --- | --- | --- |
| V1 | `x < ω, A : U(x) ⊢ Trunc {x} A : U(x)`; the same at `U(x + 1)` by `Lift` | Accept; Accept | Universe-preserving |
| V2 | `Box {x} A : U(0)` for every `x` (2.2) | Accept | Phantom parameter |
| V3 | `Pair {x, y} A B : U(max(x, y))`; `: U(x)` | Accept; Reject | Stored data |
| V4 | `Tree {x, y} L B : U(max(x, y))` | Accept | Arity counts |
| V5 | `Quotient {x, y} A R : U(max(x, y))`; `: U(x)` | Accept; Reject | The relation counts |
| V6 | `Small(x < ω, A : U(x)) : U(0) { wrap(a : A); }` | Reject | Lowering |
| V7 | `point {0} A a : Trunc {1} A` for `A : U(0)` | Reject | Mismatched instances (Q8) |
| V8 | `Trunc {ω}` | Reject | `LevelApply` needs a finite level |
| V9 | the former `Trunc : Π (x < ω). Π (A : U(x)). U(x) : U(ω)` | Accept | The former's universe is not the sort's |
| V10 | `Big(A : UU0) { wrap(a : A); } : UU0`; its eliminator into `UU1` | Accept | Fixed tier-1 signature; any motive universe |
| V11 | instantiating `Trunc` at `x + 1` inside a generic definition and reducing `elim` on `point` | Accept | Level substitution commutes (2.4) |

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
| K5 | transport of `point(a)` in `Trunc {0} (A(i))` along a line of types | `point(transp a)` |
| K6 | transport of `merid(a) @ r` in `Susp {0} (A(i))` along `ua` of a closed equivalence | The `hcomp` of 3.5; its faces reduce to the transported poles |
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
| E9 | a motive over `Trunc {1} A` used on `Trunc {0} A` | Reject |
| E10 | a motive into `UU0` for `S1` | Accept |

### 10.6 Trust controls

| ID | Case | Verdict |
| --- | --- | --- |
| T1 | `SignatureBegin` with the extension off | Reject |
| T2 | a definition using `S1` carries `kernel extension: H1`; one using that definition carries it too | Accept, marker listed |
| T3 | `computable def` using `S1` | Accept |
| T4 | `computable def` using `S1` and `LEM` | Reject, naming `LEM` only |
| T5 | rollback after admission: the signature, its constants and its JavaScript record are gone; a later admission reuses nothing | Accept |

### 10.7 Truncation policy

| ID | Case | Verdict |
| --- | --- | --- |
| G1 | `Trunc {1} A : U(0)` | Reject: no downward resizing |
| G2 | `small_mere_eliminate`'s statement proved with `Trunc`'s eliminator into `U(1)` | Accept, with no assumption |
| G3 | the archive with its legacy assumptions after H1 lands | Unchanged: 3,804 declarations, 0 gaps |
| G4 | the migration verifier on a ledger-listed change, and on the same change unlisted | Accept; Reject |

### 10.8 Release fixtures

The work plan's H1 release fixtures, each in the canonicity fixture or its
support module where it computes:

- the declared `N`, `List`, `Tree` and `Push` compared with the native forms
  (X1–X4);
- a declared circle with winding number 1, by `rfl` and by `evaluate` (E1);
- `code_meridian` by `rfl` (E2);
- `Trunc` and `Quotient` with checked dependent elimination (E3, E4);
- the rejections of A4–A12 and E6–E8. Nonstructural recursion and missing
  h-level proofs are L2.2's rejections, not the kernel's.

### 10.9 Resources and malformed input

| ID | Input | Verdict |
| --- | --- | --- |
| R1 | malformed `CC_SORT_REF`, `CC_CON_REF`, `CC_ELIM` or `CC_CLAUSE` nodes; indices out of range | Reject; inspection stays inert |
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
| Q8. Level irrelevance across instances | Still no |
| Q9. Cube and infinitary positions in higher sorts | Admit both |
| Q10. Are signatures generative | Yes |
| Q11. `Unit` and `Void` | Keep native |
| Q12. Resizing | No assumption; restate the eight roots |
| Q13. Where the experimental gate lives | In the kernel |
| Q14. Specialised reduction after retirement | Decide from X5 |

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

**Q8. Level irrelevance across instances.** G0 decided that `Trunc {0} A` and
`Trunc {1} A` are distinct (G0 Q1) and asked to revisit at H1. The ledger
found no archive result that needs them identified once each result is
stated at its own universe. *Recommended:* still no. The rule would need its
own soundness argument.

**Q9. Cube and infinitary positions.** The `set` squash needs path
positions, and W-like constructors in higher sorts need infinitary ones.
*Recommended:* admit both (D4, D5).

**Q10. Are signatures generative.** Two textually identical declarations
could be one type or two. *Recommended:* generative: each admission is a new
sort, as each definition is a new constant. Identification is a theorem.

**Q11. `Unit` and `Void`.** They are not in K2.4's oracle list.
*Recommended:* keep them native. Declaring them for comparison is allowed,
and retiring them is a later, separate decision.

**Q12. Resizing.** The measured roots of 8.3 all have remedies without
resizing (8.4). *Recommended:* no resizing assumption in the rebuilt
foundation; restate the eight roots as 8.4 proposes when their areas are
rebuilt. `PropResizing` stays unused unless a rebuilt result proves to need
it.

**Q13. Where the experimental gate lives.** In the elaborator only, or in the
kernel too. *Recommended:* in the kernel, so no client can admit a signature
by accident before review.

**Q14. Specialised reduction after retirement.** Generic reduction may be
slower than the hand-coded rules (design open question 4). *Recommended:*
decide from X5's measurements; specialised paths, if any, must be observably
identical to the generic rules and tested against them.
