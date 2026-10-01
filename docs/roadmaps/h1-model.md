# H1 model: the construction for the whole schema

Status: review draft, 2026-09-30, revised after its first review the same
day and after its second on 2026-10-01 (below). This writes out the semantic construction
of the [H1 specification](h1-signature-specification.md)'s section 4.2 for
every admitted signature: release checklist item 1, the obligations D1, D4
and D5 of its 4.3. The maintainer must review it; adding this draft does not
record that decision. It is relative to the baseline model, which remains an
assumption (4.1). Each lemma is proved in outline, at the level of detail of
G0's 3.2.

Its first review, on 2026-09-30, found that transport can raise the weight
of section 3: filling a path position evaluates its endpoint expressions at
moved data, and those trees can outweigh every original position. The
review's constructor order shows it:

```text
base : s
loop : Path(s, base, base)
step : s → s
pack : Π (f : A → s). Path(s, step(f(a)), step(f(a))) → s
```

Take for `A` a pushout with a connecting path, `f` sending its endpoints to
`base` and the path to `loop`, and `p := refl(step(base))`. Under the old
weight the positions weighed at most `ω³ + ω`. Once `a` moves into the
connecting path, the transported position's endpoint `step(f₁(a₁))` weighs
`ω³ + ω²`, and so does the position. The weight is now the next multiple of
`ω^k` (section 3, Lemma M0): `step` of anything lighter than `ω³` weighs
`ω³`, and `pack` weighs `ω⁴` before and after. Lemma M4a fills the
telescope with its dependent endpoints, and M4 is proved from it. The
[canonicity draft](h1-canonicity.md)'s transport lemma inherits both.

The second review, on 2026-10-01, accepted the block weight and the
telescope filling, and asked for three repairs:

- **The eliminator was typed after it was defined.** A clause is a function
  on its dependent telescope, so the recursive results on a constructor's
  positions must already be natural, with the displayed endpoints, before
  the clause applies to them. Defining `elim` by rank first fails, because
  restriction can raise rank. `elim`, its typing and its naturality are now
  one construction by `μ` (section 6, Lemmas M6a and M6). `μ`'s second
  component is now the spine rank, which restriction does not raise
  (section 3).
- **P1's scope.** Positional arguments `λ (y : A). E′` bring function β at
  types over `s`. P1 now includes function β and η at the arities, is
  stated as the existence of a conversion derivation within its fragment,
  and is an explicit assumption of Theorem M (section 4).
- **Transport's induction** now carries uniformity and the constancy face
  with totality and the weight bound: M5 is merged into M4, and M4a assumes
  all four of transports on lighter trees.

Since #101 the kernel has no primitive Nat or W, and since #110 no primitive
pushout. All three are H1 declarations, and this construction covers them;
the baseline below no longer lists them.

## The claim

**Theorem M.** Assume the baseline model **B**: CCHM_{ω²} in cubical sets
(G0 3.1), with Π, Σ, Path, Glue, universes `U_α` for `α < ω²`, unit, empty
type and sums, sound for the baseline rules. Assume also premise
P1 (section 4) on the kernel's conversion of constructor expressions. Then
every admitted signature has an interpretation extending B in which:

1. each instance is a fibrant family whose code lies in the universe its
   former declares;
2. constructors, boundary reduction, composition, transport and the
   eliminator satisfy the rules of sections 3.1–3.7 as strict equalities;
3. the interpretation is stable under substitution of the context.

So H1 is consistent relative to ZFC with ω² inaccessible cardinals, as G0
is, given P1. Levels are handled as in 4.2 step 1: the construction below runs at
fixed recorded levels and fixed parameter values (D8), and erased levels
only name a universe that contains the result (D9).

## 1. Setting

- **Cubes.** Fix a countable set of names and an enumeration of it. `□` has
  the finite sets of names as objects; a map `f : J → I` sends each name of
  `I` to a De Morgan formula over `J`. `□` has countably many objects and
  morphisms, since the free De Morgan algebra on a finite set is finite.
  `F(I)` is the face lattice.
- **Fresh names.** `I⁺` adds to `I` the first name not in `I`, and `I⁺ᵉ`
  adds `e` of them. A map `f : J → I` extends to `f⁺ : J⁺ → I⁺`, sending
  fresh name to fresh name. An element of `Path(A, a, b)` at `I` is an
  element of `A` at `I⁺` with faces `a` and `b`; a cube of depth `e` lives at
  `I⁺ᵉ`.
- **Types.** A type over a cubical set `Γ` is a presheaf on its category of
  elements `∫Γ` with a uniform CCHM composition structure. Its code lies in
  `U_α` when its fibres and structure are `V_α`-small (G0 3.1).
- **Signature data.** For each constructor `c_k`, `1 ≤ k ≤ n`, the squash
  included, B interprets its data telescope `D_k`, each position's arity
  `A_{k,j}`, and the data terms in its boundary. They mention no `s`,
  constructor or position (1.3), so they are available before the carrier.
  `d_k` is the number of dimensions, `e_{k,j}` the depth of position `j`'s
  cube, and `E_{k,l,ε}` the boundary expression on the face `i_l = ε`, a
  constructor expression (1.4) over the data, the positions and
  `c_1 … c_{k-1}`.

## 2. Raw trees (D4, D5)

For `(I, ρ) ∈ ∫Γ`, the raw trees `R(I, ρ)` are generated by two node kinds:

- `con(k, t, Q, rs)`, with `t ∈ D_k(I, ρ)`, formulas `rs ∈ dM(I)^{d_k}`, and
  for each position `j` a family `Q_j` that assigns to every `f : J → I` and
  every `y ∈ A_{k,j}(J, ρf, tf)` a raw tree `Q_j(f, y) ∈ R(J⁺ᵉ, ρf)`, where
  `e = e_{k,j}`;
- for a higher sort, `hcomp(φ, U, u₀)`, with `φ ∈ F(I)`, a family `U` that
  assigns to every `f : J → I` with `φf = 1` a raw tree `U(f) ∈ R(J⁺, ρf)`,
  and `u₀ ∈ R(I, ρ)`.

This is an ordinary W-type in sets. Its labels are sets, and each node
branches over the set of pairs `(f, y)` or maps `f`, which is a set because
`□` is countable and each arity is a set. So the trees exist in ZFC, as the
least fixed point of a set-sized polynomial functor, and each has an
ordinal rank.

- **D5, infinitary positions.** Branching is arbitrary. W-types in sets have
  any set-sized branching, so no further argument is needed.
- **D4, cube positions of every depth.** A position of depth `e` is a subtree
  at the larger stage `J⁺ᵉ`. The tree order ignores stages, so the trees are
  well founded at every depth, including the squash's `n + 1`.
- **No induction-recursion.** Naturality of the families and the boundary
  conditions refer to restriction, which is defined on raw trees afterwards
  (section 3). Section 4 imposes them as a predicate.

## 3. Weight, evaluation and restriction

The recursions below do not always descend to subtrees. Evaluating a
boundary builds new nodes, and transport (section 5) acts on boundary pieces
and on the endpoint expressions of path positions, whose leaves are
transports of positions. They are well founded because every boundary and
every endpoint mentions only earlier constructors. The weight makes that
precise, with a constructor's index as an exponent. For an ordinal `β` and
`k ≥ 1`, `β ↑ k` is the least multiple of `ω^k` above `β`: if
`β = ω^k · δ + σ` with `σ < ω^k`, then `β ↑ k := ω^k · (δ + 1)`.

```text
‖con(k, t, Q, rs)‖   :=  (sup over j, f, y of ‖Q_j(f, y)‖) ↑ k
‖hcomp(φ, U, u₀)‖   :=  max(sup over f of ‖U(f)‖, ‖u₀‖)
μ(x)                :=  (‖x‖, srank x), ordered lexicographically
```

An empty supremum is `0`, so a constructor without positions weighs `ω^k`.
The *spine rank* `srank x` is the rank of `x` with every subtree lighter than
`x` counted as a leaf of rank `0`. A constructor's positions are lighter
than it, so a constructor has spine rank `1`; an `hcomp` has one more than
the largest spine rank among its parts of its own weight. Plain rank would
not do: restriction can raise it. In section 6's example, `edge @ i` has
rank `0` and its endpoint `step(step(base))` rank `2`.
A constructor weighs more than each of its positions. It also weighs more
than anything that earlier constructors build over trees in its *block*,
the ordinals from `ω^k · δ` to below `ω^k · (δ + 1)`:

**Lemma M0 (blocks).** Let `m < k` and `γ ≤ ω^k · δ + σ` with `σ < ω^k`.
Then `γ ↑ m ≤ ω^k · δ + (σ + ω^m)`, and `σ + ω^m < ω^k`.

*Proof.* If `γ < ω^k · δ`, then `ω^k · δ` is itself a multiple of `ω^m`
above `γ`. Otherwise `γ = ω^k · δ + τ` with `τ ≤ σ`. As `ω^k · δ` is a
multiple of `ω^m`, `γ ↑ m = ω^k · δ + (τ ↑ m)`, and `τ ↑ m ≤ τ + ω^m`.
Finally `ω^k` is closed under addition, and `σ` and `ω^m` are below it. ∎

For a constructor expression `E`, `wt(E)` is the largest ordinal sum
`ω^{m_p} + … + ω^{m_1}` along a root-to-leaf path of its syntax, from the
deepest constructor node `c_{m_p}` out to the outermost `c_{m_1}`. An
expression that mentions only `c_m` with `m < k` has `wt(E) < ω^k`, and by
M0 each node it adds keeps its value in the block of its leaves: over trees
of weight at most `ω^k · δ + σ`, it weighs at most `ω^k · δ + σ + wt(E)`
(Lemma M1).

**Evaluation.** An environment for `c_k` at `(J, ρ')` gives data, position
families and formulas for the dimensions in scope. `ev(E, env)` follows
`E`'s syntax:

- `q_j(us)` is `Q_j(id, ⟦us⟧)`, where B interprets the data terms `us`;
- a positional argument applied to data terms, `(λ (y : A). E′)(us)`, which
  instantiating an earlier constructor's type produces, is `ev(E′, env, ⟦us⟧)`;
- `c_m(us, Es')` is `con(m, ⟦us⟧, Q', fresh names)`, a `d_m`-cube, where
  `Q'_{j'}(g, y) := ev(Es'_{j'}, env·g, y)`;
- `E @ r` restricts `ev(E, env)` along the map that sends its first cube
  name to `r`;
- `⟨i⟩ E` evaluates `E` with `i` read as a new cube name.

**Restriction.** For `f : J → I`, `f*x` is:

- for `con(k, t, Q, rs)`: if no `r_l f` is an endpoint,
  `con(k, tf, Q·f, rs f)`, where `(Q·f)_j(g, y) := Q_j(fg, y)`. This case
  does not recurse: the families already hold every later stage. Otherwise,
  with `(l, ε)` the first face in a fixed order where `r_l f = ε`,
  `f*x := ev(E_{k,l,ε}, (tf, Q·f, rs f without r_l))`;
- for `hcomp(φ, U, u₀)`: if `φf = 1`, `U(f)` restricted along `ι ↦ 1`;
  otherwise `hcomp(φf, U·f, f*u₀)`.

**Lemma M1 (restriction and evaluation are well defined).** Both are total,
by recursion on `μ` of the tree restricted. Moreover `μ(f*x) ≤ μ(x)`, and if
`E` mentions only `c_m` with `m < k` and the environment's position trees
weigh at most `ω^k · δ + σ` with `σ < ω^k`, then
`‖ev(E, env)‖ ≤ ω^k · δ + σ + wt(E) < ω^k · (δ + 1)`.

*Proof.* At an endpoint, restriction of `x = con(k, …)` evaluates
`E_{k,l,ε}` over position trees of weight at most `β := sup ‖Q‖`; write
`β = ω^k · δ + σ`, so `‖x‖ = ω^k · (δ + 1)`. Evaluation restricts those
trees, which have smaller `μ`. It also builds nodes and restricts them. By
M0, node by node, each weighs at most `ω^k · δ + σ + wt(E_{k,l,ε})`, below
`‖x‖`. A built node that reaches its own boundary is replaced by the
evaluation of that boundary, over still earlier constructors, which M0
bounds in the same way. Restriction of an `hcomp` recurses into `U(f)` or
`u₀`, of smaller `μ`. At a non-endpoint, the positions of `f*x` are among
those of `x`, so it has the same spine rank `1`. An `hcomp` restricted keeps
its parts or restricts them, and a part's spine rank does not grow by
induction; where it gets lighter, it stops counting. The bounds are proved
in the same induction. ∎

This weight is the semantic form of the precedence the critical-pair analysis
relies on: every boundary mentions only earlier constructors.

## 4. The carrier

**Good trees** are defined by recursion on rank:

- `con(k, t, Q, rs)` is good if no `r_l` is an endpoint, every `Q_j(f, y)` is
  good, each family is natural (`Q_j(f, y)` restricted along `g⁺ᵉ` is
  `Q_j(fg, y·g)`), and each position has its declared faces: `Q_j(f, y)`
  restricted to a face of its cube is `ev` of that endpoint expression, over
  `tf`, the earlier positions and `y`;
- `hcomp(φ, U, u₀)` is good if `φ ≠ 1`, `U(f)` and `u₀` are good, `U` is
  natural, and `U(f)` at `ι = 0` is `f*u₀`.

**Premise P1 (conversion in the fragment).** The admission context of `c_k`
holds the parameters, `s : U(ℓ)`, `c_1 : T_1, …, c_{k-1} : T_{k-1}`, the data
and the positions. Its *fragment* is the terms of cube types over `s` built
from constructor expressions (1.4), positional arguments `λ (y : A). E′`, and
their applications to data terms, which instantiating an earlier
constructor's type produces. P1: if the kernel finds two terms of the
fragment convertible, some conversion derivation relates them using only:

- the path step at an endpoint, reading the annotation of a variable of path
  type;
- path β and η;
- function β and η at the arities of positional arguments, substituting
  data terms for arity variables;
- congruence and dimension substitution;
- the baseline's conversion of data terms, which mention no `s`.

The reason to expect it: in the fragment, every subterm of a type over `s`
has as head a variable (a position or an earlier constructor), a function
or path abstraction, or an application of one. Nothing else of type `s`
exists there (1.3), and endpoints contain no composition (Q3). So the only
redexes the kernel can contract in such a term are function β, path β and
the path step at a variable's annotation, and its conversion check compares
weak-head forms up to η and congruence, with data terms compared by the
baseline. A successful check then yields such a derivation. This is a
claim about the kernel's conversion algorithm on the fragment, not a
consequence of B's soundness, so Theorem M assumes it, and review must
accept it. The review of 2026-10-01 found no counterexample, and asked that
its scope be stated so. The critical-pair analysis's CP02 uses the same
fragment.

**Lemma M2 (corners).** For a good environment of `c_k` and faces
`(l, ε)`, `(l′, ε′)` with `l ≠ l′`, `ev(E_{k,l,ε})` restricted to
`i_{l′} = ε′` equals `ev(E_{k,l′,ε′})` restricted to `i_l = ε`.

*Proof.* Admission derives this agreement as the typing of `T_k`'s iterated
path type (1.4). By P1 some derivation uses only the five kinds of step, and
evaluation respects each one:

- endpoint steps: for earlier constructors, by the definition of
  restriction; for positions, by goodness;
- path β and η: by the definition of `ev`;
- function β and η: a positional argument evaluates to a family of its
  arity arguments, so `ev((λ y. E′)(us))` and `ev(E′[us/y])` are both its
  value at `⟦us⟧`, and `λ y. q(y)` evaluates to `q`'s family;
- congruence and substitution: by Lemma M3 at smaller weight (M1);
- data conversion: by B's soundness.

The proof is by induction on the conversion derivation. ∎

**Lemma M3 (a presheaf).** For good `x`:

- `f*x` is good, `id*x = x` and `(fg)*x = g*(f*x)`;
- restriction does not depend on the order in which endpoint faces are
  chosen;
- evaluation is natural: `ev(E, env)` restricted along `g` is `ev(E, env·g)`.

*Proof.* Induction on `μ`, with the cases of M1. The only nontrivial case is
a constructor whose formulas reach an endpoint under `fg` but not under `f`.
Then `g*(f*x)` evaluates the boundary piece at `g`, which is `(fg)*x` by
naturality of evaluation. Several endpoints at once agree by M2. ∎

**The carrier.** `X(I, ρ)` is the set of good trees in `R(I, ρ)`, with the
restriction maps `f*`. By M3 it is a presheaf on `∫Γ`. Its elements are
saturated constructors at non-endpoint formulas and, for a higher sort,
formal compositions with `φ ≠ 1`. It is the least family closed under
4.2 step 2's clauses, and it contains only reduced forms.

- **Constructors.** A good family is an element of the position's type in
  the presheaf model: a Π over the arity into a cube. So `Con(k; I)` applied
  to an element of the argument telescope is a `con` node. It interprets
  `T_k`, and at an endpoint its restriction is the boundary piece (3.2).
- **Stability.** A raw tree at `(I, ρ)` depends on `ρ` only through the
  parameter values there and the stage. For `σ : Δ → Γ`, `X_Δ` is literally
  `X_Γ ∘ ∫σ`, which is Coquand–Huber–Mörtberg's locality.
- **Size.** Data and arity sets are `V_{κ_ℓ}`-small, since their types lie in
  `U(ℓ)` (2.1). `□` is countable and `κ_ℓ` is inaccessible, so the raw trees
  and `X`'s fibres are `V_{κ_ℓ}`-small.

## 5. Kan structure

**Data sorts (3.3).** Every element is a `con` node without formulas, and
restriction keeps its constructor index. So in `comp^i X [φ ↦ u] u₀`, every
tube restricted to `i = 0` equals the base's restriction and has the base's
index `k`. The composition is `c_k` of the telescope's composition:

- data by B's rules;
- positions by the Π rule, whose recursive call has a position of `u₀` as
  its base, of smaller rank;
- a path position also takes its endpoint lines as tubes, evaluated along
  the filled telescope.

Uniformity and the face condition hold by induction, and this validates 3.3
strictly.

**Higher sorts: formal composition (3.4).** `hcomp` is the generator. On a
face that holds it is the tube at `1`, which is the Face step. Tubes on the
empty face are dropped.

**Transport (3.5).** For a line `ρ ∈ Γ(I⁺)` constant on `φ ∈ F(I)`,
`T_{ρ,φ} : X(I, ρ(0)) → X(I, ρ(1))` follows 3.5's cases on the element:

- case 1 is a point constructor, whose argument telescope is filled along
  the line;
- case 2 is a constructor at dimensions, filled the same way and corrected
  by an `hcomp` whose walls are squeezes of the boundary pieces;
- case 3 is an `hcomp`, transported componentwise.

The model has no neutral case. Filling a position is composition in its
cube, whose faces are the position's endpoint expressions. They are
evaluated at the filled earlier positions and the moved data, so they are
tubes of the composition, and they are not subtrees of `x`.

**Lemma M4a (telescope filling).** Let `x = con(k, t, Q, rs)` at
`(I, ρ(0))`, with `sup ‖Q‖ = ω^k · δ + σ` and `σ < ω^k`. Suppose `T` is
defined, at every stage and along every line, on every tree lighter than
`x`, and that there it does not increase weight, is uniform and is the
identity where its face holds. Then the filler `θ(i)` of `c_k`'s
argument telescope along `ρ`, constant on `φ`, exists, and:

- each filled position has its declared faces at every `i`;
- every filled position tree weighs at most `ω^k · δ + σ′`, for some
  `σ′ < ω^k` that depends only on `σ` and the signature;
- so `ev(E, θ(i))` weighs less than `‖x‖ = ω^k · (δ + 1)` for every
  constructor expression `E` over `c_1 … c_{k-1}`.

*Proof.* Along the telescope, with `σ_0 := σ`.

- The data are filled by B.
- Position `j` has a type at `i` that is a `Π` over the arity into the cube
  `C_j(i)` over `X(ρ(i))`. Its faces are `ev` of the endpoint expressions
  `P` over the filled data, the arity argument and `θ_{<j}(i)`. B's `Π`
  rule fills an arity argument backward and composes in the cube: the base
  is `Q_j` at the moved argument, and the tubes are `φ ↦ Q_j` and, on each
  face of the cube, the line `i ↦ ev(P, θ_{<j}(i), y(i))`.
- Composition in `X` is 3.4's `hcomp` of transports. `Q_j` weighs at most
  `ω^k · δ + σ`. By induction along the telescope the earlier filled
  positions weigh at most `ω^k · δ + σ_{j-1}`, so by M1 the endpoint lines
  weigh at most `ω^k · δ + σ_{j-1} + wt(P)`. Both are lighter than `x`, so
  `T` is defined on them and keeps these bounds. Its uniformity makes the
  filled family natural in the stage and the arity arguments, and its
  constancy face makes it constant on `φ`. The `hcomp` weighs the
  maximum of its parts: at most `ω^k · δ + σ_j`, where `σ_j` is the larger
  of `σ` and `σ_{j-1} + wt(P)` over the cube's faces, still below `ω^k`.
- On a face of the cube, the `hcomp` is its tube at the end of the line,
  the transport of the endpoint line along its constancy face: the declared
  face at `θ_{<j}(i)`.

`σ′` is `σ_j` for the last position. The last claim is M1 at `σ′`. ∎

**Lemma M4 (transport).** `T` is defined by recursion on `μ`, and
simultaneously:

1. `‖T x‖ ≤ ‖x‖`;
2. `T` is uniform: `f*(T_{ρ,φ} x) = T_{ρf,φf}(f*x)` for every `f : J → I`;
3. `T` is the identity where `φ` holds.

The recursion defines `T` on all trees with one value of `μ` at once, from
smaller values; by M1, `f*x` never has a larger `μ` than `x`, so `T(f*x)` is
defined whenever (2) mentions it.

*Proof.* In cases 1 and 2, with `x = con(k, …)` and the notation of M4a,
the induction hypothesis gives M4a's premise, since every tree lighter than
`x` has smaller `μ`.

- Case 1 calls `T` only through M4a, on positions and endpoint lines
  lighter than `x`. Its result `c_k(θ(1))` has positions of weight at most
  `ω^k · δ + σ′`, so it weighs at most `ω^k · (δ + 1) = ‖x‖`.
- Case 2's walls call `T` on `b_{l,ε}(i) = ev(E_{k,l,ε}, θ(i))`, lighter
  than `x` by M4a. The result `hcomp[φ ↦ x, walls](c_k(θ(1)) @ rs)` weighs
  at most `max(‖x‖, ‖walls‖, ‖x‖) = ‖x‖`.
- Case 3 recurses into the tubes and the base, of smaller `μ`.

That gives (1). For (2) and (3):

- where `f` changes no face or formula, the construction commutes with
  `f`, by (2) for the transports it calls (Lemma H2 in the model);
- where some `r_l f = ε`, the wall at `h = 1` is the transport of
  `b_{l,ε}(0) = f*x`: CP06 in the model. Two walls at a corner agree by M2
  and (2) for the lighter pieces: CP07;
- where `φf = 1`, the filler and the squeezes are constant by (3) for the
  transports they use, so the result is `f*x`: CP08. This is also (3);
- the faces of a transported `hcomp` are CP09. ∎

This is D4 in its sharpest form. The walls transport boundary pieces, and
the fillers transport endpoint expressions, whose leaves are transports of
the positions, not subtrees of `x`. It is the weight, not the rank, that
decreases. A transported position can outweigh every original one, as in
the review's `pack`; it stays in `x`'s block, which `x`'s weight absorbs.
M4 includes what the earlier drafts' M5 stated after it: uniformity, the
identity on `φ`, and transport's commuting with restriction to a
constructor's faces. M4a needs all of these for the transports it calls.

**General composition** is 3.4's decomposition, `hcomp` after transport,
which gives a CCHM composition structure, as Coquand–Huber–Mörtberg show for
pushouts. So `X` is fibrant, and with its size it has a code in `U_ℓ`.

## 6. The eliminator

A motive `M` is a fibrant family over `X` at the given parameters, at any
level, UU tiers included (D7). Its clauses `m_k` are sections of the clause
types. A clause is a function on its dependent telescope. So `elim` can
apply `m_k` to a constructor only once the recursive results on its
positions form an element of the displayed position types: natural in the
stage and the arity arguments, with the displayed endpoints on every face of
each cube. That needs `elim`'s naturality and the semantic Lemma H1, at the
positions and at their faces. Restriction can raise rank, as in the review's
example:

```text
base : s
step : s → s
edge : Path(s, step(step(base)), step(step(base)))
wrap : Path(s, step(step(base)), step(step(base))) → s
```

In `wrap(edge)`, the cube `edge @ i` has rank `0`, but its endpoint
`step(step(base))` has rank `2`. So `elim`, its typing and its naturality
are constructed together, by recursion on `μ`, which restriction does not
raise. Here the weight descends:
`‖step(step(base))‖ = ω² · 2 < ω³ = ‖edge @ i‖ < ω⁴ = ‖wrap(edge)‖`.

```text
elim(con(k, t, Q, rs))     :=  m_k(t, Q, Q̄) @ rs        with Q̄_j := elim^{C_j} ∘ Q_j
elim(hcomp(φ, U, u₀))     :=  comp^j M(hfill^j) [φ ↦ elim(U(j))] (elim(u₀))
```

**Lemma M6a (displayed boundary: the semantic Lemma H1).** Let `B` be an
ordinal such that `elim` is defined on every tree lighter than `B`, lies in
`M` there, and is natural there: `elim(f*y) = f*(elim y)`. Let `env` be a
good environment for `c_k` whose position trees weigh at most
`ω^k · δ + σ`, with `σ < ω^k` and `ω^k · (δ + 1) ≤ B`. Let `E` be a
constructor expression over `c_1 … c_{k-1}`, and suppose the lifted
positions `elim^C ∘ env` lie in the displayed types of the positions `E`
mentions. Then `⟦E⟧` is defined at `(env, elim^C ∘ env)`, and

```text
elim^C(ev(E, env)) = ⟦E⟧[env, elim^C ∘ env].
```

*Proof.* `⟦E⟧` is a term of the kernel-checked clause context, so B
interprets it at these arguments. Every tree below is lighter than `B`: the
positions by assumption, and the nodes `ev` builds and their restrictions
by M1. By induction on `E`:

- `q_j(us)`, or a positional argument applied to data terms: by the
  definition of the lifted positions, and of `ev` on applied positional
  arguments;
- `c_m(us, Es′)`: `ev` builds the cube `con(m, ⟦us⟧, Q′, fresh names)`.
  `elim`'s first clause gives `m_m(⟦us⟧, Q′, elim ∘ Q′)` at the fresh names,
  and `elim ∘ Q′` is `⟦Es′⟧` by induction, at every stage by naturality.
  Path η gives `⟦c_m(us, Es′)⟧`;
- `E @ r`: `ev` restricts `ev(E, env)` along the map that sends its first
  cube name to `r`. `elim` commutes with that restriction, and `⟦E @ r⟧` is
  `⟦E⟧ @ r`;
- `⟨i⟩ E`: by induction, at the new name. ∎

**Lemma M6 (the eliminator).** By recursion on `μ`, `elim` is defined on
every good tree, and simultaneously:

1. `elim(x)` lies in `M(x)`;
2. `elim(f*x) = f*(elim x)` for every `f`.

As for transport, the recursion defines `elim` on all trees with one value
of `μ` at once, from smaller values, and `f*x` never has a larger `μ`.

*Proof.*

- **`x = con(k, t, Q, rs)`.** Let `β = ω^k · δ + σ` be the positions'
  supremum, so `B := ‖x‖ = ω^k · (δ + 1)`. Every tree lighter than `x` has
  smaller `μ`, so (1) and (2) hold below `B`.
  - `Q̄_j := elim^{C_j} ∘ Q_j` is natural in the stage and the arity
    arguments, since `Q_j` is (goodness) and `elim` commutes with
    restriction below `B`.
  - On each face of its cube, `Q_j(f, y)` is `ev(P, …)` for that endpoint
    expression `P` (goodness). Along the telescope, M6a at `B` gives
    `elim(ev(P, …)) = ⟦P⟧[…, Q̄]`: `P` mentions only earlier positions,
    whose lifts are already typed. So `Q̄` lies in the displayed position
    telescope, and `m_k(t, Q, Q̄)` is defined, an element of the clause type
    `R̄`. At `rs` it lies in `M(x)`: (1).
  - For (2), if no `r_l f` is an endpoint, `f*x = con(k, tf, Q·f, rs f)`,
    and `elim(f*x) = m_k(tf, Q·f, Q̄·f) @ rs f = f*(elim x)`, since `m_k` is
    a section.
  - If `r_l f = ε` is the first endpoint, `f*x = ev(E_{k,l,ε}, env_f)`,
    lighter than `x`. M6a at `B` gives
    `elim(f*x) = ⟦E_{k,l,ε}⟧[env_f, Q̄·f]`, which is the face of the clause
    type on `r_l = ε`, so `f*(elim x)`. This is CP01.
- **`x = hcomp(φ, U, u₀)`.** Its parts, and their restrictions, have
  smaller `μ`, so (1) and (2) hold for them.
  - The eliminated tube is natural, and at `ι = 0` it is `elim(U(f))`
    restricted, which is `elim(f*u₀) = f*(elim u₀)`: the tube and the base
    are compatible.
  - Each `elim(U(f))` lies in `M(U(f))`, and `hfill^j` is `U(j)` on `φ`, so
    the composition in `M` along `hfill^j` is defined. At `j = 1`,
    `hfill^1 = x`, so it lies in `M(x)`: (1).
  - For (2), where `φf = 1`, `f*x` is `U(f)` at `1`, and composition's face
    condition gives the eliminated tube there (CP03). Otherwise
    `f*x = hcomp(φf, U·f, f*u₀)`, and the uniformity of composition in `M`,
    with (2) for the parts, gives `f*(elim x)`. ∎

So point and dimensional Iota, the elimination of `hcomp` and the boundary
rule hold strictly.

## 7. The rules of section 3 in the model

| Rule | Model fact |
| --- | --- |
| 3.1 formation, erased and recorded levels | `X` at fixed recorded levels and parameter values; D8 and D9 as in 4.2 step 1 |
| 3.2 constructors and boundary reduction | `con` nodes; restriction at an endpoint is the boundary piece (M3) |
| 3.3 data-sort composition | Section 5, by recursion on the base |
| 3.4 formal and general composition | `hcomp` generator; the decomposition |
| 3.5 transport with boundary correction | M4a, M4 |
| 3.6 clause types | The semantic Lemma H1 (M6a); typing in M6 |
| 3.7 Iota, elimination of `hcomp` | The definition of `elim`; M6 |
| 2.4, 2.5 substitution | Stability of the construction; M3 |

## 8. Consistency

`⟦Void⟧` is the empty presheaf, so no closed term of `Void` exists. H1 is
consistent relative to ZFC with ω² inaccessible cardinals, to the soundness
of B, and to premise P1.

## 9. What this discharges, and what review must check

- **D1.** The construction is uniform in the signature. It uses:
  - the constructor order, through the weight's exponents;
  - the cube boundary's typing, through M2;
  - positivity, through the raw trees.

  No step names a particular signature. For the circle, suspensions,
  pushouts and propositional truncation it gives carriers of the same shape
  as Coquand–Huber–Mörtberg's.
- **D4.** Raw trees are well founded at every cube depth (section 2), and
  transport's recursion terminates by weight (M0, M4a, M4).
- **D5.** Raw trees allow set-sized branching, and the fibres stay
  `V_{κ_ℓ}`-small (section 4).

Review must accept:

- the premise P1, with its fragment and its scope (section 4), which
  Theorem M assumes;
- the weight, revised after the first review: Lemma M0, and its use in M1,
  the telescope filling of M4a and M4;
- the spine rank in `μ`, which restriction does not raise (M1);
- transport's simultaneous induction, M4 with M4a;
- the functoriality case of M3 at endpoints;
- the eliminator's simultaneous construction, M6, and the semantic Lemma
  H1 with its explicit bound, M6a;
- that the model cases of CP01, CP03 and CP06–CP09 match the syntactic
  joins of the [critical-pair analysis](h1-critical-pairs.md), which was
  approved on 2026-09-30.

Not claimed: normalization or decidable conversion; that the kernel
implements these rules, which its tests exercise; canonicity, which the
[canonicity draft](h1-canonicity.md) treats. B remains an assumption, as in
the specification's 4.1.
