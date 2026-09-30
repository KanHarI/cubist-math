# H1 canonicity

Status: review draft, 2026-09-30. This writes out the canonicity argument of
the [H1 specification](h1-signature-specification.md)'s section 4.4:
release checklist item 3. The maintainer must review it; adding this draft
does not record that decision. It is relative to the baseline's canonicity,
which remains an assumption (4.1; G0 3.5, 3.6). It uses the
[critical-pair draft](h1-critical-pairs.md) for coherence, so it depends on
item 2's review too. Each step is proved in outline, at the level of detail
of G0's 3.5.

Since #101, `Nat` is a data sort declared in `nat.cubist`, not a primitive.
Invariant 10's promise that a closed natural number computes to a numeral
therefore rests on this argument.

## The claim

"Reduces" means the specification's weak-head reduction: the baseline's
rules together with sections 3.2–3.7.

**Theorem C.** Let `I` be a context of dimension variables only, and let
`⊢_I t : A`, where `t` uses no assumption. Then `t` is computable at `A`, in
the sense of section 1. In particular:

- **C1, data sorts.** If `A` reduces to an instance `S(as)` of a data sort,
  then `t` reduces to `c_k(as′)(ts, qs)` with computable arguments. When
  `S` is first-order, iterating on the arguments gives a closed constructor
  term: every data type is first-order and every position has depth `0` and
  an empty arity. For `Nat` this is a numeral.
- **C2, higher sorts.** The weak head of `t` is a constructor at
  non-endpoint formulas, or an `hcomp` with `φ ≠ 1` whose tube and base are
  computable. These are the canonical forms of 3.8.
- **C3, elimination into data.** Eliminating a higher sort into a data sort
  gives a value as in C1. The canonicity fixture's winding numbers are
  instances.

Not claimed: normalization, decidable conversion, or that the kernel
implements these rules. The canonicity fixture and the acceptance matrix
exercise the implementation.

## 1. Computability predicates

Huber's predicates are used as G0 3.5 extends them:

- For each dimension context `I`, there are predicates `⊩_I A` (computable
  type), `⊩_I t : A` and `⊩_I t = u : A`. They are defined by well-founded
  induction on levels below ω², and within a level by an inductive
  definition of the computable types.
- They are Kripke over substitutions `f : J → I`. A term is computable when
  every restriction of it reduces to a computable weak-head value, and the
  reducts of different restrictions agree up to computable equality. This
  *coherence* is what the cubical setting adds, because reduction does not
  commute with substitution.
- Huber's expansion lemma closes computability under coherent weak-head
  expansion, and computable equality contains common reducts.

This framework and its fundamental lemma for the baseline formers are
assumed, as the specification's 4.1 assumes them. Huber's published proof
covers Π, Σ, Path, Glue, one universe and natural numbers. The kernel's
baseline adds unit, the empty type, sums, pushouts, the hierarchy below ω²
and level quantification. No published proof covers pushouts.

## 2. The predicate for a declared instance

Let `S(as)` be an instance with computable parameters `as`. Its data types
and its arities at computable arguments are baseline types at levels at most
`ℓ`, and they do not mention `S` (1.3). So they are computable types by the
ordinary induction, before `S(as)`'s own predicate is defined.

`⊩ u : S(as)` is the least family of predicates, over all stages at once,
closed under three clauses:

- **V1.** `u ⇒* c_k(as)(ts, qs)` with `d_k = 0`, where `ts` are computable at
  `D_k` and each position is computable pointwise: for every `f` and every
  computable arity argument `y` at `J`, `q_j f (y)` is computable at the cube
  `C_j` over `S(as f)`. At a fresh cube its faces are computably equal to
  its evaluated endpoint expressions.
- **V2.** `u ⇒* (c_k(as)(ts, qs)) @ rs` with no `r_l` an endpoint at `I`, and
  arguments as in V1.
- **V3,** for a higher sort. `u ⇒* hcomp^i S(as) [φ ↦ w] w₀` with `φ ≠ 1`,
  where `w₀` is computable and `w` is computable at every `f` with `φf = 1`.

In every clause `u` is coherent: each restriction `u f` is computable, and
its reduct is computably equal to the restriction of `u`'s reduct.
Computable equality is the least relation that relates:

- values of the same clause, with the same constructor index or the same
  `hcomp` shape and equal parts;
- terms that are related after coherent expansion.

`S` occurs only as the codomain of positions, so the definition is strictly
positive and has a least fixed point. It is an inductive definition in the
metatheory, infinitary where arities are, and it has the well-founded order
of derivations: positions and the parts of an `hcomp` come first. Each
derivation has the model's weight:

- a V1 or V2 derivation of `c_k` weighs the supremum of its positions'
  weights `⊕ ω^k`;
- a V3 derivation weighs the maximum of its parts.

## 3. Coherence of the new reductions

**Lemma C1.** Let `t ⇒ t′` by a rule of sections 3.2–3.7. For every `f`, the
reducts of `t f` and `t′ f` are computably equal.

*Proof.* By Lemma H2, either the same rule applies to `t f` and gives
`t′ f`, or substitution has made a formula an endpoint or a face true. In
the second case, the joins CP01–CP10 of the critical-pair draft give a
common reduct, and computable equality contains common reducts. ∎

This is where canonicity depends on item 2. The joins are the syntactic
counterparts of the model's naturality lemmas ([model draft](h1-model.md),
M3–M6).

## 4. The fundamental lemma: the H1 cases

The fundamental lemma is proved by induction on typing derivations. The
baseline cases are assumed, and Lemma C1 supplies the coherence of every new
reduction.

- **Formation (3.1).** `S{ℓs_r}(as)` is a computable type when `as` are
  computable (section 2).
- **Constructors and boundaries (3.2).** A constructor with computable
  arguments is computable. With `d_k = 0` this is V1; at formulas `rs` that
  are not endpoints, V2. Under a restriction `f` where some `r_l f = ε`, the
  term reduces by the boundary rule to `E_{k,l,ε}` at the arguments. That is
  computable by induction on `k`, since it mentions only earlier
  constructors, and by the positions' computability. Several faces agree by
  the cube boundary's typing (premise P1 of the model draft), and coherence
  is CP02.
- **The eliminator (3.6, 3.7).** Let `u` be computable at `S(as)`. Then
  `elim_{M,ms}(u)` is computable at `M(u)`, by induction on the derivation of
  `u`'s computability:
  - **V1.** `elim(u) ⇒ m_k(ts, qs, q̄s)`. The clause is computable by the
    fundamental lemma, and `ts`, `qs` are computable. The lifted
    `q̄_j = λ ys. elim^{C_j}(q_j(ys))` are computable by the induction
    hypothesis at the positions, which come earlier in the derivation.
  - **V2.** `elim(u) ⇒ m_k(…) @ rs`, computable at the clause type's nested
    `PathP`. At an endpoint face, Iota then the path step gives `⟦E⟧[q̄]`,
    and the boundary then Iota gives `elim(E)`. Lemma H1 joins them by Iota
    steps (CP01).
  - **V3.** `elim(u) ⇒ comp^j M(hfill^j) [φ ↦ elim(w(j))] (elim(w₀))`,
    computable by the baseline's composition in the computable family `M`
    and the induction hypothesis for `w` and `w₀`. Coherence on `φ` is CP03.
- **Data-sort composition (3.3).** Consider `comp^i S(as(i)) [φ ↦ u] u₀` with
  computable parts:
  - `u₀` reduces to `c_k(θ₀)` by V1.
  - In a dimension context each conjunct of `φ` is a substitution. Under it
    the tube is computable, so it reduces to some `c_{k′}(θ_u)`.
  - Computable equality with `u₀` at `i = 0` forces `k′ = k`, so the rule of
    3.3 fires.
  - Its result, `c_k` of the telescope's composition, is computable by
    induction on `u₀`'s derivation, through its positions.

  This is Huber's argument for natural numbers, with the telescope in place
  of the predecessor; coherence is CP04.
- **Formal composition (3.4).** An `hcomp` with computable parts and
  `φ ≠ 1` is V3. On a face that holds it reduces to its tube (CP10).
- **Transport (3.5).**

  **Lemma C2.** Let `u` be computable at `S(as(0))`, and let `as(i)` be a
  computable line, constant on `φ`. Then `transp^i S(as(i)) φ u` is
  computable at `S(as(1))`, of weight at most `u`'s.

  *Proof.* By induction on the pair of weight and derivation height, the
  measure of the model draft's Lemma M4.
  - **V1.** The telescope transport is the baseline's for data, and uses the
    induction hypothesis for positions. It gives `c_k(θ(1))`, which is V1.
  - **V2.** The reduct is `hcomp[φ ↦ u, walls](v)`, and `v` is V2 at `θ(1)`.
    Each wall transports `b_{l,ε}(i) = E_{k,l,ε}[θ(i)]`. That expression is
    computable, built from earlier constructors over fillers of the
    positions, and its weight is below `u`'s, so the induction hypothesis
    applies. The walls agree where they meet (CP07) and on `φ` (CP08), and
    each restricts to the transport of its boundary piece (CP06).
  - **V3.** Componentwise (CP09). ∎

  The walls transport boundary pieces whose leaves are transports of
  positions, not parts of `u`'s derivation. As in the model, the weight,
  not the height, decreases.
- **General composition of a higher sort (3.4).** It is an `hcomp` of
  transported parts: V3, by formal composition and C2. Coherence is CP05.
- **Levels.** A motive may land at any level `l′`, including UU tiers (D7).
  `M(z)`'s computability is defined at its level by the level induction of
  G0 3.5. No rule reads a level (2.4), so the predicates at fixed recorded
  levels suffice (D8). An erased level only names a universe, related by
  cumulativity as in G0 (D9).

## 5. Canonical values

C1 and C2 read off the clauses V1–V3: a computable term reduces to one of
those weak heads. For first-order data, the derivation is well founded, so
iterating on the arguments gives a finite closed constructor term. For
`Nat`, that is a numeral.

For C3, `elim` of an `hcomp` reduces to composition in the data motive, by
V3's case above. That composition reduces by the data-sort case to a
constructor with computable arguments.

## 6. Assumptions, and what review must check

- **Assumed.** The baseline's computability predicates and fundamental
  lemma (specification 4.1, G0 3.5, 3.6).
- **Premise P1** of the model draft, for the agreement of boundary pieces at
  corners.
- **Item 2.** Lemma C1 uses the joins CP01–CP10, so this argument is
  conditional on the critical-pair review.
- **Metatheory.** An inductive definition of predicates with set-sized
  branching, within ZFC and G0's universes.

Review must accept:

- the clauses V1–V3 and their coherence condition;
- the use of Lemma C1;
- the measure in Lemma C2;
- the constructor-index argument in the data-sort composition case;
- the level cases.
