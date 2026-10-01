# H1 canonicity

Status: review draft, 2026-09-30, revised the same day after its first
review (below). This writes out the canonicity argument of the
[H1 specification](h1-signature-specification.md)'s section 4.4: release
checklist item 3. The maintainer must review it; adding this draft does not
record that decision. It is relative to the baseline's canonicity, which
remains an assumption (4.1; G0 3.5, 3.6). It uses the
[critical-pair analysis](h1-critical-pairs.md), which the maintainer
approved on 2026-09-30 (item 2), to find every coherence obligation. Each
step is proved in outline, at the level of detail of G0's 3.5.

Since #101, `Nat` is a data sort declared in `nat.cubist`, not a primitive.
Invariant 10's promise that a closed natural number computes to a numeral
therefore rests on this argument.

## Revision after review

The first review, on 2026-09-30, found three substantive issues:

1. **The least fixed point was empty.** Every clause required every
   restriction `u f` to be computable. At `f = id` a term's computability
   was a premise of itself, so the empty predicate was closed under the
   clauses, and not even `Nat.zero` had a derivation. Section 2 now
   separates the value clauses from expansion, as Huber's clauses for `N`
   separate `0` and `S u` from non-introduced terms. A value's premises are
   its parts and, for a constructor at dimensions or a formal composition,
   its restrictions to the faces where it stops being a value: other terms.
   Stability under substitution is Lemma C3. Lemma C4 shows that every
   constructor with computable arguments has a derivation.
2. **The weight did not bound transport.** Filling a path position creates
   endpoint tubes that can outweigh every original position. The
   [model draft](h1-model.md) revises its weight (Lemma M0) and adds a
   telescope-filling lemma (M4a). Section 2.4 carries the revised weight to
   derivations, Lemma C5 fills the telescope with its dependent endpoints,
   and Lemma C2 uses it.
3. **Lemma C1 took computable equality from syntactic joinability.**
   Huber's Expansion Lemma needs the reducts to be computable, and a common
   reduct does not provide that. C1 is now stated under explicit
   computability hypotheses. Section 4 establishes, inside the fundamental
   induction, that both sides of every join are computable and computably
   equal; the table in section 3 says where.

The items of Theorem C were called C1–C3, like the lemmas; they are now
(i)–(iii).

## The claim

"Reduces" means the specification's weak-head reduction: the baseline's
rules together with sections 3.2–3.7.

**Theorem C.** Let `I` be a context of dimension variables only, and let
`⊢_I t : A`, where `t` uses no assumption. Then `t` is computable at `A`, in
the sense of section 1. In particular:

- **(i) Data sorts.** If `A` reduces to an instance `S(as)` of a data sort,
  then `t` reduces to `c_k(as′)(ts, qs)` with computable arguments. When
  `S` is first-order, iterating on the arguments gives a closed constructor
  term: every data type is first-order and every position has depth `0` and
  an empty arity. For `Nat` this is a numeral.
- **(ii) Higher sorts.** The weak head of `t` is a constructor at
  non-endpoint formulas, or an `hcomp` with `φ ≠ 1` whose tube and base are
  computable. These are the canonical forms of 3.8.
- **(iii) Elimination into data.** Eliminating a higher sort into a data
  sort gives a value as in (i). The canonicity fixture's winding numbers
  are instances.

Not claimed: normalization, decidable conversion, or that the kernel
implements these rules. The canonicity fixture and the acceptance matrix
exercise the implementation.

## 1. Computability predicates

Huber's predicates are used as G0 3.5 extends them. Lemma numbers are those
of the arXiv version, arXiv:1607.04156v2. Its Lemma 3.11, the Expansion
Lemma, is the review's Lemma 9 of the journal version.

- For each dimension context `I` there are predicates `⊩_I A`,
  `⊩_I A = B`, `⊩_I u : A` and `⊩_I u = v : A`. They are defined by
  well-founded recursion on levels below ω² and, within a level, by
  induction-recursion.
- Reduction `≻` is weak-head and deterministic. `u↓` is the reduct of `u`,
  or `u` itself when it has none. Reduction is not closed under
  substitution: `u ≻ v` at `I` does not give `u f ≻ v f`.
- **Values and expansion.** An *introduced* term, such as `0` or `S u` in
  `N`, is computable when its parts are, by a clause for its head. A
  *non-introduced* term `u` is computable when, for every `f : J → I`, `u f`
  has a reduct, `⊩_J u f↓`, and for every further `g : K → J`,
  `⊩_K (u f↓) g = (u fg)↓`. No clause has a term's own computability among
  its premises.
- Huber proves, for each type former:
  - reflexivity (3.5);
  - monotonicity under substitution, with derivations no higher (3.6);
  - computability of reducts (3.7);
  - that computable equality is a partial equivalence (3.8);
  - `⊩ u = u↓` (3.10);
  - the **Expansion Lemma** (3.11): if for every `f`, `u f` has a reduct,
    `⊩_J u f↓ : A f` and `⊩_J u f↓ = (u↓) f : A f`, then `⊩ u : A` and
    `⊩ u = u↓ : A`. In particular, a reduction closed under substitution
    to a computable term gives both.

  The Expansion Lemma's premises are about the reducts: that two terms have
  a common reduct makes neither computable.

This framework and its fundamental lemma for the baseline formers are
assumed, as the specification's 4.1 assumes them. The baseline's argument
quantifies over computable types generically, through the lemmas above, so
it applies to a declared instance once that instance's predicates satisfy
them (2.3). Huber's published proof covers Π, Σ, Path, Glue, one universe
and natural numbers. The kernel's baseline adds unit, the empty type, sums,
pushouts, the hierarchy below ω² and level quantification. No published
proof covers pushouts.

## 2. The predicates for a declared instance

Let `S(as)` be an instance with computable parameters `as` at `I`. Its data
types, and its arities at computable arguments, are baseline types at
levels at most `ℓ`. They do not mention `S` (1.3), so they are computable
types by the ordinary induction. A position `q_j` has type
`Q_j = Π (ys : A_j). C_j`, where the cube `C_j` over `S(as)` has endpoint
expressions over the data, the earlier positions and `ys`. Computability at
`Q_j` is given by Huber's Π and Path clauses, from the predicates of
`S(as)` being defined.

### 2.1 The clauses

`⊩_I u : S(as)` and `⊩_I u = v : S(as)` are the least predicates, over all
stages at once, closed under the clauses below. The *introduced* terms are
those of V1–V3, and every other term is non-introduced.

- **V1.** `c_k(as)(ts, qs)` with `d_k = 0`, when `⊩ ts : D_k(as)` and
  `⊩ q_j : Q_j` for each position.
- **V2.** `u = (c_k(as)(ts, qs)) @ rs` with `d_k ≥ 1` and no `r_l` an
  endpoint, when its arguments are as in V1 and `⊩_J u f : S(as f)` for
  every `f : J → I` that makes some `r_l f` an endpoint.
- **V3,** for a higher sort. `u = hcomp^i S(as) [φ ↦ w] w₀` with `φ ≠ 1`,
  when:
  - `⊩ w₀ : S(as)`;
  - `w` is computable on `φ`: at `J, i` for every `f : J → I` with
    `φf = 1`;
  - `w(0)` is computably equal to `w₀` on `φ`;
  - `⊩_J u f : S(as f)` for every `f` with `φf = 1`.
- **N.** A non-introduced `u`, when for every `f`, `u f` has a reduct and
  `⊩_J u f↓ : S(as f)`, and for every `f` and `g`,
  `⊩_K (u f↓) g = (u fg)↓ : S(as fg)`.

Computable equality relates two computable terms `u` and `v` in these
cases:

- two V1 or V2 values with the same index `k`, the same formulas `rs` and
  computably equal arguments, and, for V2, with `⊩ u f = v f` at every `f`
  that makes an endpoint;
- two V3 values with the same `φ` and computably equal tubes and bases;
- `u` and `v`, one of them non-introduced, when `⊩_J u f↓ = v f↓` for
  every `f`.

V2's and V3's face premises follow Huber's clause Gl-C for `Glue`, which
asks for the restrictions where `φ` holds. They concern other terms: at
`f = id` no `r_l` is an endpoint, and `φ ≠ 1`. The restricted term is
non-introduced, and N derives it from its reducts, the boundary pieces or
the tube at `1`. V3's face premise follows from its others, as Huber's
Remark 4.18 observes for `Glue`; it is kept so that stability is immediate.

### 2.2 Well founded, and not empty

Every premise concerns one of:

- a part of the term: its arguments, tube or base;
- a reduct (N);
- a restriction at which the term is no longer a value (V2, V3).

None concerns the term itself. `S`'s predicates occur only positively,
through Huber's Π and Path clauses for the positions. So the clauses define
a monotone operator with a least fixed point. It is the union of the
operator's stages, and each derivation is a well-founded tree with an
ordinal height. Exactly one clause applies to a term and reduction is
deterministic, so a computable term has one derivation, and the measures of
2.4 are functions of the term.

Positivity shows that the least fixed point exists, not that it contains
anything. Lemma C4 shows that it contains every constructor with computable
arguments. For instance:

- `Nat.zero` is V1, with no premises;
- `succ(zero)` is V1 over it;
- `loop @ i` is V2 with no arguments. At a face `i = ε`, `loop @ ε` reduces
  to `base` at every restriction, so N derives it, and that is V2's face
  premise.

### 2.3 Stability under substitution

**Lemma C3 (stability).** Let `f : J → I`. Then `⊩_I u : S(as)` gives
`⊩_J u f : S(as f)`, and `⊩_I u = v : S(as)` gives `⊩_J u f = v f`.
Derivations get no higher.

*Proof.* By induction on the derivation, as Huber's Lemma 3.6.

- **V1.** `u f` is V1 with restricted arguments: the data by the baseline's
  monotonicity, the positions because their Π clause quantifies over every
  `f` already.
- **V2.** If some `r_l f` is an endpoint, `⊩ u f` is a face premise of `u`.
  Otherwise `u f` is V2 with restricted arguments. Its face premises are
  among `u`'s: a `g` that makes `r_l fg` an endpoint does so for `u` at
  `fg`.
- **V3.** If `φf = 1`, it is a face premise. Otherwise `u f` is V3 with
  restricted parts.
- **N.** `u f` is non-introduced, and its premises are among `u`'s.

Equality is the same, clause by clause. In each case the new derivation is
a subderivation, or is built from restrictions of subderivations and from
face premises of `u`. ∎

Huber's other lemmas hold for `S(as)`, with his proofs for `N`:
reflexivity (3.5), reducts (3.7), the partial equivalence (3.8),
`u = u↓` (3.10) and the Expansion Lemma (3.11). The value clauses take the
part of `0` and `S u`, and their face premises are handled as Gl-C's. So
`S(as)` is a computable type in the sense that the baseline's fundamental
lemma quantifies over.

### 2.4 The measure

A derivation's weight is the model's (the model draft's section 3). There,
`β ↑ k` is the least multiple of `ω^k` above `β`.

- **V1 or V2** at `c_k`: the supremum of its positions' weights, `↑ k`. A
  position's weight is the supremum of the weights of the derivations at
  `S` that its Π and Path clauses contain: at every `f`, arity argument and
  point of its cube.
- **V3:** the larger of the base's and the tube's weights.
- **N:** the supremum over `f` of the weights of the `u f↓`.

`μ(u)` is the pair of weight and height, ordered lexicographically.
Positions are lighter than their constructor. The parts of a V3 value and
the reducts of an N term have lower derivations, of no greater weight.
Restriction does not increase `μ`: in C3's cases the derivation of `u f` is
built from restrictions of lower derivations, or is a face premise of `u`,
and a V2 value's face premises are lighter than it by the block bound
below.

**Block bound.** Let the positions of `c_k(ts, qs) @ rs` weigh at most
`ω^k · δ + σ`, with `σ < ω^k`. Let `E` be a constructor expression over
`c_1 … c_{k-1}`, with `wt(E) < ω^k` as in the model draft. Evaluated at
these arguments, restricted along any `f`, `E` weighs at most
`ω^k · δ + σ + wt(E) < ω^k · (δ + 1)`.

*Proof.* By induction on `E`, from the derivations of Lemma C4:

- a position application weighs at most its position;
- `c_m` at non-endpoint formulas weighs its positions `↑ m`, which the
  model's Lemma M0 bounds;
- at an endpoint, N derives it from a piece over still earlier
  constructors;
- a path application of `⟨i⟩ E′` is derived by N from its reduct. ∎

## 3. Coherence of the new reductions

A redex `t` at `I` becomes computable through the Expansion Lemma, which
needs, for every `f`, `t f↓` computable and `⊩ t f↓ = (t↓) f`. By Lemma H2,
either the rule that reduces `t` also reduces `t f`, to `(t↓) f`, or
substitution has made a formula an endpoint or a face true, and another
rule reduces `t f`. The pairs of rules that meet this way are CP01–CP10.

**Lemma C1 (coherence, under computability).** Let `t ≻ t↓` at `I` by a
rule of sections 3.2–3.7, and let `f : J → I`. Assume:

- **(a)** `t f↓` and `(t↓) f` are computable;
- **(b)** if the rule of `t` does not reduce `t f`, the join of their
  critical pair, taken at `t f`, has computable terms, and each of its
  steps is a computable equality: a reduction whose redex is computably
  equal to its reduct, or a baseline conversion, sound by the baseline's
  fundamental lemma.

Then `⊩_J t f↓ = (t↓) f`.

*Proof.* If the rule of `t` reduces `t f`, then `t f↓` is `(t↓) f` up to
bound names, and reflexivity (3.5) applies. Otherwise the join connects
`t f↓` and `(t↓) f` by steps that are computable equalities by (b), and
symmetry and transitivity (3.8) chain them. ∎

The critical-pair analysis shows only that the joins exist. The hypotheses
(a) and (b) are discharged in section 4, inside the fundamental induction,
in the case that handles each redex. There the other terms of a join are
boundary pieces, positions and parts of an `hcomp`, all of smaller `μ`, so
the induction hypothesis makes them computable and equal to their reducts.
A join's remaining steps are baseline redexes and conversions, which the
baseline's fundamental lemma covers.

| Pair | Case | `t f↓` and `(t↓) f` are computable by | They are computably equal by |
| --- | --- | --- | --- |
| CP01 | C6, V2 | the induction hypothesis at the lighter piece; the clause, by Huber's Path clause | the semantic Lemma H1, whose `Iota` steps are at lighter scrutinees |
| CP02 | C4 | C4 at earlier constructors | premise P1, with the baseline's fundamental lemma |
| CP03 | C6, V3 | the induction hypothesis at the tube; the baseline's composition in the motive | the baseline's face rule for composition |
| CP04 | C2 (b) | the tube; C4, and the induction hypothesis at the positions | the tube's own arguments, which the telescope composition returns on its face |
| CP05 | 4.5 | the tube; C2 (a) | C2 (a) on the transport's constancy face |
| CP06 | C2 (a), V2 | the induction hypothesis at the lighter piece; V3 | the wall at `h = 1` is that transport, and the filler is `θ₀` at `0` |
| CP07 | C2 (a), V2 | the induction hypothesis at the lighter pieces | pieces agree at corners (C4), and transport respects equality (induction hypothesis) |
| CP08 | C2 (a) | `u f`, by C3; the structural reduct, by the case at hand | the filler and the squeezes are constant on `φ` |
| CP09 | C2 (a), V3 | the induction hypothesis at the tube | both are the transport of `w(1) f` |
| CP10 | 4.3 | the tube | the empty tube is never selected |

This is where canonicity depends on item 2, approved on 2026-09-30: the
critical pairs name every obligation. The joins are the syntactic
counterparts of the model's naturality lemmas ([model draft](h1-model.md),
M3–M6).

## 4. The fundamental lemma: the H1 cases

The fundamental lemma is proved by induction on typing derivations, and
its baseline cases are assumed. The H1 cases below use Lemmas C2 and C4–C6.
Each lemma's own induction runs inside one case of the fundamental lemma,
where the parameters, motive, clauses and lines are computable by the outer
induction hypothesis. Every reduction is made computable by the Expansion
Lemma, with Lemma C1 at the restrictions where the rule changes.

### 4.1 Formation (3.1)

`S{ℓs_r}(as)` is a computable type when `as` are computable: its predicates
are those of section 2, and 2.3 gives them Huber's lemmas. Computably equal
parameters give computably equal types, whose predicates agree, as Huber's
Lemma 3.8 (1) requires. That is an induction on derivations: the clauses at
`as` and at `as′` read computably equal data types, arities and endpoints.

### 4.2 Constructors and boundaries (3.2)

**Lemma C4 (constructors).** Let `ts` be computable at `D_k(as)`, and `qs`
at the positions' types. Then:

1. `(c_k(as)(ts, qs)) @ rs` is computable for all formulas `rs`, endpoints
   included, and computably equal arguments give computably equal terms.
   Where some `r_l = ε`, it is computably equal to its boundary piece.
2. Every constructor expression `E` over `c_1 … c_{k-1}`, evaluated at
   these arguments, is computable at its cube type. Computably equal
   arguments give computably equal evaluations.
3. Two constructor expressions that are convertible in `c_k`'s admission
   context by the fragment of premise P1 (model draft, section 4) evaluate
   to computably equal terms.

*Proof.* By induction on `k`.

- **(2),** by induction on `E`:
  - `q_j(us)`: the data terms `us` are baseline terms, computable by the
    baseline's fundamental lemma, and `q_j` is computable at its Π type.
  - `c_m(us, Es′)` with `m < k`: (1) at `m`. Each positional argument
    `λ ys. E′` is computable at its Π type by (2) at every `f` and every
    computable `ys`, and its endpoints are right by (3).
  - `E @ r`: Huber's Path clause for `E`.
  - `⟨i⟩ E`: `(⟨i⟩ E) f @ r` reduces to `E[f, r/i]` by path β, which is
    closed under substitution, so the Expansion Lemma applies.
- **(3).** The admission context holds `s`, `c_1 … c_{k-1}`, the data and
  the positions as variables. Instantiate `s` with `S(as)`, each `c_m` with
  `Con(m; S(as))`, which is computable at `T_m` by (1) at `m`, and the
  data and positions with the given arguments. This substitution is
  computable. By P1 the conversion uses only baseline rules: path β and
  η, congruence, dimension substitution, data conversion, and the path step
  at an endpoint of a variable's annotation. So the baseline's fundamental
  lemma makes the two instances computably equal. At `c_m(…) @ ε` the path
  step becomes the boundary rule of an earlier constructor, whose equality
  is (1) at `m`.
- **(1).** Suppose first that some `r_l` is an endpoint. The term is
  non-introduced, and at every `f` its reduct is the piece
  `E_{k,l,ε}[f]` at the first face that holds, computable by (2). Two
  restrictions give either the same piece, or pieces of two faces at a
  corner, which are convertible by the cube boundary's typing and so
  computably equal by (3): this is CP02. So N derives the term, and the
  Expansion Lemma equates it with its piece. If no `r_l` is an endpoint,
  the term is V1 or V2, and V2's face premises are the endpoint case at
  `J`. Equality follows by the same clauses. ∎

C4 is the constructor case of the fundamental lemma and the soundness of
the boundary rule. By the block bound, its pieces are lighter than the
constructor.

### 4.3 Formal composition (3.4)

`hcomp^i S(as) [φ ↦ w] w₀` with computable, compatible parts and `φ ≠ 1`
is V3. Its face premise: at `f` with `φf = 1`, the term reduces by `Face`
to `w(1) f` at every further restriction, so N derives it. On a face that
holds it equals `w(1)`, by the Expansion Lemma.

A tube on the empty face is dropped. The shorter `hcomp` is computable, and
at a restriction where another tube's face holds, both orders select that
tube: the empty tube is never selected (CP10). So the Expansion Lemma
applies.

### 4.4 Transport, and composition of a data sort (3.3, 3.5)

Transport of a higher sort fills the argument telescope, whose path
positions have dependent endpoints. The filled positions can outweigh the
original ones, as in the model draft's `pack`, but they stay in the
constructor's block.

**Lemma C5 (telescope filling).** Let `u = c_k(as(0))(θ₀)`, or that at
formulas `rs`, be a computable value of a higher sort whose positions weigh
at most `ω^k · δ + σ`, with `σ < ω^k`. Let `as(i)` be a computable line of
parameters, constant on `φ`. Assume C2 (a) for every term lighter than
`ω^k · (δ + 1)`. Then:

- the filler `θ(i) := fill^i Θ_k(as(i)) [φ ↦ θ₀] θ₀` is computable at
  `I, i`, and computably equal to `θ₀` at `i = 0` and on `φ`;
- its positions weigh at most `ω^k · δ + σ′`, for some `σ′ < ω^k` that
  depends only on `σ` and the signature;
- `E[θ(i)]` is computable and lighter than `ω^k · (δ + 1)`, for every
  constructor expression `E` over `c_1 … c_{k-1}`.

*Proof.* Along the telescope, with `σ_0 := σ`, as the model's Lemma M4a.

- The data are filled by the baseline.
- Position `j` has type `Π (ys : A_j(i)). C_j(i)`. The baseline's Π rule
  fills an arity argument backward and composes in the cube `C_j(i)`. The
  cube's faces are the endpoint expressions `P` at `θ_{<j}(i)` and the
  arity argument, so the composition in `S(as(i))` has the tube `φ ↦ q_j`
  and, on each face of the cube, the line `P[θ_{<j}(i), y(i)]`.
- Those endpoint lines are computable by C4. The earlier filled positions
  weigh at most `ω^k · δ + σ_{j-1}`, so by the block bound the lines weigh
  at most `ω^k · δ + σ_{j-1} + wt(P)`.
- The composition is 3.4's `hcomp` of transports. The transported terms
  are lighter than `ω^k · (δ + 1)`, so C2 (a) makes their transports
  computable, of no greater weight, and 4.3 makes the `hcomp` computable.
  It weighs at most `ω^k · δ + σ_j`, where `σ_j` is the larger of `σ` and
  `σ_{j-1} + wt(P)` over the cube's faces, still below `ω^k`.

`σ′` is `σ_j` for the last position. The last claim is the block bound at
`σ′`. ∎

**Lemma C2 (transport and data-sort composition).** Let `as(i)` be a
computable line of parameters at `I, i`, constant on `φ`.

- **(a)** For a higher sort, if `⊩ u : S(as(0))`, then
  `⊩ transp^i S(as(i)) φ u : S(as(1))`, of weight at most `u`'s, and it is
  computably equal to `u` on `φ`. Computably equal inputs give computably
  equal results.
- **(b)** For a data sort, let `⊩ u₀ : S(as(0))`, and let `w` be
  computable on `φ` at `I, i`, with `w(0) = u₀` there. Then
  `comp^i S(as(i)) [φ ↦ w] u₀` is computable, and computably equal to
  `w(1)` on `φ`. Computably equal inputs give computably equal results.

*Proof.* By induction on `μ` of `u`, or of `u₀` in (b), for all lines and
faces at once. Write `t` for the transport or the composition. Each case
shows `t↓` computable, and then applies the Expansion Lemma, with C1 at the
restrictions where the rule changes. Equality follows by the same cases on
both derivations.

- **`φ = 1`.** `t` reduces by `Face` to `u`, or to `w(1)`, and so does
  every restriction of it. That reduction is closed under substitution, so
  the Expansion Lemma applies. Below, `φ ≠ 1`.
- **N.** The argument reduces first, so `t f↓` is the transport or
  composition of `u f↓`. That is computable by the induction hypothesis,
  since `u f↓` has a lower derivation of no greater weight. Coherence
  follows from `u f↓ = (u↓) f` (3.10, C3) and the equality part of the
  induction hypothesis. Where `φ` becomes true in (a), `t f` reduces by
  `Face` to `u f`, and `(t↓) f` to `(u↓) f`, computably equal by 3.10; in
  (b) both reduce to `w(1) f`.
- **(a), V1.** `t↓ = c_k(as(1))(θ(1))`, computable by C5 and C4. Its
  positions weigh at most `ω^k · δ + σ′`, so it weighs at most
  `ω^k · (δ + 1)`, `u`'s weight. The filler commutes with substitution, so
  where `φf ≠ 1` the rule reduces `t f` to `(t↓) f` (H2). Where `φf = 1`
  this is CP08: `t f↓ = u f`, and `(t↓) f = c_k(θ(1) f)` equals
  `c_k(θ₀ f) = u f` by the filler's constancy on `φ` and C4.
- **(a), V2.** `t↓` is 3.5's corrected `hcomp`, and it is V3:
  - its base `v = c_k(as(1))(θ(1)) @ rs` is computable by C5 and C4;
  - each wall squeezes `b_{l,ε}(i) = E_{k,l,ε}[θ(i)]`, computable by C4 and
    lighter than `u` by C5, so the induction hypothesis makes its
    transports computable;
  - walls meet in computably equal terms: the pieces agree at corners (C4),
    and the induction hypothesis's equality part carries that through the
    transports (CP07). On `φ ∧ (r_l = ε)` the squeeze is constant and
    equal to `u` there;
  - at `h = 0` each wall is `b_{l,ε}(1)`, which is `v`'s piece on its face
    by C4, and on `φ` the base `v` is `u`.

  It weighs at most `u`'s weight: the walls are lighter and `v` weighs
  `ω^k · (δ + 1)`. Coherence:
  - where no formula or face changes, H2;
  - where `r_l f = ε`, CP06. `t f↓` is the transport of the piece
    `E_{k,l,ε}[θ₀ f]`, computable by the induction hypothesis. `(t↓) f`
    selects the wall at `h = 1`, the transport of `b_{l,ε}(0) f`. The two
    are computably equal, since `θ(0) = θ₀` computably;
  - with several faces, CP07; where `φf = 1`, CP08.
- **(a), V3.** `t↓ = hcomp^j S(as(1)) [ψ ↦ transp w(j)] (transp w₀)`, V3
  by the induction hypothesis at the parts. Coherence is CP09 where `ψ`
  becomes true, CP08 where `φ` does, and H2 otherwise.
- **(b), V1.** As Huber's case N-C for composition in `N`, without the
  discreteness of `N`.
  - Each irreducible face `α ≤ φ` is a conjunction of equations, so a
    substitution `ᾱ`. The tube `w ᾱ` is computable at `Iα, i`, so it
    reduces to some `c_{k′}(θ_w)`. Restricted to `i = 0` it is computably
    equal to `u₀ ᾱ`, which reduces to `c_k(θ₀ ᾱ)`. Values with different
    indices are never computably equal, so `k′ = k`, and the rule of 3.3
    fires.
  - Its reduct is `c_k(as(1))(comp^i Θ_k(as(i)) [φ ↦ θ_w] θ₀)`. Data are
    composed by the baseline. Each position is composed in its cube by (b)
    at that position, whose derivation is lower, with the endpoint
    expressions, computable by C4, as further tubes. So C4 makes the
    reduct computable.
  - Coherence: CP04 where a tube's face becomes true, since the rule then
    returns the tube's own arguments on that face; an empty tube contributes
    nothing; H2 otherwise. ∎

A data sort has no V2 or V3, and its transport is (b) with `w := u₀`. It
needs only the height: the tubes of its position compositions are never
recursed into as bases.

### 4.5 General composition of a higher sort (3.4)

`comp^i S(as(i)) [φ ↦ u] u₀` reduces to an `hcomp` of transported parts.
That reduct is V3, by C2 (a) and 4.3. Where `φ` becomes true this is CP05:
the reduct selects `transp^k S(as(1 ∨ k)) 1 u(1)`, whose constancy face
holds, so C2 (a) equates it with `u(1)`, the source's `Face` reduct.

### 4.6 The eliminator (3.6, 3.7)

**Lemma C6 (elimination).** Let `M` be a computable family over `S(as)`,
at any level, and `ms` computable clauses at their clause types. If
`⊩ u : S(as)`, then `⊩ elim_{M,ms}(u) : M(u)`, and computably equal
scrutinees give computably equal results. Moreover, if `u` is
`c_k(ts, qs) @ rs`, then for every constructor expression `E` over
`c_1 … c_{k-1}` at `u`'s arguments, restricted along any `f`, the
**semantic Lemma H1** holds: `⊩ elim^C(E) = ⟦E⟧[q̄s]`.

*Proof.* By induction on `μ(u)`.

- **N.** As Huber's `natrec` (his Lemma 4.10): `elim(u) f` reduces to
  `elim(u f↓)`, which is computable by the induction hypothesis, and
  coherent by 3.10 and the induction hypothesis's equality part.
- **V1.** `elim(u) ≻ m_k(ts, qs, q̄s)`. This reduction is closed under
  substitution, since every `u f` is again V1. Each
  `q̄_j = λ ys. elim^{C_j}(q_j(ys))` is computable at its displayed type:
  pointwise by the induction hypothesis at the lighter position. Its
  endpoints `elim(q_j(ys) @ ε)` equal `⟦P⟧` by the induction hypothesis's
  equality part, since `q_j(ys) @ ε = P[…]` by the Path clause, and by the
  semantic H1 for the endpoint expression `P`, at lighter scrutinees. The
  clause is computable, so the reduct is, and the Expansion Lemma applies.
- **V2.** `elim(u) ≻ m_k(ts, qs, q̄s) @ rs`, computable at the clause
  type's nested `PathP` by the Path clause. Where no formula changes, H2.
  Where `r_l f = ε` this is CP01:
  - `t f↓ = elim(E_{k,l,ε}[f])` is computable by the induction hypothesis
    at the lighter piece;
  - `(t↓) f = m_k(…) f @ rs f` is computable, and by the Path clause's
    endpoint premise it equals `⟦E_{k,l,ε}⟧[f]`;
  - the semantic H1 equates the two.
- **V3.** `elim(u) ≻ comp^j M(hfill^j) [ψ ↦ elim(w(j))] (elim(w₀))`. It is
  computable by the baseline's composition in the computable family `M`
  along the computable line `hfill^j`. Its tubes and base are computable by
  the induction hypothesis at lower derivations, and agree at `j = 0` by
  its equality part. Where `ψ` becomes true
  this is CP03: the scrutinee reduces by `Face` and the composition by the
  baseline's face rule, both to `elim(w(1) f)`, and that rule's soundness
  gives the equality. H2 otherwise.
- **Semantic H1,** by induction on `E`:
  - a position application: `q̄_j(us)` reduces by β to
    `elim^C(q_j(us))`, an expansion the baseline covers;
  - `c_m(us, Es′)` at non-endpoint formulas: one `Iota` step,
    `elim(c_m(…)) ≻ m_m(us, Es′, elim(Es′))`, at a scrutinee lighter than
    `u` by the block bound, then congruence of `m_m` and induction on `Es′`;
  - `c_m(…) @ rs′` where some formula is an endpoint: the scrutinee takes
    the boundary step and the clause the path step, and the semantic H1 at
    the lighter value `c_m(…) @ rs′` (induction hypothesis, case V2)
    equates the results;
  - path application and abstraction by the Path clause and path β. ∎

### 4.7 The computation rules as equalities

Every rule of 3.7 is sound as a judgmental equality. At computable
instances and at every restriction, a redex is computably equal to its
reduct: the Expansion Lemma's second conclusion, in the case that made the
redex computable. That is C4 for boundary reduction; C6 for `Iota` and the
elimination of `hcomp`; C2 for data-sort composition and transport; 4.5 for
higher composition; and V3's face premise for `Face`. The congruences are
the equality parts of the same lemmas.

### 4.8 Levels

A motive may land at any level `l′`, including UU tiers (D7). `M(z)`'s
computability is defined at its level by the level induction of G0 3.5. No
rule reads a level (2.4), so the predicates at fixed recorded levels
suffice (D8). An erased level only names a universe, related by cumulativity
as in G0 (D9).

## 5. Canonical values

A computable term reduces to a value. N at `f = id` gives a reduct with a
lower derivation, and heights are well founded.

- **(i).** For a data sort the value is V1, with computable arguments. When
  `S` is first-order, iterate on the positions, whose derivations are
  lower: this gives a finite closed constructor term. For `Nat` it is a
  numeral.
- **(ii).** For a higher sort the value is V2, a constructor at
  non-endpoint formulas with computable arguments, or V3, an `hcomp` with
  `φ ≠ 1` whose base and tube are computable.
- **(iii).** C6 at a V3 scrutinee gives composition in the motive. For a
  data-sort motive, that composition is computable by C2 (b), so it reduces
  to a constructor with computable arguments.

## 6. Assumptions, and what review must check

- **Assumed.** The baseline's computability predicates and fundamental
  lemma (specification 4.1, G0 3.5, 3.6), generic in the computable types
  they quantify over.
- **Premise P1** of the model draft, for C4 (3): the agreement of boundary
  pieces at corners, and the endpoints of positional arguments.
- **Item 2.** The critical pairs CP01–CP10, approved on 2026-09-30, name the
  coherence obligations. Their computable joins are proved here.
- **Metatheory.** An inductive definition of predicates with set-sized
  branching, within ZFC and G0's universes.

Review must accept:

- the clauses V1–V3 and N, with V2's and V3's face premises (2.1, 2.2);
- stability, Lemma C3, and Huber's lemmas for the new predicates (2.3);
- the weight of derivations and the block bound (2.4);
- Lemma C1 and its table of obligations (section 3);
- Lemma C4, and its use of P1 with the baseline's fundamental lemma;
- the telescope filling of C5, and the measure in C2;
- the constructor-index argument in C2 (b);
- Lemma C6 and the semantic Lemma H1;
- the level cases.
