# H1 model and canonicity review findings

Reviewed on 2026-09-30:

- [H1 model](docs/roadmaps/h1-model.md)
- [H1 canonicity](docs/roadmaps/h1-canonicity.md)

The review found three substantive issues. Release checklist items 1 and 3
should remain open until they are resolved.

## 1. The computability predicate's least fixed point is empty

**Location:** [h1-canonicity.md, section 2](docs/roadmaps/h1-canonicity.md#2-the-predicate-for-a-declared-instance),
lines 83–94.

Every V1–V3 clause requires each restriction `u f` to be computable. Taking
`f = id` makes computability of `u` a premise of itself. Consequently, even
`Nat.zero` has no well-founded derivation: the empty predicate already
satisfies the stated inductive closure.

**Required change:** Separate the canonical-value clauses from expansion,
then prove stability under substitution. Strict positivity alone does not
resolve this circularity.

## 2. M4's weight bound does not account for path-position endpoints

**Locations:** [h1-model.md, section 5](docs/roadmaps/h1-model.md#5-kan-structure),
lines 241–255; also [h1-canonicity.md, section 4](docs/roadmaps/h1-canonicity.md#4-the-fundamental-lemma-the-h1-cases),
lines 161–175.

The induction hypothesis bounds transport of carrier elements. Filling a
path-valued position also introduces endpoint tubes evaluated from earlier
positions. Their weights can exceed the asserted `β := sup ‖Q‖`.

For example, this constructor order is admitted for parameters `A` and
`a : A`:

```text
base : s
loop : Path(s, base, base)
step : s → s
pack : Π(f : A → s).
       Path(s, step(f(a)), step(f(a))) → s
```

Take `A` to be a baseline pushout with a connecting path, and `f` mapping its
endpoints to `base` and its connecting path to `loop`. At the initial
endpoint, use `p := refl(step(base))`. The initial position bound is
`β = ω³ + ω`.

Moving `a` to an interior point of that path makes the transported
position's endpoint `step(f₁(a₁))`, of weight `ω³ + ω²`; the transport's
`hcomp` wrappers preserve the loop's weight. By M1, the position containing
that endpoint must have at least this weight, exceeding `β`. The enclosing
`pack` therefore also exceeds its claimed original weight.

**Required change:** Revise the measure and prove a telescope-filling lemma
that covers dependent endpoints. C2 inherits this problem.

## 3. C1 assumes computable equality from syntactic joinability

**Location:** [h1-canonicity.md, section 3](docs/roadmaps/h1-canonicity.md#3-coherence-of-the-new-reductions),
lines 103–109.

CP01–CP10 establish common reducts. They do not establish that those reducts
are computable. C1 has no computability hypotheses, yet uses the joins to
conclude computable equality and then supplies that conclusion to the
fundamental lemma.

[Huber's Expansion Lemma, Lemma 9](https://link.springer.com/article/10.1007/s10817-018-9469-1),
requires computability of the reduct. That premise cannot be replaced by
the existence of a common reduct.

**Required change:** State C1 under explicit computability hypotheses and
establish the joins' computability and equality within the fundamental
induction.
