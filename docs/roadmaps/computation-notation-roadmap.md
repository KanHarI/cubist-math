# Computation notation: monadic do and arrows

Status: planned on 2026-09-25. No notation or supporting interfaces in this
roadmap are implemented. Code blocks are proposed syntax or schematic
signatures, not checked examples. Existing proofs cited below are evidence
for the work, not implementations of it.

This extends the [language feature proposal](inductive-language-features.md)
with one family of computation blocks: monadic `do` and its generalization
to arrows. Both elaborate to ordinary checked terms. This roadmap owns the
notation and its supporting library interfaces; the
[work plan](work-plan.md#computation-notation-track) places it alongside the
existing rebuild. It does not resume paused mathematical developments.

## Purpose and scope

Let mathematical constructions name intermediate values while retaining the
structure in which those values are used. The first targets are existence
proofs and substitution in free algebras. Probability and structured
composition supply later examples.

Arrows generalize monads: a monad `M` gives Kleisli arrows
`Hom(A, B) = A -> M(B)`. General arrows need fewer operations than monads;
dynamic application is an additional capability. Thus the two forms share
a design, with separate lowering rules for their available operations.
See the [introduction to arrows](https://www.haskell.org/arrows/).

The first release provides explicit structure selection, sequential binds,
pure local definitions and results. Existing proof blocks, `let`, `obtain`
and `calc` retain their roles. General typeclass search, automatic effect
lifting, an IO runtime, recursive `do`, feedback, and dependent or indexed
bind are outside that release.

Neither notation needs a new kernel rule. Particular instances can need
the kernel roadmap: native truncation and the single-sort free algebra
declarations used here need H1; the proposed partiality construction needs
H3. Representing partiality
does not grant permission for nonterminating kernel evaluation.

## 1. Mathematical acceptance examples

### Existence proofs: closure of linear span

The archive defines membership in a span as the propositional truncation of
a finite linear-combination witness in
[linear_span.cubist](../../archive/first-library/linear_span.cubist).
The existing `span_add` in
[span_subspace.cubist](../../archive/first-library/span_subspace.cubist)
uses two nested truncation eliminators. Its mathematical argument is:
take representations of `x` and `y`, concatenate them, and conclude that
`x + y` has a representation.

With `MereMonad` naming the selected operations, the proposed body is:

```text
do using MereMonad {
  wx <- hx;
  wy <- hy;
  span_add_witnesses(K, V, P, x, y, wx, wy);
}
```

The final helper already returns a truncated witness. The block therefore
expands to the same nested elimination pattern; it adds no choice principle.
Trying to finish with an untruncated representation is rejected. This
notation does not turn `Mere(A)` into a general source of values of `A`.

**Acceptance:** reproduce the rebuilt span-closure proof, compare its source
and generated term with the explicit proof, and reject witness escape.
The archive's truncation uses assumptions; record those when using it as a
baseline. Assumption-free `computable` acceptance waits for native H1
truncation, rather than hiding the archive's dependencies.

### Substitution in free algebras

For a suitable algebraic theory `T`, a map `A -> FreeT(B)` assigns an
expression to each generator. Its extension `FreeT(A) -> FreeT(B)` is
substitution, supplied by `fold` into the free model on `B`.

```text
do using FreeTMonad {
  a <- expression;
  replacement(a);
}
```

Here `expression : FreeT(A)` and `replacement : A -> FreeT(B)`. The binding
is interpreted by substitution throughout the expression. For groups this
substitutes words for generators; for commutative rings it supplies the
free-algebra account of polynomial substitution.

**Acceptance:** construct `pure` from generators and `bind` from `fold` for
one supported theory. Prove the unit and associativity laws using its
universal property, including any respect/coherence obligations. Compare a
two-stage substitution with composed substitution by a checked equality,
and evaluate a closed example. Do not derive a monad for every theory
without establishing the required free construction and functoriality.

### Probability: joint distributions and composition

A later instance uses finite-support rational probability distributions:

```text
do using DistributionMonad {
  x <- initial;
  y <- transition(x);
  pure (x, y);
}
```

For finite carriers the resulting joint mass is
`joint(x, y) = initial(x) * transition(x)(y)`. Returning just `y` gives the
marginal, summing over `x`. These blocks describe distributions as
mathematical values. They do not execute random sampling.

**Acceptance:** prove normalization and the joint/marginal formulas, and
evaluate a small rational example once the required library exists.
Continuous measures, integration and conditioning are separate work.
Probability monads and categorical composition also support substantial
theorems about statistical experiments; see
[Fritz, Gonda, Perrone and Rischel](https://arxiv.org/abs/2010.07416).

These three examples justify the monadic specialization. The arrow release
also needs an example using only the weaker arrow interface, as specified
in milestone N4.

## 2. Checked interfaces and explicit scope

Begin with explicit records of operations. At a fixed universe, the monadic
interface has the schematic fields:

```text
Carrier : U -> U
pure    : forall A : U, A -> Carrier(A)
bind    : forall A B : U, Carrier(A) -> (A -> Carrier(B)) -> Carrier(B)
```

`do using M` selects one such record. In the mathematical signatures below,
`M(A)` abbreviates `M.Carrier(A)`; this is not a proposed implicit coercion
from records to functions. Every omitted type or level argument must have
an explicit spelling. No global instance search or implicit conversion
between structures is required.

Separate operations from a record of checked laws. Parsing and lowering
need the operation types. Library claims about a monad and algebraic
rewriting additionally require its unit and associativity proofs. A
matching set of field names is not evidence for the laws.

The monad laws state, with type arguments omitted:

```text
M.bind(M.pure(a), f) = f(a)
M.bind(m, M.pure) = m
M.bind(M.bind(m, f), g) = M.bind(m, fun a => M.bind(f(a), g))
```

Models from the theory machinery may package these interfaces where that
machinery supports them. The notation must also accept ordinary records:
polymorphic operations over types are not automatically a strictly positive
signature with an initial model. Specify the universe levels of the records
and their fields through G0; do not silently identify `U` with `next(U)`.

Laws are paths, with their actual proof dependencies. Neither law records
nor the notation introduce proof irrelevance or claim to construct a fully
coherent higher monad or higher category. Initial categorical theorems can
use set-valued instances; higher coherence is separate library work.

## 3. Monadic blocks

### Syntax and lowering

```text
do using M {
  x <- mx;
  let z := h(x);
  y <- f(z);
  pure (x, y);
}
```

The block has type `M(B)` for an inferred or explicit result type `B`.
Here and below, expansions omit inferable type arguments:

| Source form | Expansion |
| --- | --- |
| Final `pure e;` | `M.pure(e)` |
| Final computation `e;` | `e`, checked against the block's expected type |
| `x <- e; rest` | `M.bind(e, fun x => rest)` |
| Nonfinal computation `e; rest` | `M.bind(e, fun _ => rest)` |
| `let x := e; rest` | An ordinary local definition inside the continuation |

`pure` introduces the final result; it is not an early return. Nested blocks
select their own structure explicitly. The elaborator uses fresh binders,
preserves source order, and retains source locations for each expansion.
The [Haskell do translation](https://www.haskell.org/onlinereport/haskell2010/haskellch3.html#x8-470003.14)
is a precedent; Cubist does not import its partial pattern behavior.

Start with variable binds. Add exhaustive product and dependent-pair
patterns through the existing checked matching service. Refutable patterns
require an explicit exhaustive `match`; the language never inserts an
error, an assumed inhabitant, or a hidden failure operation. If the selected
structure has a failure value, authors can return it in an explicit branch.
Ordinary conditionals and matches may return monadic computations without
introducing a separate monadic branching capability.

### Dependent types and elimination

The `B` in ordinary `bind` is fixed outside its continuation. Terms and
local types in the continuation may depend on `x`, but that `x` cannot escape
into the enclosing result type. For example, a block can return
`M(exists x : A, P(x))` by constructing a dependent pair. It cannot return
`M(P(x))` with a locally bound `x` escaping its scope.

Bind patterns retain dependencies between pair components. Reuse dependent
matching without K; do not erase equations between indices or insert
unreported transports to make a block typecheck. Unsupported dependent or
indexed bind signatures receive a local diagnostic; they are not coerced
into the ordinary monad interface.

For truncation, bind is a checked eliminator into a truncated target. All
restrictions follow from that eliminator's type. There is no new rule for
extracting witnesses, selecting quotient representatives, or performing
choice under the appearance of a local binding.

## 4. Arrow blocks and their monadic specialization

An arrow interface supplies the following schematic operations. `A and B`
here is a non-dependent product, and `then(f, g)` means first `f`, then `g`:

```text
Hom   : U -> U -> U
arr   : (A -> B) -> Hom(A, B)
then  : Hom(A, B) -> Hom(B, C) -> Hom(A, C)
first : Hom(A, B) -> Hom(A and C, B and C)
```

The associated law record states the category laws, preservation of pure
composition by `arr`, and the usual compatibility/naturality laws for
`first`. N1 must give their full checked signatures before implementation.

The proposed arrow form names the input and intermediate outputs:

```text
proc using R (x : A) {
  y <- f -< x;
  yield (x, y);
}
```

For `f : R.Hom(A, B)`, this defines `R.Hom(A, A and B)`. Its explicit
expansion is:

```text
R.then(
  R.arr(fun x => (x, x)),
  R.then(R.first(f), R.arr(fun (y, x) => (x, y)))
)
```

`yield e` lifts a pure output expression through `arr`. A block may also end
with an arrow command `g -< e`. Local `let` definitions and nonfinal commands
are compiled by carrying an environment of needed variables through
products. Unused outputs are discarded through lifted projections. The
inspector shows that environment and the generated operations.

### Capabilities and scope

| Construct | Required operations | Scope rule |
| --- | --- | --- |
| `f -< e`, binds, `let`, `yield` | Basic arrow interface | `e` may use block locals; the arrow expression `f` cannot |
| Conditional or sum-case selection between commands | `ArrowChoice` operations for composing alternatives | Conditions may use locals; branch arrows retain their scope restrictions |
| Dynamic `f -<< e` | `ArrowApply` operation `app : Hom(Hom(A, B) and A, B)` | The arrow expression itself may depend on locals |

These restrictions allow the basic block to describe a composition whose
arrows are fixed while their inputs vary. Pure conditionals inside an input
expression need no `ArrowChoice`. An outer parameter may select a fixed
arrow before the `proc` block; local selection during the block needs the
appropriate capability. Capability records are explicit extensions of the
same selected arrow structure, not independently inferred dictionaries.
As with the basic interface, lowering uses their operation types, and
algebraic reasoning requires their associated checked laws. Ship lawful
instances of each supported extension.
The [GHC arrow guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/arrows.html)
documents the corresponding distinctions.

Haskell-style arrows already support copying and discarding inputs through
`arr`. They are not arbitrary categories: for example, lifting every plain
function is not an interface for continuous maps alone. General monoidal
diagram notation, with restricted copying or a restricted class of pure
maps, is a possible later extension and needs its own typing rules.

### Relationship to do

For a checked monad `M`, construct the Kleisli arrow instance:

```text
Hom(A, B)    = A -> M(B)
arr(f)(x)    = M.pure(f(x))
then(f,g)(x) = M.bind(f(x), fun y => g(y))
first(f)(x,z)= M.bind(f(x), fun y => M.pure((y,z)))
app(f,x)     = f(x)
```

Prove its arrow and application laws from the monad laws. Conversely, the
lawful `ArrowApply` interface recovers monadic expressive power. The basic
arrow interface alone does not promise that every value-dependent monadic
block can be translated into it.

Keep direct lowering to `bind` for `do`, and to arrow operations for `proc`.
Share binder handling, source mapping and diagnostics where appropriate.
Prove agreement of corresponding Kleisli and monadic examples by checked
equalities; do not require their generic expansions to be definitionally
equal or force all monadic terms through extra product environments.

## 5. Computability, laws and inspection

- Every accepted block produces a complete term for the native checker.
  Operation records, inferred arguments, pattern eliminators and inserted
  transports remain visible. Browser and CLI use the same elaborator.
- `computable` follows the expanded term's dependencies, including the
  selected operations. Selecting an assumed operation cannot bypass the
  existing dependency report. Law proofs used in a rewrite retain their
  dependencies as well.
- Evaluation follows the definitions of the selected operations. Monad and
  arrow laws are checked equalities, not new conversion rules. Ordinary
  lowering preserves sequencing; reassociation or removal of operations
  using laws needs a checked equality. Independent binds are not reordered
  merely because their values do not mention each other.
- Normalization of a block is not a promise that it returns a value outside
  its structure. A truncated result, distribution or partiality value keeps
  that type. Closed evaluation examples state the expected representation.
- Formatter round trips preserve the selected structure, bind scopes,
  command boundaries and explicit application capabilities. Diagnostics
  point to the statement needing a missing capability or illegal variable.

## 6. Milestones and gates

All milestones below are unfinished. N2 and N4 are implementations within
one design; N4 need not wait for every mathematical instance in N3.

| ID | Work | Dependencies | Acceptance |
| --- | --- | --- | --- |
| N0 | Record explicit mathematical baselines and proposed blocks | Existing archive; design only for new examples | Span closure, free substitution and an arrow example have stated types, assumptions and expected expansions; measure existing proofs without claiming unmeasured savings |
| N1 | Checked operation/law records and Kleisli construction | N0; G0 for generic universes; ergonomics 6 for record syntax | Full universe-correct signatures and laws; function, identity-monad and Kleisli instances check; no reliance on generating an initial model of a monad theory |
| N2 | Monadic `do` parser, elaboration, diagnostics, formatting and inspection | N1; HoTT A5; ergonomics 5 argument inference | Variable binds, local definitions, final computations and `pure`; representative explicit expansions agree; selected dependencies remain visible |
| N3 | Exhaustive patterns and mathematical monad instances | N2; ergonomics 7 matching; H1 foundations and free constructions for the relevant instances | Rebuilt span closure and one free-algebra substitution example check; witness escape and refutable binds fail; closed computable examples pass `evaluate` |
| N4 | Basic `proc` and arrow environment lowering | N1; HoTT A5; ergonomics 5 | Function and Kleisli comparisons check; a basic-arrow example works without `ArrowApply`; invalid local arrow selection fails; environments are inspectable |
| N5 | Explicit choice and dynamic application extensions | N4; N1's checked extension laws | Branching requests choice only when needed; dynamic application requests `app`; Kleisli examples agree with corresponding `do` blocks |

**N4 example beyond the monadic interface.** Start with static optional
functions `Hom(A, B) = Option(A -> B)`. Composition propagates absence;
`arr` wraps a function; `first` maps a present function over the first
component. The presence of a function is fixed independently of its input.
Prove the arrow laws and give a block that composes these partial
specifications. This interface has no general `app` implementing dynamic
application: the desired result could be absent for one input and present
for another, which a static optional function cannot express. Compare it
with `A -> Option(B)` to make the distinction visible. This is a small
library and elaborator fixture; a larger mathematical arrow application
must be justified by its own development.

**Later instances and extensions:** finite rational distributions after
their library prerequisites; partiality after H3; dependent/indexed binds
with explicit signatures; and diagram rendering derived from checked arrow
expansions. None is a gate for the first `do` release. Recursive commands,
feedback and automatic applicative translations require separate proposals.

## 7. Validation and integration

Each implementation milestone adds checked source examples to the reference
harness, including rejected examples with local diagnostics. Cover:

- capture avoidance, nested structures, explicit type arguments, universe
  errors, and formatter round trips;
- dependent-pair binds and forbidden result-type escape;
- truncation witness escape, uncovered patterns, and missing capabilities;
- arrow input duplication/discarding and the distinction between using a
  local in the input expression and using it to select an arrow;
- equality with explicit expansions, preservation of assumption reports,
  and closed evaluation for each computable instance;
- source size, checking time and kernel work on the mathematical baselines.

Use the existing canonicity fixture for releases. Do not require every
representation of a free algebra to have canonical word or polynomial
normal forms: its particular quotient and fold computation rules determine
what `evaluate` can promise. Publish the chosen examples and measurements.

The [language proposal](inductive-language-features.md) assigns monadic
blocks tier 2 and the broader arrow capabilities tier 3 within this shared
design. Ergonomics milestones 5–7 provide inference, structures and
matching; milestone 8 supplies computability checks. The HoTT roadmap owns
the shared goal and scope machinery. This roadmap adds no kernel stage and
does not make arrow notation a prerequisite for the library rebuild.

## Open decisions

1. **Surface syntax.** Confirm `do using`, `proc using`, `pure`, `yield`,
   `-<` and `-<<` against parser and formatter prototypes. The explicit
   capability distinction and lowering contracts are the design; the exact
   tokens remain provisional.
2. **Universe and object domains.** Start with explicitly levelled records.
   Decide which level-preserving instances to ship first, and how extensions
   whose hom types become input objects express universe closure.
3. **Theory integration.** Determine which polymorphic operation records
   the theory frontend can express. Do not block basic notation on generic
   free constructions or automatic structure identity for these records.
4. **Dependent and higher variants.** Require concrete mathematical examples
   before specifying indexed bind, dependent arrow environments, or higher
   coherence beyond the checked law records. Ordinary dependent pairs inside
   monadic continuations remain part of the initial design.
5. **Broader arrow mathematics.** Select a real library development before
   adding categorical diagram generalizations. The static optional-function
   fixture establishes the capability boundary, not widespread demand.
