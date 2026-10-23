# Simplicial types alongside cubical equality

Status: proposed on 2026-10-24 against main `41d507a0`. No directed kernel
rules, syntax or library packages are implemented by this roadmap. The
spelling `x ->[C] y` is agreed; the other syntax below is a design sketch.
The mixed type theory, its model and its preservation arguments remain open.
The [work plan](../work-plan.md#simplicial-types-track) owns scheduling;
runtime and numerical work retain their current priority.

## Purpose and existing foundations

Add directed shapes and extension types alongside cubical paths, so that
arrows, composition and higher coherence can be expressed through geometry.
The first mathematical target is synthetic category theory: Segal types,
functors, natural transformations and covariant families. Later targets are
coherent diagrams of spaces, categories of algebraic models and higher
algebra. This does not require replacing ordinary category theory or
waiting to develop set-based universal algebra.

Cubist currently has a De Morgan interval, endpoint face constraints,
cubical paths, composition, Glue, universes and H1 declarations. The
[interval/face API](../../../kernel/include/cubical.h) distinguishes interval
formulas from faces, but has no directed coordinate sort or order topes.
The [H1 specification](h1-signature-specification.md) describes cubical
constructors; it does not supply general simplicial extension types.
Theories elaborate to ordinary dependent records and add no kernel rule.
These are useful foundations, not an implementation of simplicial types.

A library of set-valued simplicial objects, or fixed finite coherent
diagrams, is also a possible project using existing records. It would not
supply the native shape contexts, strict restrictions and extension rules
proposed here, nor solve the coherence problem for arbitrary space-valued
simplicial objects.

## Preservation contract

Keep existing ordinary `U`, `IsProp`, `IsSet`, `HasLevel`, `prop U`,
`set U`, cubical equality and H1 truncation unchanged. In particular,
[`IsSet`](../../../library/hlevels.cubist) remains its current path-truncation
definition. Do not strengthen it with directed discreteness, or broaden its
quantification by importing a directed module. Quotients, powersets,
propositions, classical assumptions and algebraic carriers already use
these definitions and their ordinary meaning.

The design must provide an explicit ordinary/space setting and a directed
setting, with checked transitions between them. Their concrete mode or
universe syntax is still undecided. Separate names or an opt-in flag alone
do not establish the required interpretation.

In the directed setting, truncation of cubical identity and directed
discreteness are distinct properties. A type can have proposition-valued
identity types in the cubical direction and still have noninvertible arrows.
If a path-truncation predicate is exposed there, its scope and name must
distinguish it from the ordinary
library contract; this is not a redefinition of ordinary `IsSet`.

Three distinctions constrain imports and bridges:

- An embedding of the ordinary univalent universe must preserve its
  equivalences as paths. A directed classifier `Spaces`, whose arrows are
  arbitrary functions, is a different object. Taking a core or applying a
  proposed modality to an arbitrary directed universe is not by itself an
  interpretation of the old universe: its codes may still include directed
  objects.
- An ordinary polymorphic operation `F : U -> U` does not automatically
  become a functor on `Spaces`. For example, `A -> A` has mixed variance;
  an arbitrary function `A -> B` supplies no canonical forward map between
  these endomorphism types. Directed lifts require their own construction.
- Discrete fibers do not imply a covariant family. Over the walking arrow
  `0 -> 1`, the contravariant family `P(x) = Arrow(x, 0)` has fibers `Unit`
  and `Void`; a forward action would require `Unit -> Void`. Covariance
  needs separate evidence.

Existing module universe binders and assumptions keep their scope. In
particular, optional excluded middle and choice must not silently become
assumptions about all directed objects or families. Audit both current
library consumers and the remaining archive before enabling a bridge;
this roadmap does not claim that audit has been completed or identify a
bug in the current proofs.

The following obligations must be recorded separately:

| Obligation | Required evidence |
| --- | --- |
| Preserve old derivations | Old syntax, elaboration, definitions and rules retain their old derivations, with unchanged assumptions and universe scopes |
| Preserve old computation | Old terms retain their reduction and conversion behavior; new conversion rules do not identify previously distinct old terms |
| Preserve old meaning | An explicit interpretation of the ordinary fragment preserves its type formers, universe classification and theorem statements |
| Sound combined theory | A model of the stated mixed rules, including substitution, cubical composition, Glue, universes, H1 and cross-setting operations |
| Conservativity, if claimed | A separate argument that the extension proves no new propositions expressible entirely in the old language under the same assumptions |

A model or a passing regression suite does not establish all five. Preserving
old-term computation also does not establish canonicity for new terms at
old types. The existing [H1 model](h1-model.md) and
[canonicity argument](h1-canonicity.md) are relative to stated baseline
assumptions; they are not formal proofs of implementation correctness and
do not automatically extend to mixed directed rules. Do not promise that
the proposed extension is already conservative or that all existing proofs
have been semantically audited against it.

## Proposed Cubist interface

### Arrows and shared categorical notation

Keep the three forms distinct:

| Form | Meaning |
| --- | --- |
| `A -> B` | Existing function type |
| `x =[A] y` | Existing cubical equality in `A` |
| `x ->[C] y` | Proposed arrow type selected by the explicit category/type `C` |

For an ordinary `Precategory`, the last form elaborates to `C.Arr(x, y)`.
For a directed type it denotes an interval extension with endpoints `x`
and `y`; composition additionally requires Segal evidence. Resolution must
use a checked interface, with ambiguity and unsupported instances rejected.
Sharing notation does not identify an ordinary category with a directed
type. Their comparison is a separately proved adapter.

Develop `use C`, `g ∘ f`, `F.map(f)` and `alpha.at(x)` against the same
categorical interfaces where applicable. The ordinary version can ship
with L2.12/L3.4 before any directed kernel extension. Keep the `Category`
name for the planned ordinary univalent-category package; use library
interfaces such as `SegalType` and `RezkType` for the synthetic development.
`Hom` is already reserved for generated theory members, so a foundational
arrow library should not depend on redefining that name.

### Shapes, extensions and cells

The following is proposed syntax, not a checked Cubist program:

```text
shape Delta2 := (s, t : Directed) where t <= s;

// For x, y, z : C and f : x ->[C] y, g : y ->[C] z, h : x ->[C] z:
extension ((s, t) : Delta2) in C {
  on t = 0 => f @ s;
  on s = 1 => g @ t;
  on s = t => h @ s;
}

// Introduction against an expected extension type:
cell (s, t) => body
```

This triangle has vertices `(0, 0)`, `(1, 0)`, `(1, 1)`. Its edges express
that `h` is a composite of `f` and `g`. The extension is a **type of
sections with the specified boundary**, not an instruction that manufactures
a filler. It can be empty. A library definition `Triangle(C, f, g, h)` can
name it. Segal evidence makes the type of pairs consisting of a composite
`h` and such a triangle contractible; generic composition and its coherence
are then derived in the library.

The same extension notation should admit a dependent family after `in`.
Empty boundary braces should express a section over the entire shape
without prescribed boundary values.
`Directed` is a shape-coordinate sort, not a type or a set in ordinary `U`.
Tuple shape binders are coordinate contexts, not ordinary Sigma pairs.
Within `where` and `on`, geometric `=` and `<=` are topes, separate from
cubical paths and selected term notation. The endpoints `0` and `1` are
fixed geometric syntax, independent of imported numeral notation.

`cell` checks its body and all restrictions against the expected extension;
overlapping boundary clauses must agree strictly under their joint tope.
`@` selects cubical or directed coordinate application from its checked
head. Existing `path` remains cubical. Cubical reversal `~` and Kan
composition/filling do not become operations on arbitrary directed arrows.
For a function between directed types, the proposed term
`cell t => F(f @ t)` gives the induced arrow; the same expression is not a
new automatic directed lift of every ordinary polymorphic function.

The exact grammar, precedences, tope algebra and mode declarations must be
settled in ST0/ST1/ST2. In particular, a totally ordered simplicial interval
and the bounded-distributive-lattice ambient geometry used by later modal
research are distinct choices. The example above does not decide that
question or approve all future modalities.

If ST0 selects the lattice ambient geometry, the library must also state
and verify simpliciality: Segal and Rezk conditions alone do not ensure
it there. ST3's category interfaces and ST4's `Spaces` construction must
include that additional condition wherever required by the chosen model.

### Using the kernel features from the language

The first frontend release needs more than a parser:

- Bind coordinate sorts and tope assumptions through checking, substitution,
  imports and contextual REPLs; report scope errors at the relevant boundary.
- Infer arrow endpoints and propagate expected extension types, restrict dependent
  contexts correctly, and show the residual tope when a boundary fails.
- Inspect and print shapes, extensions, cells, selected categorical
  interfaces and any bridge used by elaboration. Generated source must keep
  the same bindings and assumptions.
- Add cubical path rewriting inside cells, boundary simplification and
  categorical calculation using explicit Segal/functor evidence. Every
  tactic still produces instruction-kernel derivations. No tactic invents
  composition or a coherence filler without the required hypotheses.

At the kernel boundary, coordinate kinds must survive the ABI, codec,
substitution, restriction, rollback, caches and readback. Review mixed
composition and conversion cases as well as shape entailment. Existing
endpoint-face substitution is not a solver for diagonals or inequalities.
Keep directed shape decisions in trusted instructions with a precise
decision procedure or checked certificates, and derivation search in the
untrusted driver. Resource exhaustion must reject rather than prove a tope.

## Theories and mathematical milestones

The [core-theories contract](../high-level-abstractions/core-theories.md)
continues to elaborate records. `law` fields remain proposition-valued;
proof-relevant higher cells belong in ordinary fields. `T(U)`, its chosen
ordinary category `T.cat`, and any future synthetic category of its models
are distinct constructions. For supported ordinary theories, prove that
synthetic arrows agree with the intended generated `T.Hom`, respecting
parameters, variance and universes. For higher-model pilots outside the
generator's supported fragment, use explicitly defined coherent morphism
records and prove the comparison with those. Free and initial objects still
require their universal proofs for those morphisms; an H1 fold does not
supply them.

Start higher-model bridges with pointed spaces and their explicitly defined
point-preserving maps, then pointed loop structures and their preservation
squares. The current generator rejects these untruncated carriers. These
pilots exercise proof-relevant fields before attempting a general
generator. Dropping `set` from an ordinary monoid and retaining only unit
and associativity paths does not define a fully coherent higher monoid.
Higher algebra needs an explicit Segal, operadic or higher Lawvere-theory
presentation and a justified morphism construction.

All ST packages are proposed and unimplemented. Dependencies below are
mathematical gates, not a schedule to interrupt the runtime track.

| ID | Deliverable and acceptance target | Dependencies |
| --- | --- | --- |
| ST0 | Specify ordinary/directed contexts, shape algebra, mixed rules and explicit embeddings; audit setness, universes and assumption scope. Review the model and preservation obligations before trusting a combined implementation; state any unproved claims | Current G0/H1 contracts; no change to them |
| ST1 | Shared `x ->[C] y` syntax on ordinary precategories, with explicit resolution, printing and rejected ambiguous uses; coordinate its precedence with composition | L2.12/L3.4 interfaces; independent of ST2 |
| ST2 | Separate directed coordinates, topes, extensions and cells through kernel instructions and frontend; checked interval/triangle examples and negative boundary/scope cases; mixed-rule and old-fragment preservation evidence | ST0 gate; a reviewed operational account for the admitted fragment |
| ST3 | Library definitions of arrows, triangles, Segal and Rezk conditions; derive identities, composition, associativity and functoriality. Develop covariant families and dependent Yoneda without requiring a classifier of all spaces | ST2; reviewed rules sufficient for the stated theorems |
| ST4 | Construct a directed `Spaces` classifier with the required covariance and directed univalence, proving its simplicial, Segal and Rezk properties; build separately checked bridges for ordinary categories and selected theory models, starting with pointed spaces | ST3; additional universe/modal rules only after their own model and computation review; L3.4 and relevant theory interfaces for bridges |
| ST5 | Coherent diagrams of spaces over categories with relations; presheaves, Yoneda embedding and selected adjunction/Kan-extension or limit/colimit constructions, each with explicit size and existence hypotheses | ST3/ST4 as used; any necessary additional type formers and modal rules |
| ST6 | A universe/category of higher categories, the comparison with UA6's model-category construction, and properly presented higher algebra | Further reviewed foundations beyond minimal Segal types; ordinary UA milestones for their comparison |

ST3 can establish useful synthetic category theory without directed
univalence. ST4 groups related goals rather than claiming that every bridge
needs the full classifier. Presheaf and higher-category research may need
more than the first shape fragment; dependency names do not assert those
constructions follow from the minimal kernel extension alone.

The early payoff is deriving coherent composition from the Segal condition
and functoriality from functions between the resulting types. A useful
next test is a diagram of spaces on `0 < 1 < 2`: its three arrows include
a specified comparison of the direct map with the composite. A graph-only
diagram records three unrelated maps. The latter remains the scope of
existing graph-shaped type limits/colimits; general coherent indexing and
the existence of its colimits require additional work.

The [category roadmap](../high-level-abstractions/categories.md) keeps
L3.4–L3.6's ordinary packages. The
[universal-algebra roadmap](../mathematics/universal-algebra.md) keeps
UA0–UA6, including UA5's ordinary pushout in `Clone.cat` and UA6's explicit
equivalence with a shared-carrier model category. A later universal
pullback property in a synthetic category of categories requires a proved
comparison with the coherent pullback; it is not a reinterpretation of the
existing statement.

The [homological-algebra roadmap](../mathematics/homological-algebra.md)
likewise retains its algebraic and cubical starting points. The expression
`H^n(X; G) = ||X -> K(G, n)||_0` does not require a directed extension.
Coherent naturality, diagram categories and later derived/stable categories
are additional targets, with their own constructions and prerequisites.

## Acceptance evidence

For each kernel slice, pin the baseline revision and its assumptions. Replay
the old instruction derivations and source checks, comparing elaborated
terms, assumptions and universe scopes; retain computation/conversion
probes and expected failures. Include quotients, powersets, h-level closure,
theory morphisms and optional classical modules in the preservation audit.
Check both command-line and browser inspection, including mixed contexts.

New negative cases must reject coordinate-sort mismatches, invalid topes,
incompatible boundaries, unrestricted reversal of directed arrows or
arbitrary horn filling, generic directed composition without the required
Segal evidence, covariance inferred only from discrete fibers, and
accidental widening of ordinary universe binders. Review the
critical pairs and canonicity obligations introduced by each interaction.
Do not label source proposals as checked examples in the reference.

If a prototype precedes completion of these gates, keep it explicitly
experimental with extension provenance on results and no default migration
of ordinary modules. Such isolation is operational containment, not a
soundness or conservativity proof. Release requires the specified semantic
and computational review in addition to tests.

## Research basis and limits

These works motivate different parts of the design, not a single ready-made
extension of Cubist's kernel:

- [Riehl–Shulman, *A type theory for synthetic infinity-categories*](https://arxiv.org/abs/1705.07442):
  shapes, extension types, Segal/Rezk types and dependent Yoneda.
- [Weaver–Licata, *A Constructive Model of Directed Univalence in Bicubical Sets*](https://dlicata.wescreates.wesleyan.edu/pubs/wl20bicubical/wl20bicubical.pdf),
  and [Weaver's thesis](https://mzweav.github.io/pdfs/thesis.pdf):
  computational directed-type-theory guidance. The thesis's directed
  `cooltt` prototype uses a Cartesian cubical core; its implementation
  does not supply Cubist's De Morgan/H1 combination or a completed
  directed-univalent universe implementation. The model paper is by
  Weaver and Licata; the broader computational lineage also includes Harper.
- [Rzk](https://arxiv.org/abs/2607.12207): a working shape/extension interface
  and synthetic category theory reference, not evidence for the reductions
  of this proposed cubical implementation.
- [Gratzer–Weinberger–Buchholtz, *Directed univalence in simplicial homotopy type theory*](https://arxiv.org/abs/2407.09146):
  directed universes and modalities. Its triangulated ambient geometry uses
  a bounded distributive lattice; its axiomatic theory does not satisfy
  canonicity. A computational account is a further design obligation.
- [Cavallo–Riehl–Sattler, *Directed univalence for simplicial objects in an ∞-topos*](https://arxiv.org/abs/2607.02420):
  semantic foundations for directed univalence, not kernel computation rules.
- [Gratzer–Weinberger–Buchholtz, *The Yoneda embedding in simplicial type theory*](https://arxiv.org/abs/2501.13229)
  and [their construction of the category of categories](https://arxiv.org/abs/2602.02218):
  references for the later presheaf and higher-category targets. Their
  additional foundations must be accounted for before claiming those
  targets from ST2/ST3.
