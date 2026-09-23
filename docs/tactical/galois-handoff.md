# Galois development: resumption checkpoint

Updated 2026-09-23. Continue from this file and the
[full roadmap](../roadmaps/galois-roadmap.md). All canonical proofs now use the cubical C
kernel and `.cubist` sources. The old Id/J engine, its proof exporters and
its reference-comparison commands are retired; older checkpoints describe
historical validation, not the current development workflow.

## Active checkpoint: 2026-09-23

Artin's theorem is now checked in `artin_degree`: for a merely finite subgroup
H of extension loops, `[E:E^H] = |H|`. `artin_equivariance` proves the
evaluation coefficients are H-fixed, giving spanning over E^H; the same
evaluation points are independent over E^H. `artin_embedding_bound` excludes
more than n distinct embeddings over a field spanned by n elements.
`artin_classification` uses that bound to prove `Aut_{E^H}(E) = H` as an
equality of bundled subgroups. The matrix entries and automorphism actions
are transport around extension paths; composition and inverse cancellation
are checked at the loop level. No new axiom or kernel rule was added.

The core finite correspondence is checked in `galois_intermediate_roundtrip`.
For a finite normal separable E/K and a supplied algebraically closed T with
an embedding E → T, `galois_normal_target` proves
`|Aut_M(E)| = [E:M]` for every intermediate M. A degree-one inclusion argument
then proves `Fix(Aut_M(E)) = M`. `finite_decidable_subtypes` derives the
cardinality of every proposition-valued subgroup from the finite ambient
automorphism group, so the two roundtrips assemble into
`Equiv(U1, GaloisSubgroup(K,E), IntermediateField(K,E))` without a separate
finiteness argument for each H. Existing order proofs show both maps reverse
inclusion. The full automorphism group fixes exactly the embedded base field,
and `finite_galois_cardinality_tower_law` checks
`|G| = |Aut_M(E)| [M:K]`. Exact axioms for the correspondence are LEM(U0), Truncate(U0/U1),
TruncateElim(U0/U1), TruncateIntro(U0), and TruncateProp(U0); no Choice axiom.

The new focused regressions check Artin degree, classification, both
roundtrips, and the exact axiom families. Older increment sections below are
historical and may list work that has since been completed.
Full validation: `npm test` passes 292 tests; the canonical corpus checks
3,766 concrete declarations and 44 universe templates with zero failures,
blocked declarations, or optimization candidates.

Remaining finite milestones, in suggested dependency order:

1. Complete derivative/repeated-root criteria and the polynomial
   characterization of normality. Develop finite splitting-target embedding
   extension/counting, so the finite route needs no constructed algebraic closure.
2. Connect finite normal separable extensions with their splitting-field and
   automorphism-count characterizations.
3. Present finite coset indices in a small type, prove the index formula
   `[M:K] = [G:H]`, and make join/meet exchange explicit. Package the general
   loop-group identification and promote the correspondence to the bundled
   lattice equality required by the roadmap, using structure identity.
4. Prove the normal-subgroup criterion and restriction quotient isomorphism,
   reusing the checked quotient universal property and first isomorphism theorem.
5. Supply Lang's distinguished-class instances for finite and finite separable
   extensions, including compositum base change.
6. Validate a proper intermediate-field example, negative statements, exact
   assumptions, and the full corpus. Reuse univalence and the existing
   automorphism/loop interpretation where applicable.

The complete finite fundamental theorem still needs index and normal quotient
statements. Infinite extensions,
algebraic-closure existence, and infinite Galois theory remain out of scope.
No new axioms or mathematical kernel rules are planned.

## Scope decision: finite theory first

The user explicitly deferred infinite extensions on 2026-09-22. Initial completion
means finite Galois theory; infinite embedding extension, algebraic/separable
closure construction, profinite topology, and infinite correspondence are out of
scope. See the roadmap's deferred section. Do not treat them as initial blockers.

## Previous increment: finite algebraic extensions and embedding counts

The four requested finite milestones now have checked source proofs. See
[polynomial-algebra.md](polynomial-algebra.md) for statements, representation,
universe assumptions, and the boundaries of the results.

- Finite spanning subfamily bases, finite subspace bases, converse tower finiteness.
- Formal polynomials, division/uniqueness, extension root bounds, Bézout,
  irreducible factors, root adjunction, and residue-field degree.
- Canonical monic minimal polynomials; finite ⇔ finitely generated algebraic
  extensions; extension of embeddings into an explicitly algebraically closed target.
- Finite splitting-field existence with generation, embedding normality,
  separability under intermediate base change, and the general finite separable
  embedding count by extension degree.

The final count is `embedding_counts.finite_separable_embedding_count`.
It uses a tower of root adjunctions obtained from finite basis generators,
not a primitive-element assumption. `embedding_tower_type_equality` and
`adjoined_embeddings_are_roots` transport counts along univalent equalities.
`f4_formal_polynomial` connects the new formal polynomial API to the existing
F4 roots.

Validation: the full bounded diagnostic audit checks **3,572 declarations and
44 universe templates, with zero failures** (347 imported modules). The former
`embedding_root_roundtrip` conversion-budget failure is fixed by selectively
unfolding the two root/embedding maps and their pair projections, including
`sigma_first` and `sigma_second`. The reproducer now checks that declaration in
about 13 ms; timings vary by machine and import context. A regression test
collects inspector references and caps this declaration at 10 million steps,
below the 100 million steps previously exhausted.

Final validation: `npm test` passes all **282 tests**; the formatter checks
348 sources with no changes needed; the browser module/topic registry tests
pass; `git diff --check` is clean. No kernel or language changes were needed.

Performance follow-up: `embedding_counts.finite_separable_count_step` now checks
in **476–478 ms** in the standalone and broader one-second benchmarks (Apple M3
Pro). The broader run covers 1,858 entries: **1,823 checked, 35 templates, zero
optimization candidates, blocked declarations, or failures**. These are focused
Galois graphs, not a claim that every declaration in the full corpus is below
100 ms.

The proof now uses `embedding_tower_degree_count` to check the generic tower
transport once (about 5 ms). It keeps the lower degree in its named
`adjoined_extension` form, then selectively unfolds that alias and
`AdjoinedEmbeddings` at the conversion boundaries. No kernel changes or new
assumptions are involved. All four algebraic-extension tests pass, including
a new 10-million-step budget regression for the count step and its helper with
inspector references enabled. Formatting and whitespace checks pass.

Since this increment, Artin's fixed-field degree theorem and the core general
correspondence have been checked. See the [active checkpoint](#active-checkpoint-2026-09-23)
for their hypotheses and the remaining finite work, including splitting-target
embedding counts, derivative criteria, and distinguished-class instances.

## Previous increment: finite dimension and extension degree

All three requested milestones now check: finite dimension invariance,
basis-independent extension degree, and the finite tower law. See
[the proof guide](finite-dimension.md) for statements and the elimination proof.

The new modules are `linear_constructions`, `function_linear_isos`,
`scalar_restriction`, `coordinate_splitting`, `coordinate_elimination`,
`finite_dimension`, `dimension`, and `extension_degree`. The headline results
are `finite_dimension_invariance`, `extension_degree_unique`,
`finite_extension_tower`, and `tower_law`. The product basis is constructed
from actual coordinate isomorphisms. The tower triangle transports along an
equality of embeddings, and `extension_degree_iso` uses univalent equality
of complete extensions. No new axioms or kernel changes were needed.

Dimension invariance uses LEM(U0) to select a nonzero coordinate of a finite
vector; no choice is used. `FiniteDimensional(K,V)` is a proposition proved
from uniqueness of the natural number and truncated basis evidence.
`extension_degree` needs this finiteness evidence and is independent of it.
Infinite extensions are not assigned zero. The identity extension has degree
one, and zero degree is ruled out.

The subsequent algebraic-extension increment supplies the converse tower criterion,
finite subspace bases, and indexed subfamily extraction from spanning families.

## Previous increment: the general basis theorem

Checked modules added:

| Module | Contribution |
| --- | --- |
| `permutation_groups` | Bijection group on a set, group laws, point stabilizers, conjugation action |
| `non_normal_subgroup` | S3 has six elements; a point stabilizer is not normal, with an explicit conjugation counterexample |
| `vector_spaces` | Bundled abelian additive group with scalar action and the four scalar laws |
| `field_vector_spaces` | Additive field group; a field embedding K -> L makes L a K-vector space; extension instance |
| `linear_maps` | Bundled linear maps, composition, extensionality, linear isomorphisms, coherent carrier equivalences and univalence |
| `finite_bases` | Pointwise function spaces, K^n, explicit finite bases, coordinate roundtrips/uniqueness, one-element scalar basis, basis transport |
| `linear_span` | Finite combinations, proposition-valued span, empty independence, exclusion of zero, and `VectorBasis` for arbitrary subset bases |
| `finite_combinations` | Concatenation and scaling laws for finite combinations; scalar action preserves zero |
| `vector_subspaces`, `span_subspace` | Span is the least subspace containing its generators; idempotence as a univalent predicate equality |
| `predicate_chains` | U1-indexed unions, chain-to-directed conversion, and finite covers in directed unions |
| `independent_unions`, `independent_order` | Independent chain unions, a univalent partial order of complete subset records, and chain least upper bounds |

The permutation/group results, vector-space constructions and finite-basis
results use no axioms. Span membership uses existing small propositional
truncation; U1-indexed unions use the existing `Truncate(U1)` interface.
The new basis-existence theorem adds explicit uses of the existing
`Choice(U1)` and `LEM(U0)` schemas, not new axioms.

The user specifically requests **general basis existence**, with **Zorn
derived from the existing axiom of choice**, not a new Zorn axiom. See
[basis-theorem.md](basis-theorem.md) for the exact interfaces, mathematical
proof route and outstanding formal lemmas. **General basis existence is now
checked** as `vector_basis_existence.vector_space_has_basis`. It uses the
proved chain-complete form of Zorn (`zorn_chain_complete`) via a checked
Bourbaki–Witt tower argument. Independent extension and deletion of arbitrary
finite summands are also checked. The existing universe-lowering U1
truncation is used explicitly; no axiom or kernel interface changed.
The later finite spanning increment connects the finite-coordinate and
indexed independent-subset basis interfaces.

Alongside the mathematics, the inspector now separates axioms from local
context, including in the workbench. Annotated declarations show their
source conclusion first, with named parameters and hypotheses expandable;
the precise elaborated type remains in kernel details. Inferred declarations
also separate their conclusion from the parameter telescope. Displayed types
beta-reduce administrative motive applications, checked again by C, without
unfolding named definitions. Induction binders retain their source names,
lambda text includes the domain, and summaries wrap in the narrow panel.
Stored/raw views preserve the original type syntax.

## Previous increment: quotient universal property

The bundled quotient universal property is now checked. For a small group
G, a normal subgroup S, any H : GroupAt(U1), and a homomorphism
h : GroupHomAt(U1, group_lift(G), H) killing S, there is a unique
factor : GroupHomAt(U1, QuotientGroup(G,S,normal), H). Its composite with
`quotient_projection` equals h as a complete homomorphism record.

`quotient_group_universal.cubist` contains:

- `quotient_projection`, `quotient_projection_kills`;
- `quotient_descend_map`, its beta and arbitrary-coset multiplication laws;
- `quotient_descend_hom`, `quotient_descend_triangle`, `quotient_descend_unique`;
- `quotient_group_universal`, packaging existence and uniqueness;
- `quotient_projection_epimorphism`;
- `quotient_descend_agrees_with_map`, compatibility with the earlier small-target recursor.

`group_hom_universes.cubist` supplies `GroupHomAt(U)`, projections,
composition, identity, and homomorphism extensionality. The original
`GroupHom` / `GroupHomLaws` now specialize this family at U0. Extensionality
constructs a cubical dependent pair path, using the proposition-valued law
field; it does not postulate proof irrelevance. Templates are tested at
U0, U1, U2, and U3.

The universal property needs only `Truncate(U1)`, `TruncateIntro(U1)`,
`TruncateElim(U1)`, and `TruncateProp(U1)`. No LEM, choice, new axiom, or
kernel change was introduced. Regression checks that descending the
projection to its own (genuinely U1) quotient gives the identity homomorphism.

## Earlier increment: first isomorphism theorem

The general first group isomorphism theorem is checked:

```text
group_first_isomorphism(G, H, h) :
  GroupIsoAt(U1, KernelQuotientGroup(G, H, h),
    group_lift(ImageGroup(G, H, h)))
```

This is an isomorphism of bundled groups, including multiplication
preservation on arbitrary quotient elements. It reuses the previously
checked carrier equivalence and inverse maps without selecting preimages.
The quotient is represented in U1; its small image is explicitly repackaged
in U1. This is not a resizing argument.

| Module | Checked contribution |
| --- | --- |
| `group_universes` | `GroupAt(U)`, group laws, projections and `GroupIsoAt(U)` as universe schemas; the existing `Group` specializes this family at U0 |
| `quotient_sets` | General predicate-quotient setness via constant paths; dependent function setness via a pointwise square of paths |
| `quotient_operations` | Descent of binary operations, computation on classes, two- and three-variable propositional induction |
| `quotient_groups` | Multiplication, inversion, all group laws for arbitrary cosets, `QuotientGroup`, and `group_lift` |
| `group_first_isomorphism` | Multiplicativity of the existing quotient-to-image map and the bundled group isomorphism |

The generic group templates are checked at specialization. Regression tests
exercise U0, U1 and repackaging into U2. This does not claim a new primitive
universe-polymorphic term in the kernel.

## Constructivity and homotopy

No LEM, choice, new axiom, or kernel rule was added. Exact remaining axiom
families for the first isomorphism theorem are `Truncate`, `TruncateIntro`,
`TruncateElim`, and `TruncateProp`, specialized at U0 and U1. General quotient
setness only needs `Truncate`, `TruncateElim`, and `TruncateProp` at U1.
The construction of `QuotientGroup` additionally uses `TruncateIntro(U1)`.
The existing truncation interface itself retains its established universe
signature; this increment does not strengthen it.

Function extensionality and univalence are derived in the cubical kernel.
The existing `kernel_quotient_image_equality` identifies quotient and image
**carriers** via univalence. The new function-setness proof is an explicit
higher path (a square). Group laws are proposition-valued; arbitrary
representatives are never selected from truncation.

The structure identity equivalence for small `Group` remains available.
Its extension to `GroupAt(U1)` has not been proved: do not describe the new
large-group isomorphism as an equality of bundled groups yet. Carrier equality
alone is insufficient for that claim.

## Existing Galois development

Stage 1 of the roadmap has subgroups and subfields, normal kernels, subgroup
carriers, homomorphisms and images, generated subfields, intersections,
composita with specified embeddings, and Lang's distinguished-class interface.
Fixed fields and fixing subgroups form an order-reversing Galois connection.
Automorphisms are identified with loops of extension structures, acting by
transport. The F4/F2 automorphism group is identified with the cyclic group
of order two, and the decidable subobjects have a checked correspondence.

Useful modules: `galois_paths`, `galois_orders`, `f4_galois_correspondence`,
`distinguished_extensions`, `embedded_composita`, `field_embedding_image`,
`group_cosets`, `group_quotient_maps`, and `kernel_quotient_image`.
See [the development guide](galois.md) for the earlier constructions.

Finite spanning and degree interfaces, polynomial division and root adjunction,
finite algebraic extensions, splitting fields, separable embedding counts, and
Artin's fixed-field theorem are now checked. The core finite correspondence is
checked with a supplied algebraically closed target and embedding into it.
The full finite target still includes the index formula, normal-subgroup and
restriction quotient theorems, and the bundled lattice equality. Algebraic
closures and infinite correspondence are deferred. `AlgebraicField` is the
unordered field interface; its name does not assert that an extension is algebraic.

## Next work

Use the ordered list in the [active checkpoint](#active-checkpoint-2026-09-23).
Finite spanning-family reduction, subspace bases, converse tower finiteness,
and Artin's theorem have been completed. Larger-group structure identity is
still needed to turn the general loop-group isomorphism into equality of
bundled groups; the existing first isomorphism theorem already provides a
bundled `GroupIsoAt(U1, ...)`.

The quotient construction still starts from a small source group and small
subgroup predicates. Its universal-property target may be any group in U1.
No quotient universe lowering has been proved.

## Validation and workflow

Historical quotient batch validation: **255 tests passed**. The complete corpus checked
**2,537 concrete declarations and 44 universe templates**, with no failed,
blocked, or over-budget declarations at the regression deadline. The browser
landing regression passes, including the quotient universal-property page
and folded `QuotientGroup` / `GroupHomAt` names.

All 415 concrete declarations in the quotient universal-property import
graph passed the focused 100ms benchmark, with 35 templates counted
separately. The U0–U3 schema checks, quotient-as-target identity test,
small-homomorphism compatibility, and rejection of a missing killing
hypothesis pass. All four changed mathematical sources pass the formatter.
The previously known all-source formatter issues in `bouquet_actions`,
`bouquet_cover`, `bouquet_generation`, and `primes` were not changed here.

Selected checks for that quotient increment:

```sh
npm test -- quotient_group_universal group_first_isomorphism circle_group_identity
npm test -- tests/quotient-universal.test.mjs tests/quotient-groups.test.mjs tests/proof-library.test.mjs
node tests/landing.browser.mjs
node tools/format-mathscript.mjs --check
```

The focused regression checks the general theorem, identity/trivial
homomorphism specializations, the U2 group specialization, truncation-only
assumptions, and rejection of missing normality and silent universe lowering.
The browser regression checks the circle and group-univalence landing links
and folded kernel inspection. A new registry regression checks that every
bundled source import is permitted by the browser worker: the new
`group_universes` import initially exposed this missing-registration bug.

Run the whole library once at the end of a mathematical batch, not after
every edit. `npm test` also runs the current native-kernel regressions.
Check exact assumptions as well as successful type checking.

Use `with unfolding [left_coset] { ... }` when class-constructor conversion
would otherwise expand the entire quotient recursor. Check generic
constructors against abstract carriers before specializing to large terms
(`group_iso_object_at` follows this pattern). These are elaborator hints;
the kernel still verifies all conversions.

Register new modules in `web/mathscript/modules.mjs` and
`web/proof-library.mjs` when introducing imports, so the live website remains
usable during development. Source comments supply inspector documentation.
Pushes to main publish the website; deployment checks are separate from
mathematical validation.

For a concrete quotient target, prefer proving that the descended projection
is the identity by `quotient_projection_epimorphism` and the bundled triangle.
Inlining propositional induction into homomorphism extensionality caused
expensive conversion of the nested quotient. The epimorphism proof checks
under the 1,000,000-step diagnostic budget without new conversion hints.

Previous checkpoint benchmark: **662 checked declarations**, 35 templates,
no slow/failed/blocked entries at a 100ms limit for `linear_span` and
`non_normal_subgroup`. Regression checks include actual cubical computation
of transport along the one-dimensional coordinate equivalence, rejection of
a nonlinear constant map and a changed basis length, and axiom-free S3 laws.
The new statement browser regression verifies both reported inspector issues
and the S3 / scalar-basis proof pages. Final `npm test`: **262 tests passed**,
including **2,641 checked corpus declarations and 44 templates**, with no
failed, blocked, or over-budget entries at the regression deadline. Landing,
statement, and universe-specialization browser regressions pass.

Previous validation (2026-09-22): **265 tests passed**, including the complete
canonical corpus. The focused `span_subspace independent_order` benchmark
checks **579 declarations**, with 35 templates and no slow, failed, or blocked
entries at a 100ms limit. Regression examples exercise empty chains and an
actual U1-indexed family (`I = U0`), and confirm no Choice/LEM assumptions in
the new results. Inspector and statement browser regressions pass, including
`finite_combinations.linear_combination_scale` and workbench navigation.

Previous validation after basis existence (2026-09-22): **269 tests passed**,
including the complete corpus. The focused `vector_basis_existence` benchmark
checks **676 declarations** and 35 templates, with no failures, blocked
entries, or entries above 100ms. Browser regression verifies the new basis
page, its explicit Choice assumption, and the reformatted vector-space source.
All 264 proof files pass the formatter check. The formatter now distinguishes
an equality in an annotated type from an assignment and inserts a blank line
between top-level declarations. Existing sources were reformatted with
expanded-AST preservation checks; Linear Algebra has its own browsing topic.

Current validation after degree/tower development (2026-09-22): **273 tests
passed**, including the whole corpus. The focused `extension_degree`
benchmark checks **747 declarations** and **35 templates**, with no failures,
blocked entries, or entries above 100ms. All new modules are registered in
the proof selector and bundled-source registry. The negative regressions
reject selecting a basis from truncation and forgetting linearity or a tower
triangle. The browser regression checks the new dimension and tower-law
pages, and all 272 sources pass the formatter check.

Current focused commands:

```sh
npm test -- tests/dimension.test.mjs tests/linear-algebra.test.mjs
node tools/benchmark-cubical.mjs extension_degree --limit-ms=100
node tests/statement.browser.mjs
node tests/cubical-specialization.browser.mjs
```
