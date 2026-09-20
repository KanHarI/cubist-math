# Galois development: resumption checkpoint

Recorded 2026-09-20. Mathematical development is paused for later resumption.
The implementation checkpoint is commit
[`5f34197`](https://github.com/KanHarI/thth-c/commit/5f34197).
There is no unfinished mathematical source file or partial proof to recover.

Read this file first when resuming, then the [full roadmap](galois-roadmap.md)
and the [mathematical development guide](galois.md). The roadmap remains the
full target; the concrete F4 example does not replace it.

## What is complete, and what is not

The constructions listed in **stage 1** and its completion criterion are
checked: subobjects, normal subgroups, generated subfields, intersections,
composita, and the order-reversing fixed-field/fixing-subgroup connection.
There is also a full equivalence for **decidable** subobjects of F4/F2.

The general fundamental theorem of Galois theory is **not proved**. We have
not developed extension degree and the tower law, the required general
polynomial and algebraic-extension theory, separability/normality of field
extensions, Artin's fixed-field theorem, or the finite degree/index and
quotient formulas. Algebraic closures and the infinite correspondence with
Krull topology are later, separate milestones. Stage 1 being complete is not
an estimate that one ninth of the total effort is complete.

The term `AlgebraicField` names the existing unordered field interface. It
does not assert that an extension is algebraic. Likewise the normal subgroup
theorems do not establish normality of field extensions.

## Results and where to resume reading

All module names below refer to `web/proofs/<name>.proof` and are exposed in
the website proof selector.

| Area | Modules and useful entry points |
| --- | --- |
| Structure identity | `groups`, `group_identity`, `group_univalence`, `structured_sets`, `algebraic_fields`, `field_extensions`: bundled groups, fields and extensions, with isomorphism/equality equivalences |
| Automorphisms as loops | `galois_paths`, `f4_galois`, `f4_galois_group`: transport actions, composition and inversion; `f4_galois_is_cyclic_two`, `f4_galois_group_equality` |
| Group algebra and maps | `group_operations`, `group_homomorphisms`: inverses, cancellation, conjugation; `GroupHom`, preservation of unit and inverse derived from multiplication preservation |
| Subgroups | `subgroups`, `subgroup_constructions`, `normal_subgroups`: inclusion orders, inverse images, small intersections, normal kernels, conjugation and transport |
| Subgroups as groups | `subgroup_carriers`: `subgroup_as_group`, injective `subgroup_inclusion`, `subgroup_factor`, its triangle and uniqueness |
| Images of homomorphisms | `subgroup_images`: image closure, `subgroup_image_preimage_adjunction`, covariance, `group_image_factor_triangle`, `group_image_factor_surjective`; identity/trivial image equalities |
| Subfields and embeddings | `subfields`, `subfield_carriers`, `field_embeddings`, `intermediate_fields`, `intermediate_towers`: realized fields, injective inclusions and commuting towers |
| Field images and factorization | `subfield_preimages`, `subfield_images`, `subfield_image_orders`, `field_embedding_factorization`, `field_embedding_image`, `f4_embedding_images`: adjunction, unique factorization and isomorphism onto the image |
| Generated subfields | `subfield_generation_steps`, `generated_subfields`, `subfield_composita`, `subfield_transport`, `compositum_embeddings`, `f4_generated_subfields`: finite derivations, leastness, compositum laws and change of ambient field |
| Embedded composita | `embedded_composita`, `f4_embedded_composita`: separate embeddings into a common field, compatibility over the base, both inclusion triangles and leastness |
| Distinguished classes | `distinguished_extensions`: Lang's three clauses, third derived from first two, invariance by transport; no finite/algebraic/separable instances proved yet |
| General Galois connection | `galois_fixed_points`, `galois_fixed_fields`, `galois_fixing_subgroups`, `order_maps`, `galois_orders`: actual assignments, order reversal and idempotent closures |
| F4 subobject recovery | `f4_fixed_field`, `f4_intermediate_fields`, `f4_galois_connection`: fixed field equals embedded F2, classification and recovery with explicit membership decisions |
| F4 normal subgroups | `f4_normal_subgroups`: commutativity transported from `CyclicTwo`; every subgroup is normal, without deciding membership |
| Decidable correspondence | `finite_decisions`, `decidable_subobjects`, `f4_galois_correspondence`: membership algorithms, uniqueness of decision data, inverse maps and order reversal |
| General coherent inverses | `equivalence_from_inverse`: `equiv_from_inverse` converts two inverse homotopies into the existing full half-adjoint `Equiv`, for arbitrary types/universes, by path induction alone |

The latest principal result is:

```text
f4_galois_correspondence : Equiv(
  U1,
  DecidableSubgroup(F4GaloisGroup),
  DecidableIntermediateField(F2, F4OverF2)
)
```

Its forward map is `f4_decidable_fixed`; its inverse is
`f4_decidable_fixing`. The proofs `f4_decidable_fixing_fixed` and
`f4_decidable_fixed_fixing` are equalities of complete bundles, including
decision data. `f4_decidable_fixed_antitone` and
`f4_decidable_fixing_antitone` establish order reversal.

This is not a correspondence for arbitrary undecidable subobjects. The earlier
recovery lemmas need only the decision at Frobenius or alpha, respectively;
the packaged types provide pointwise membership decisions. Finite search
constructs decisions for their images. Finiteness of the ambient carrier does
not itself decide arbitrary proposition-valued membership.

## Assumptions to preserve

| Result family | Dependencies |
| --- | --- |
| Group algebra, subgroup carriers/inclusions, factor construction | None |
| Equality and uniqueness of homomorphism factors | Function extensionality |
| `equiv_from_inverse`, finite universal search | None |
| Uniqueness of decisions for propositions | Function extensionality |
| F4 fixed-membership decision via automorphism classification | Function extensionality |
| Packaged F4 correspondence | Function extensionality and univalence |
| Group image construction, adjunction and surjectivity | Existing propositional-truncation axioms |
| Group image factorization triangle | Truncation and function extensionality |
| Image subgroup equalities | Truncation, function extensionality and univalence |

The new correspondence and image modules use neither LEM nor choice. Their
tests assert exact kernel axiom dependencies, not just successful checking.
No new kernel rule was needed for this batch.

Group-image membership truncates preimages because a homomorphism need not
be injective. Field-embedding images can retain actual preimages because
those fibers are already propositions. Do not conflate these constructions,
or turn mere surjectivity into a chosen inverse.

The foundational univalence refactor is complete: `idtoequiv` is derived;
one axiom asserts it is an equivalence; `ua` and its beta/eta laws are derived.
Use the same universe-polymorphic `IsEquiv` throughout. Do not revive a
separate `HigherIsEquiv`. See [univalence.md](univalence.md).

## Validation and unresolved integration failures

Local validation before this pause:

- Full `npm test`: **217 passed**, after the decidable-correspondence batch.
- Subsequent subgroup-image module check: **19 declarations checked**.
- Subsequent image regression plus proof-library selection check: **7 passed**.
- Five browser checks for subgroup carriers, adjointification, finite
  decisions and F4 correspondence; two more for subgroup images: all passed,
  including verified folded kernel types and links.
- Formatter check: **240 sources clean**; `git diff --check` clean.
- Static-site build and browser smoke passed for landing/mobile layout,
  repository links, Euclid, the F4 correspondence and kernel workbench.

Do not describe the 217-test run as covering the later image tests: the latter
were added and checked separately. The CI run for the pushed checkpoint is
separate from these local results.

The deployment agent subsequently reported **two failures in the existing
C-engine CI** for `5f34197`:

1. `tools/check_reference.py`: the frozen upstream reference comparison differs
   after the univalence changes.
2. `make proof-export`: `tools/proofs/wnat_equiv.mjs`, through
   `tools/proofs/paths.mjs` (`J`/naturality/commutation), reaches
   `Builder.coerce` with `Conversion types differ`.

[Failing CI run](https://github.com/KanHarI/thth-c/actions/runs/35511108966).
These were reported after the successful local checks and are **unresolved at
this checkpoint**. Inspect the run logs and reproduce the individual failure
before changing anything. Reconcile the intended univalence migration with
the independent reference check; do not blindly replace the frozen reference
or weaken equality/export checks. The website publication workflow is a
different job; successful publication does not resolve these failures.

## Recommended restart sequence

1. Read this checkpoint and check for later commits or CI fixes. Reconcile the
   exporter/reference failures above before treating the integration baseline
   as green.
2. Develop the coset relation `N(x⁻¹ y)` and its equivalence laws. For normal N,
   prove compatibility with multiplication before descending operations.
3. Resolve the quotient universe plan, then construct quotient groups with
   their elimination/universal property for homomorphisms annihilating N.
   Reuse the image factorization for the first isomorphism theorem.
4. Add a non-normal subgroup example and a quotient example that catches a
   missing normality hypothesis. The abelian F4 example cannot test that issue.
5. Begin explicit finite linear algebra: vector spaces, supplied finite bases,
   dimension invariance, degree and the tower law. Keep basis data distinct
   from mere finite dimensionality. Continue the remaining roadmap stages.

The immediate design constraint is that our predicate-based `SetQuotient`
lives in U1 even for U0 input, while `Group` currently bundles U0 carriers.
No solution has been implemented. Evaluate a universe-polymorphic group
interface, a justified small quotient construction, or a small presentation
under stated hypotheses. Do not silently resize or introduce an incompatible
second notion of group. Finite decidable quotient presentations do not solve
the general universe problem.

Cubical foundations were discussed, but **no migration was authorized or
implemented**. Current code remains the Id/J kernel with axiomatic univalence
and native suspension. A cubical experiment is a separate possible project,
not a prerequisite for resuming Galois. Complex analysis also remains paused.

## Commands and implementation details worth retaining

Run selected modules and their imports during development:

```sh
npm test -- subgroup_images normal_subgroups
npm test -- f4_galois_correspondence
npm test -- tests/subgroup-images.test.mjs tests/normal-subgroups.test.mjs
npm test -- tests/galois-correspondence.test.mjs tests/galois-fixed.test.mjs
npm test -- tests/distinguished-extensions.test.mjs
node tools/format-mathscript.mjs web/proofs/your_module.proof
node tools/format-mathscript.mjs --check
git diff --check
```

Run `npm test` once the mathematical batch is complete. For browser/static
validation, use `npm run build:site` followed by `npm run test:site` when web
integration changes. Do not rerun the full library after every small proof edit.

- Data constructors whose projections must compute should be `def`; named
  theorems are opaque. Keep an outer record pair visible and put proof
  extraction into helper theorems where needed.
- `typed(T, term)` can recover a dependent function descriptor after a
  projection or eliminator. A term may check mathematically while the
  elaborator otherwise reports it is not a function. Use explicit carriers
  `x =[T] y` where equality inference loses the intended folded type.
- `group_hom_compose` and `field_embedding_compose` use traversal order:
  first the first map, then the second.
- Use the established right-associated tuple syntax `(a, b, c)` and formatter;
  no angle-bracket tuple syntax was introduced.
- Register new proof modules in `web/mathscript/modules.mjs` and
  `web/proof-library.mjs`; add focused regressions in `tools/test-selection.mjs`.
  Preserve verified folding and the exact axiom display in the inspector.
- The folded-view coercion already has a checked type-normalization fallback
  in `web/mathscript/kernel-folding.mjs`. Do not replace verified folding with
  source-shaped text that has not been checked by the kernel.

Pushes to `main` now rebuild/publish the website through GitHub Actions, per
the user's revised deployment preference. Deployment is separate from the
mathematics; see [deployment.md](deployment.md).
