# Galois development: resumption checkpoint

Updated 2026-09-20 after resuming mathematical development on main.
The earlier paused checkpoint is commit
[`5f34197`](https://github.com/KanHarI/cubist-math/commit/5f34197).
There is no unfinished mathematical source file or partial proof to recover.

The current increment adds `quotient_descent`, `group_quotient_maps` and
`kernel_quotient_image` on top of the coset checkpoint `1e137e6`. Maps constant
on classes descend uniquely into sets, without representative choice. For
homomorphisms this yields the carrier equivalence `G/ker(h) ≃ im(h)`, equality
of those carriers in U1 by univalence, and setness of the kernel quotient.
The next step is the universe-polymorphic group interface and quotient group
operations, followed by bundling this equivalence as a group isomorphism.

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

All module names below refer to `web/proofs/<name>.cubist` and are exposed in
the website proof selector.

| Area | Modules and useful entry points |
| --- | --- |
| Structure identity | `groups`, `group_identity`, `group_univalence`, `structured_sets`, `algebraic_fields`, `field_extensions`: bundled groups, fields and extensions, with isomorphism/equality equivalences |
| Automorphisms as loops | `galois_paths`, `f4_galois`, `f4_galois_group`: transport actions, composition and inversion; `f4_galois_is_cyclic_two`, `f4_galois_group_equality` |
| Group algebra and maps | `group_operations`, `group_homomorphisms`: inverses, cancellation, conjugation; `GroupHom`, preservation of unit and inverse derived from multiplication preservation |
| Subgroups | `subgroups`, `subgroup_constructions`, `normal_subgroups`: inclusion orders, inverse images, small intersections, normal kernels, conjugation and transport |
| Subgroups as groups | `subgroup_carriers`: `subgroup_as_group`, injective `subgroup_inclusion`, `subgroup_factor`, its triangle and uniqueness |
| Images of homomorphisms | `subgroup_images`: image closure, `subgroup_image_preimage_adjunction`, covariance, `group_image_factor_triangle`, `group_image_factor_surjective`; identity/trivial image equalities |
| Cosets and quotient paths | `group_cosets`: `same_coset_equivalence`, `normal_coset_multiply`, `normal_coset_inverse`, `right_coset_compatibility_implies_normal`, `kernel_coset_equal_images`, `kernel_coset_of_equal_images`, `normal_coset_product_path` |
| Quotient descent | `quotient_descent`: `quotient_induction_prop`, `quotient_rec`, `quotient_rec_beta`, `quotient_maps_ext`, `quotient_rec_unique`; no univalence needed |
| Descent of homomorphisms | `group_quotient_maps`: `group_quotient_map`, its beta/unique/unit/multiply laws, `quotient_factor_kills_subgroup` |
| Kernel quotient and image | `kernel_quotient_image`: `kernel_quotient_image_equiv`, both inverse laws, `kernel_quotient_image_equality`, `kernel_quotient_is_set`; a carrier equivalence, not yet a bundled quotient `GroupIso` |
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

The concrete F4 correspondence is:

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
| Quotient recursor and its computation/uniqueness, homomorphism descent | Truncation and function extensionality; exact subsets audited in `tests/quotient-descent.test.mjs` |
| Kernel quotient/image equivalence and equality; quotient setness | Truncation, function extensionality and univalence; no LEM or choice |

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

## Validation and repaired integration failures

Latest quotient increment: **37 declarations** across the three new modules
check, and all seven targeted regressions pass. Final full `npm test`:
**236 passed, zero failures** (460.7 seconds). Four new browser inspections
pass with certified folding and definition links; all four static-site smoke
checks pass. All **244 sources** pass formatting. No production kernel or
axiom declaration changed in this increment.

Previous increment: all 22 coset declarations check; six focused regressions
pass, including exact dependencies, certified folding, rejection of missing
normality evidence, representative extraction and silent U1-to-U0 lowering.
The combined workbench/coset regression run passes all 20 tests.
Final full `npm test`: **229 passed, zero failures** (459.6 seconds).
Three new coset browser inspections pass with verified folding and links;
all four static-site smoke checks pass. All **241 sources** pass formatting.
The native reference comparison passes all 9,606 records, and repeating
the complete proof export produces identical artifacts.

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

[Failing CI run](https://github.com/KanHarI/cubist-math/actions/runs/35511108966).
Both failures were reproduced and repaired during resumption:

- WNat's helper was seeding an obsolete private normalization-cache key.
  It now passes the checked, unfolded `ap` definition explicitly. Its complete
  1,910-instruction export replays with only function extensionality.
- The current native reference contains 9,606 records, independently verified
  by Rust with zero skips before updating the fixture. Universe transport in
  the generated univalence proof is derived by J, and the copied Rust baseline
  receives the documented Unit beta correction with `--correct-unit-beta`.
  Historical verification remains in `tests/reference_verification.json`.
- `make proof-export` now succeeds. Generated construction sources use the
  formatter during export so regenerated sources retain canonical formatting.

The website publication workflow is a separate job; its successful publication
was not used as evidence for these repairs. No production kernel rule changed.

## Recommended restart sequence

1. Read this checkpoint and check for later commits or CI fixes.
2. Reuse the checked coset relation `N(x⁻¹ y)`, equivalence laws, and normal
   multiplication/inverse compatibility in `group_cosets`.
3. Resolve the quotient universe plan, then construct quotient group operations.
   Reuse `quotient_rec` and `group_quotient_map_unique` for their universal
   property. Bundle the checked `kernel_quotient_image_equiv` as a group
   isomorphism after proving compatibility with the quotient operations.
4. Add a non-normal subgroup example and a quotient example that catches a
   missing normality hypothesis. The abelian F4 example cannot test that issue.
5. Begin explicit finite linear algebra: vector spaces, supplied finite bases,
   dimension invariance, degree and the tower law. Keep basis data distinct
   from mere finite dimensionality. Continue the remaining roadmap stages.

The immediate design constraint is that our predicate-based `SetQuotient`
lives in U1 even for U0 input, while `Group` currently bundles U0 carriers.
Kernel quotients now have a proved small presentation by their images, and
are sets by transport along the univalence equality. This does not solve the
universe problem for arbitrary normal-subgroup quotients, nor does it change
the universe of the predicate quotient itself. Evaluate a universe-polymorphic group
interface, a justified small quotient construction, or a small presentation
under stated hypotheses. Do not silently resize or introduce an incompatible
second notion of group. Finite decidable quotient presentations do not solve
the general universe problem.

A resumption probe also exposed a language constraint: an ordinary definition
`Group(U : Universe) = exists A : U, ...` is assigned the broad `Universe`
sort. Applying it to U0 does not by itself recover a judgement in U1, and
`typed(U1, Group(U0))` cannot justify lowering that sort. Plan universe-level
specialization/rechecking for this interface, rather than asserting a narrower
sort or duplicating the library as `HigherGroup`. The existing axiom
specializations already rebuild checked binders for concrete universes; this
is distinct from merely substituting a universe into a broadly typed term.

An isolated cubical experiment is authorized on branch `experiment/cubical-hott`
in `/private/tmp/thth-cubical-hott`. Main remains the Id/J kernel with axiomatic
univalence and native suspension. The experiment is not a prerequisite for
Galois and must not be silently merged into it. Complex analysis remains paused.
The user has also authorized a new C cubical kernel after a stable reference
milestone, emphasizing readability alongside performance. The experiment agent
owns that work, including rule organization, documentation, cross-checks and
benchmarks. It is not part of this main-branch algebra checkpoint.

## Commands and implementation details worth retaining

Run selected modules and their imports during development:

```sh
npm test -- subgroup_images normal_subgroups
npm test -- group_cosets tests/group-cosets.test.mjs
npm test -- quotient_descent group_quotient_maps kernel_quotient_image
npm test -- tests/quotient-descent.test.mjs
npm test -- f4_galois_correspondence
npm test -- tests/subgroup-images.test.mjs tests/normal-subgroups.test.mjs
npm test -- tests/galois-correspondence.test.mjs tests/galois-fixed.test.mjs
npm test -- tests/distinguished-extensions.test.mjs
node tools/format-mathscript.mjs web/proofs/your_module.cubist
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
