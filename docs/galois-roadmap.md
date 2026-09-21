# Requirements for a full Galois theory development

Status: resumed on main (2026-09-21). Start with the
[resumption checkpoint](galois-handoff.md), including validation results and
the current cubical kernel and validation commands. The listed stage-1 constructions
and its Galois-connection completion criterion are checked; stages 2–9 remain
requirements. Quotient group operations, the first group isomorphism theorem, and the bundled quotient universal property are now checked.
Checked results and their assumptions are described in
[Galois symmetries as loops](galois.md).

## Existing foundation and remaining scope

We have bundled fields, embeddings and extensions, field and extension
isomorphisms, their structure identity equivalences, and a Galois group whose
automorphisms act by transport around loops of the extension type. The concrete
extension F4/F2 has a complete automorphism classification and a checked
identification of its Galois group with the cyclic group of order two.

Subgroups and subfields now have proposition-valued membership, closure laws,
and equality of bundles determined by membership. Small-indexed subgroup and
subfield intersections satisfy their greatest-lower-bound property. Group
homomorphisms, subgroup inverse images, normal subgroups and normal kernels
are checked. Subgroups also have bundled group carriers, injective inclusions
and unique factorization of homomorphisms that land in them. For any extension,
fixed subfields and fixing subgroups form an order-reversing Galois connection;
fixed elements are also characterized by invariance under transport around
the corresponding loops.

For F4/F2, the fixed field of the whole automorphism group is the embedded F2.
An intermediate field is equal to F2 or F4 when membership of alpha is decided.
The two subobject assignments recover a subgroup when Frobenius membership is
decided, and recover an intermediate field when alpha membership is decided.
These are actual equalities of bundles. `f4_galois_correspondence` now packages
the two assignments as a full `Equiv(U1, ...)` between decidable subgroups and
decidable intermediate fields; both maps reverse inclusion. Membership
decisions are explicit data, with uniqueness proved by function extensionality.
This does not yet prove degrees or supply the general finite correspondence.
Generated subfields and ambient composita are constructed from finite
derivations, with their leastness and lattice laws. Most of the remaining
general algebra is finite linear algebra, polynomial theory, algebraic
extensions, and Artin's fixed-field theorem.

The F4 Galois group is abelian by transport from the cyclic group of order two,
and consequently all its subgroups are normal, without a decidability
assumption. This is not yet the normal-subgroup/normal-extension criterion of
the general correspondence.

The first general target is the finite fundamental theorem, including degrees,
normal subgroups, and quotient groups. Full scope also includes algebraic
closures, infinite Galois extensions with their profinite topology, and the
correspondence with closed subgroups. These are separate milestones; completing
the finite theorem must not be presented as completing the infinite theory.

## Lang's distinguished classes of extensions

Use the definition in the excerpt supplied by the user. Write C(F,E) for
membership of the specified extension F → E in the class. A class is
**distinguished** when it has these three properties:

1. **Tower criterion.** For a tower k ⊆ F ⊆ E,
   C(k,E) holds if and only if C(k,F) and C(F,E) hold.
2. **Compositum base change.** If C(k,E), and F and E are embedded over k in
   a common field Ω, then C(F,EF).
3. **Compositum closure.** If C(k,F) and C(k,E), with F and E in a common
   field Ω over k, then C(k,FE).

Here EF is the smallest subfield of Ω containing the two images. Its ambient
field and the compatibility of the embeddings are part of the data. This is
not an assertion that a tensor product of arbitrary field extensions is a
field, nor that a compositum can be chosen without specifying compatible
embeddings. Once the necessary compositum identifications exist, clause 3
follows from clauses 1 and 2; still expose all three clauses in the interface
to match Lang's definition.

Formalization requirements:

- Model a class by a proposition-valued predicate on bundled extensions, with
  explicit universe parameters or a documented fixed-universe scope.
- Package the three laws as evidence for `Distinguished(C)`. This interface
  is now implemented in `distinguished_extensions`; the intended algebraic
  instances still need their proofs.
- Express towers through embeddings and a commutative triangle. Do not rely
  on literal inclusion of underlying carrier types.
- Define composita first as subfields of a fixed ambient field; prove their
  least-upper-bound property, symmetry, associativity and change-of-ambient
  compatibility under field embeddings.
- Prove that C transports along extension isomorphisms. For a predicate on
  the existing univalent extension type this follows by transporting along
  its structure identity path; use that result instead of duplicating
  isomorphism-invariance fields in every class record.
- Keep class membership propositional. A selected basis, polynomial or
  splitting witness belongs in a separate data type; differing choices must
  not make two mathematical class-membership assertions different.
- Establish distinguished-class instances for finite extensions, algebraic
  extensions, separable algebraic extensions, and finite separable extensions,
  under the precise assumptions proved for each instance.
- Do not register normal or Galois extensions as distinguished by analogy:
  normality, and therefore being Galois, is not generally transitive in towers.

This is a useful HoTT interface: paths transport extension properties and
their theorems across equivalent presentations. It does not remove the need
to prove the algebraic tower and compositum laws.

## Development milestones

| Stage | Required constructions and results | Completion criterion |
|---|---|---|
| 1. Subobjects and fixed elements | Subgroups, normal subgroups, subfields, intermediate fields, generated subfields, intersections and composita; fixed subfield of an automorphism subgroup; subgroup fixing an intermediate field | The two assignments are defined and form an order-reversing Galois connection for arbitrary extensions |
| 2. Finite linear algebra | Vector spaces over bundled fields, spans, independence, explicit finite bases, dimension invariance, extension degree and the tower law | Degree calculations have checked hypotheses and no hidden choice of basis |
| 3. Polynomial algebra | Finite-support polynomials, evaluation, division over fields, root bound, ideals or a sufficient principal-ideal API, irreducibility and quotient fields | Adjoining a root of an irreducible polynomial constructs a field with its universal property |
| 4. Algebraic extensions | Minimal polynomials, finite versus finitely generated algebraic extensions, simple extensions, embedding extension lemmas and composita | Finite and algebraic extensions satisfy the distinguished interface |
| 5. Separability and normality | Repeated roots, formal derivative, separable polynomials/elements/extensions, splitting fields, normal extensions, embedding criteria, counts of embeddings | Separable distinguished-class instances and the finite Galois characterizations are proved |
| 6. Fixed-field theorem | Linear independence of distinct field homomorphisms; Artin's theorem for a finite group H of field automorphisms | The degree of L over its H-fixed field is the cardinality of H, and all automorphisms fixing that field are classified |
| 7. Finite correspondence | Mutual inverse assignments, order reversal, degree/index formulas, normality criterion, restriction maps and quotient group isomorphisms | The complete finite fundamental theorem stated below is checked |
| 8. Algebraic and separable closures | Existence under explicit assumptions, extension of embeddings, uniqueness up to isomorphism, normal and separable closures | Closure existence and any choices of embeddings are separately tracked |
| 9. Infinite correspondence | Finite Galois subextensions, inverse systems of finite groups, Krull topology, closed subgroups and fixed fields | The infinite fundamental theorem, with closed-subgroup hypotheses and topological quotient statements, is checked |

Stage 6 can proceed alongside parts of stages 3–5 once the linear-algebra
foundation is ready. The final finite correspondence uses both branches.
General algebraic closures are not a prerequisite for every possible proof
of the finite theorem: constructing the particular finite splitting fields
needed is a smaller initial target.

## Current implementation and next work

Checked source modules: `subgroups`, `subfields`, `subfield_intersections`,
`intermediate_fields`, `galois_fixed_points`, `galois_fixed_fields`,
`galois_fixing_subgroups`, `f4_fixed_field`, `f4_intermediate_fields`,
`f4_galois_connection`, `decidable_subobjects` and `f4_galois_correspondence`.
The reusable `order_maps` interface and its
`galois_orders` instance establish variance and idempotent closure as bundle
equality. All are available in the proof selector.

The stage-1 completion criterion (an order-reversing connection) holds, and
the listed subobject constructions are checked. Generated subfields and
composita have leastness, symmetry, associativity and
compatibility with arbitrary ambient field embeddings. Subfields are realized
as bundled fields with injective inclusions; intermediate fields give actual
commutative towers. Images and inverse images are subfields, with their order
adjunction, and every embedding is an isomorphism onto its image. Normal
subgroups, inverse images, kernels and realized subgroup carriers are now
checked. Subgroup images and their surjective factorization are also checked;
the quotient-group layer now includes arbitrary-coset operations and the first isomorphism theorem.
The F4 example has a packaged correspondence of decidable-subobject types;
a classical all-subobject theorem is not yet exposed.

Universe plan: carriers and membership values lie in U0; `Subfield(F)`,
`IntermediateField(K,E)` and `Subgroup(G)` lie in U1. The implemented
intersections are indexed by a supplied U0 type. Do not form the intersection
of all U0-valued subfields and silently claim its membership is still U0.
Generated subfields now use a checked small presentation by finite closure
derivations. Rank zero contains the generators. Each successor allows a keep
step, zero, one, negation, addition, multiplication or a witnessed inverse.
Derivations can be padded, so two different ranks can be combined. Membership
is the propositional truncation of the existence of a rank and derivation;
both the derivation data and the truncation are in U0. Closure and leastness
are proved without LEM or choice. A compositum is generated by the sum of the
two membership predicates, and the prime subfield is generated by the empty
predicate. These live in `subfield_generation_steps`, `generated_subfields`
and `subfield_composita`.

`subfield_transport` proves compatibility with ambient isomorphisms by path
induction and the field structure identity theorem. It does not claim that
arbitrary field embeddings are paths. `f4_generated_subfields` checks that
alpha generates F4 and that the prime subfield of F4 is exactly the embedded
F2; it also excludes alpha from that prime subfield and computes an actual
unequal-rank derivation.

The embedding layer is now checked in `field_embeddings`,
`field_embedding_factorization`, `field_embedding_image`, `subfield_carriers`,
`intermediate_towers`, `subfield_preimages`, `subfield_images`,
`subfield_image_orders` and `compositum_embeddings`. `f4_embedding_images`
checks the non-surjective inclusion F2 → F4, its image as a subfield, equality
of its realized image field with F2, and the intermediate-field tower.
These modules are in the new Fields & Galois Theory browsing topic.

`embedded_composita` now realizes the compositum of two separately embedded
fields, with both embeddings, their ambient triangles, common-base agreement,
leastness, factorization into every containing ambient subfield, and equality
after swapping the two factors. `f4_embedded_composita` proves that two copies
of F2 inside F4 generate a field equal to F2, not the whole ambient F4.

`distinguished_extensions` implements Lang's three clauses. It derives the
third from the first two using the checked common-base agreement, and derives
isomorphism invariance by transport along the extension structure identity
path. Its scope is U0 field carriers, U1 extension bundles and U1-valued
propositional membership; the type of class predicates lies in U2. It does not
assume that class predicates are small. The finite/algebraic/separable
distinguished-class instances still require the later algebra; none is being
asserted merely by defining this interface.

The checked group layer is in `group_operations`, `group_homomorphisms`,
`subgroup_constructions` and `normal_subgroups`. Inverses project the existing
unique witnesses in group laws. A homomorphism stores multiplication
preservation; identity and inverse preservation are derived. Kernels are
inverse images of the identity subgroup, so normality follows from the
general inverse-image theorem. Conjugation is an explicit automorphism and,
by group univalence, a loop in `Group` whose decoded isomorphism is checked.
Normality transports by path induction. `f4_normal_subgroups` transports
commutativity from `CyclicTwo` along the existing group equality. Generic
subgroup inclusion laws now supply the `galois_orders` instance.

`subgroup_carriers` realizes subgroups as groups and proves their inclusion
and factorization universal property. `finite_decisions` supplies constructive
finite search; `decidable_subobjects` bundles pointwise membership decisions
and proves their uniqueness. `f4_galois_correspondence` gives the actual fixed
and fixing maps, both inverse equalities, the full coherent equivalence and
order reversal. Its dependencies are function extensionality and univalence,
without LEM or choice. The general adjointification lemma in
`equivalence_from_inverse` uses path induction alone and has no axioms.

`subgroup_images` now constructs image membership as truncated existence,
proves the image/inverse-image adjunction and covariance, and factors any
homomorphism through its image with a merely surjective first factor. Identity
and trivial homomorphisms have their expected images as equal subgroup bundles.
The image construction and surjectivity use only the existing truncation
axioms; bundle equalities additionally use function extensionality and univalence.

`group_cosets` now proves that `S(x⁻¹y)` is an equivalence relation, that left
translation always preserves it, and that right translation preserves it
exactly when S is normal. Multiplication and inversion respect normal cosets.
Kernel cosets are exactly homomorphism fibers. These relation-level results
require no axioms. The module also identifies related representatives with
equality paths in the existing U1 predicate quotient and proves representative
independence of products, using the existing quotient dependencies.
The subsequent `quotient_operations` and `quotient_groups` modules descend
these operations to arbitrary quotient elements and bundle the resulting group.

`quotient_descent` constructs the unique map from the predicate quotient to a
U1 set from a map respecting the relation. Its value is characterized by all
representatives; uniqueness makes the entire value/evidence pair a proposition,
so truncation elimination requires no chosen representative. It proves the
propositional computation rule and uniqueness of the descended map. These
constructions use truncation and function extensionality, without univalence,
LEM or choice.

`group_quotient_maps` applies this to a homomorphism that kills a subgroup,
with the triangle, uniqueness, unit and representative-product formulas, and
the converse that a factorization kills the subgroup. `kernel_quotient_image`
proves the carrier equivalence `G/ker(h) ≃ im(h)`: the inverse sends an image
element to its whole fiber predicate. Both inverse homotopies are checked.
Univalence gives equality of these carriers in U1, and transporting setness
shows the kernel quotient is a set. No preimage choice or universe lowering
is used. `group_first_isomorphism` now packages the same maps and inverse laws
as `GroupIsoAt(U1, KernelQuotientGroup(G,H,h), group_lift(ImageGroup(G,H,h)))`,
with multiplicativity proved for arbitrary cosets.

The group interface is now the universe schema `GroupAt(U)`, with the
existing `Group` definition its U0 specialization. Quotients remain in U1;
small image groups are explicitly repackaged there with `group_lift`.
`quotient_is_set` uses the constant-path argument, and function-space setness
is proved by a pointwise square of paths. Only the existing truncation
assumptions are needed; no LEM, choice, or new kernel rules were added.

`quotient_group_universal` now supplies the bundled projection, its
subgroup-killing law, descent, the commuting triangle, and uniqueness as an
equality of homomorphisms. The target is an arbitrary `GroupAt(U1)`, so the
result applies to quotient targets themselves. `GroupHomAt(U)` is the single
homomorphism family, with the existing `GroupHom` its U0 specialization.
Projection is also proved epimorphic. On small targets the descended map
agrees with the earlier `group_quotient_map`. Only the four existing
truncation families at U1 occur in the universal-property theorem.

Next: add a concrete non-normal subgroup example. Extending the structure identity
equivalence to `GroupAt(U1)` will let this large-group isomorphism become
an equality of bundled groups, beyond the already checked carrier equality.
Then proceed to explicit finite linear algebra and degree, preserving the
separate algebraic and infinite-theory milestones below.

Implementation constraints for the remaining group layer:

- The checked image construction uses propositional truncation, unlike the
  actual unique preimages used for field-embedding images. Continue to use
  its merely surjective factor without selecting representatives.
- For a normal subgroup N, reuse the checked `SameLeftCoset(G, N)` relation
  and `normal_coset_multiply` / `normal_coset_inverse` to descend
  the operations. Reuse the checked unique descent in `group_quotient_maps`
  and its bundled extension in `quotient_group_universal`. The carrier
  equivalence from `kernel_quotient_image` is already bundled by
  `group_first_isomorphism`; reuse it for later quotient statements.
- Keep the resolved universe discipline: `SetQuotient` represents classes by
  predicates in U1, `Group = GroupAt(U0)`, and `QuotientGroup` belongs to
  `GroupAt(U1)`. Cumulativity allows repackaging a small carrier; it does not
  justify lowering the quotient to U0. Finite decidable quotients may later
  have separate small presentations.

## Precise finite target

For a finite normal separable extension L/K, let G = Aut_K(L). Prove:

- The fixed field of G is the image of K.
- `H ↦ Fix(H)` and `M ↦ Aut_M(L)` are inverse equivalences between the
  type of subgroups of G and the type of intermediate fields of L/K.
- The equivalence reverses inclusion. It exchanges generated joins and meets.
- For an intermediate field M corresponding to H,
  `[L : M] = |H|` and `[M : K] = [G : H]`.
- M/K is Galois exactly when H is normal in G.
- In that case restriction induces `G/H ≃ Aut_K(M)` as groups.

These are the usual finite correspondence and normal-subgroup target; see
the [Stacks Project's fundamental theorem](https://stacks.math.columbia.edu/tag/09DW).
The implementation must prove the hypotheses of the fixed-field and embedding
count results, rather than accepting the correspondence as a new axiom.

## Constructive and universe requirements

Preserve constructive shared foundations. Track `LEM` and `Choice` separately
on each theorem when required, following the project's existing policy.

- Distinguish an explicitly enumerated finite type from a type merely proved
  finite; likewise distinguish a supplied basis from mere existence of one.
- Do not silently decide membership in arbitrary subgroups or subfields.
  In particular, finite ambient carriers do not constructively make every
  proposition-valued subobject decidable. A constructive first example may
  classify decidable subobjects; a theorem about all subobjects needs its
  additional assumptions made explicit.
- Existence of inverses, roots, bases and embeddings must state whether it
  returns data or a propositional truncation. Eliminate truncation only into
  justified targets. Use uniqueness to recover data when available.
- Isolate classical linear-algebra and algebraic-closure arguments; do not
  add global LEM or choice to the field and extension interfaces.
- Account for the universe of all subfields and proposition-valued subsets.
  Establish a universe plan before implementing intersections, generated
  subfields or closure constructions; do not assume propositional resizing.
- Infinite Galois theory needs a separate audit of compactness, inverse-limit
  existence, and extension-of-embeddings assumptions.

Use the existing kernel rules, universes, truncation, quotient and univalence
infrastructure where applicable. No new mathematical kernel rule is planned.
Any actual expressivity or performance obstacle must be documented before
proposing language or kernel changes.

## HoTT presentation and regression examples

Reuse the existing identification of extension automorphisms with loops.
Check that composition, inversion, restriction, and actions on roots agree
with path composition, reversal, induced maps, and transport. When moving from
a group isomorphism to equality of bundled groups, apply the existing group
structure identity theorem. Equality of structures is not definitional
equality, and it must retain the univalence dependency in the inspector.

First complete the correspondence for F4/F2: its fixed fields, subgroups, and
the absence of proper intermediate fields, stating explicitly whether the
subobjects are decidable or classical. This validates the interfaces on the
current finite model. It does not replace the general theorem. Add a later
example with a proper intermediate field, and an example detecting why the
normal-subgroup condition is necessary.

For each milestone, check selected modules while developing; run the full
library once the batch is complete. Include negative checks for lost
base-field compatibility, a false degree, and an incorrect fixed-field
claim. Publish exact axiom dependencies and distinguish proved results from
planned requirements on the website.

## Effort assessment

This is a substantial library project, not a short extension of the F4
calculation. The current automorphism/loop layer is reusable, but stages
2–7 remain before the general finite theorem. Stages 8–9 form another
substantial project. Estimate calendar time only after stage 2 exposes the cost of reusable
finite-dimensional proofs in Cubist.
Development is now authorized by the subsequent request to work toward this
full roadmap. This file retains the complete target; the checked first-stage
results do not narrow it.
