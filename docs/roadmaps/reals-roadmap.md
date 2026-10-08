# Real-number roadmap

Status: paused during language development, but for R1's integers and
rationals, built on 2026-10-05; corrected on 2026-09-28 after
the [work-plan audit](audits/2026-09-28-audit.md) (previously reviewed
2026-09-27); restructured on 2026-09-25 for the rebuild of the library. The
first library's development is described below, under "The first library's
development", and is archived with that library. Its results are summarized in
[library-results.md](../library-results.md#analysis). Revised on 2026-10-07:
the [runtime evaluation roadmap](runtime-evaluation-roadmap.md) owns the
new binary numerical foundations (NUM0–NUM2), including the default `Z`
and `Q`. This roadmap owns their order, additional presentations and the
real-number constructions; those remaining packages are deferred in the
[work plan](work-plan.md#deferred-library-backlog) as B3 (integers), B4
(rationals and the field interface) and B5 (reals), and no language
milestone resumes them automatically. On 2026-10-05 the library's
foundations resumed, and R1's integers and rationals were built, as
quotients rather than the earlier signed/canonical plan. R1's remaining
work now targets NUM2's binary-backed replacements. Their order, and the
rest of this roadmap, stay deferred; NUM0–NUM2 do not wait for them.

## Plan for the rebuilt library

The audit revised the precision type, the normal-form and approximation
claims, R3's breakdown and each package's dependencies. The 2026-10-07
alignment with NUM2 makes binary-backed quotients the primary integer
and rational carriers; signed and lowest-terms forms are later
presentations of those carriers.

The interface stays an **Archimedean ordered field with Cauchy completeness**,
with Dedekind completeness as a separate property. It becomes the theory
`CompleteOrderedField` (ergonomics milestone 6), so analysis is written
against its models and does not depend on which construction supplies them.
The constructive developments assume neither excluded middle nor choice.

**An unproved compatibility obligation (corrected).** The archived interface
([complete_fields.cubist](../../archive/first-library/complete_fields.cubist))
asks, for each positive element of the field carrier, an actual
natural-number bound, both for Cauchyness and for convergence. The Cauchy
completion below uses positive-rational precision, as the
[HoTT book](https://github.com/HoTT/book/blob/master/reals.tex#L437-L450)
does. These are different constructive APIs: a selector from arbitrary real
precision does not follow from rational bounds merely existing. R2 fixes
the precision type for its computational modulus, proves the bridge between
sequences with a modulus and the completion's approximations, and states
which legacy adapters need extra data. The archive's parameterized
definitions are not claimed to fail to check; the obligation is the bridge.

| Carrier | Construction | Needs | Computation |
| --- | --- | --- | --- |
| Integers | **Built** on 2026-10-05 from unary `Nat and Nat` in `library/integers.cubist`. NUM2 owns the new default `Z`, the same-difference quotient of `BNat and BNat`, with ring/domain laws. R1 adds order; a later `inductive Int { pos(n : BNat); negsucc(n : BNat); }` presents this new `Z` | NUM1/NUM2 and effective quotients; L2.7 for the later presentation interface | Binary operations on the new quotient; decidable equality. A class of pairs need not be a signed constructor normal form |
| Rationals | **Built** on 2026-10-05 in `library/rationals.cubist`. NUM2 reuses its generic field-of-fractions construction at the new `Z` to supply the new default `Q`. R1 adds order and a later lowest-terms presentation using binary-backed `Z` and positive `BNat` denominators | NUM2 for the field; L2.7, binary gcd, normalization correctness and uniqueness for the canonical presentation | Binary fraction operations and decidable equality; quotient semantics alone do not give reduced output |
| Reals (primary) | `Real = initial CauchyStructure`: the book's Cauchy completion, a higher inductive-inductive type with its closeness relation, at precision `PosRat` | Kernel H3 (K5.1, K5.2, L5.1); L2.6 initial models and folds; the rational prerequisites | Closed reals normalize to the constructors `rat`/`lim` or to the stage's formal Kan forms; a closed rational approximation comes from a proved approximation theorem, read out through L2.9b |
| Reals (fallback) | Dedekind reals: located two-sided cuts of the rationals, in `next(U0)` | Kernel H1 (`Trunc`) and the cut and field mathematics; with canonical rationals, no generic quotient is needed for cuts | Approximations through locatedness, given a proved approximation result, a closed computable input and L2.9b's checked readout; native truncation alone supplies none of these |

- **Why Cauchy reals are primary.**
  - They are complete without countable choice, unlike the ordinary quotient
    of Cauchy sequences.
  - Their closed elements have data canonicity (corrected): constructors or
    the stage's formal compositions, which is not a canonical rational
    representation of an arbitrary real.
  - Their recursion principle is folding into a model, and the Lipschitz
    extension of maps from the rationals is such a fold.
- **When to use the fallback.** Dedekind reals need no kernel work beyond
  H1. Use them only if H3's soundness note or implementation stalls. Then
  prove that Cauchy reals embed into them later.
- **Dropped:**
  - the ordinary Cauchy quotient, whose completeness needs a
    countable-choice hypothesis;
  - classical Boolean cuts, which need excluded middle.

  Both remain in the archive as evidence.
- **Functions on the reals** are defined by composition, by folding into
  models (for example the Lipschitz extension view), and by limits with a
  modulus. A discontinuous function is defined only on a subtype, or with
  excluded middle as a visible non-computing dependency.
- **Universes.** No resizing is the rebuilt foundation's requirement
  (kernel G2), met with G0 and H1's universe-preserving `Trunc`. It does not
  describe the archive: its universe-lowering `FieldExists` remains until
  the G2 ledger's actual migrations, and that legacy behaviour is kept
  distinct from the new universe-preserving truncation.
- **Names.** `PosNat` is positive `BNat` for canonical denominators;
  `PosRat` is positive NUM2 `Q` for precision. Numerical sequence indices
  and modulus bounds use `BNat`, whatever public spelling is adopted for
  the new default `Nat`.
- **Readout.** There is no source-level selector `Trunc(A) -> A`; L2.9b is
  a closed evaluation tool that needs a closed computable input and a
  checked error certificate. Its later H3 extension must specify the
  extracted witness's type: under heterogeneous transport a base witness
  has type `A(0)` while the requested result needs `A(1)`, so "read off the
  base" needs that case. H1's homogeneous `hcomp` and computing parameter
  transport show no such defect; L2.9b's tests include transported
  truncations, and the argument is revisited when H3's formal operations
  are fixed.

### Milestones

1. **R1. Order and presentations of the new integers and rationals**
   (B3 for the integers, B4 for the rationals). Consume NUM2's `Z` and `Q`,
   their arithmetic, setness, decidable equality and algebraic laws.
   Prove their decidable orders, ordered-ring/field laws and the
   Archimedean property with binary natural bounds; define `PosRat` and
   check closed order and bound examples. These are the prerequisites
   for R2/R3 on the new hierarchy. This order development still awaits
   the scope decision in [first action 8](work-plan.md#first-actions).

   Later presentations are signed integers with binary
   magnitudes and canonical lowest-terms rationals, with binary gcd,
   normalization correctness and uniqueness. Prove agreement with NUM2's
   quotient carriers. These are not replacements for NUM2's construction
   or prerequisites for the quotient field's order; its constructors alone
   do not supply canonical representatives.

   **Historical completion:** the 2026-10-05 unary-backed carriers have
   arithmetic, setness, decidable equality and field laws, but no order.
   They remain compatibility clients. NUM2 and R1's new targets are
   planned, not implemented; neither requires comparison maps to the old
   carriers.
2. **R2. The interface** (B4). The theories `OrderedField` and
   `CompleteOrderedField`, with limits, uniqueness and the algebra of limits
   stated generically, on L2.4's core theories and L2.5a's h-level fields.
   Use R1's `PosRat` over the new `Q` for precision and `BNat` for numerical
   bounds; settle the modulus API and prove the bridge above before
   porting clients. It needs no H3 and can proceed with
   any model, even before a concrete reals construction exists. L2.4 was
   delivered on 2026-10-05, and the library's `Field` is the starting
   point; its inverse becomes partial with L2.10k.
3. **R3. Cauchy reals** (B5), scheduled as separate obligations
   (corrected: "field operations by folding" hid most of them):
   - `CauchyStructure` and its initial model at H3;
   - the rational embedding, and closeness compatible with the order;
   - Lipschitz extension of maps from the rationals, with uniqueness;
   - the field laws: addition and negation by Lipschitz folds; squaring
     and multiplication by bounded extensions; inversion away from zero,
     as the [book constructs them](https://github.com/HoTT/book/blob/master/reals.tex#L1487-L1577);
     one globally Lipschitz fold does not supply them all;
   - the Archimedean property and Cauchy completeness;
   - a `CompleteOrderedField` model;
   - an approximation theorem with a checked error certificate, and its
     readout through L2.9b: a rational within 10⁻³ of √2 from a closed real.

   A working H3 eliminator is a language milestone; this model is a
   mathematical development with its own proof obligations.
4. **R4, optional** (B5). Dedekind reals, as the fallback or as a comparison.
   Prove the embedding of Cauchy reals into them. Record the countable-choice
   or excluded-middle hypothesis under which the embedding is an equivalence.
   Readout has the gate above.

No milestone may be replaced by an axiom asserting that a construction is a
complete ordered field.

### Dependencies and acceptance

| Package | Explicit dependencies and acceptance |
| --- | --- |
| R1 integers | NUM2's new `Z`; scope decision before decidable order and ordered-ring laws. Later signed presentation: binary magnitudes, L2.7 and agreement with this `Z` |
| R1 rationals | NUM2's new `Q`; R1 integer order and the scope decision before rational order laws, `PosRat` and Archimedean bounds in `BNat`. Later canonical presentation: L2.7, binary gcd, correctness, uniqueness and agreement with this `Q` |
| R2 field interface | L2.4 core theories, L2.5a h-level fields and R1's ordered new `Q`/`PosRat` for rational precision; modulus API with binary bounds and the sequence/approximation bridge proved before clients are ported; no H3 |
| R3 Cauchy reals | K5.1/K5.2/L5.1; L2.6 initial models and folds; R1 and R2; the construction proofs listed above; L2.9b for the closed approximation readout |
| R4 Dedekind fallback | H1 truncation and the cut and field mathematics; canonical rationals in place of a generic quotient; L2.9b for readout |

The work plan replaces Cauchy reals and √2 as the active H3 release gate
with a small context/type interpreter; the mathematical example remains
deferred integration acceptance. The rebuilt library's rationals are a
field, not yet an ordered one, and no complete ordered field has been
constructed in it; the
archive records that its abstract `Q` and its candidate real carriers did
not supply those certificates.

## The first library's development (archived)

The text below describes the first library at the time it was archived.
- Its definitions and lemmas were checked by the kernel, but no theorem
  supplied a `CompleteOrderedField` instance for any of its three construction
  carriers.
- The parameter named `Q` was an abstract small type; the rational ordered
  field was never constructed.

### Shared interface

[ordered_fields.cubist](../../archive/first-library/ordered_fields.cubist) defines a commutative
ring, a proposition-valued strict order, non-strict order and apartness, lattice
operations, order-compatible arithmetic, and inversion for elements apart from
zero. It proves cancellation, uniqueness of inverses, and `zero != one` from
the stated laws.

[complete_fields.cubist](../../archive/first-library/complete_fields.cubist) adds:

- `Archimedean`: every element is below some natural-number multiple of one.
- `FieldCauchy`: a sequence **with a modulus**. Each positive epsilon supplies
  an actual natural bound, not merely the proposition that a bound exists.
- `FieldConverges` and `CauchyComplete`: a limit and its convergence evidence.
- `CompleteOrderedField`: the ordered-field laws, Archimedean property, and
  Cauchy completeness together.
- `DedekindComplete`: every inhabited, rounded, disjoint, located two-sided
  cut is realized. This is separate from `CompleteOrderedField`.

The distinction between the two completeness properties, and the two-sided
cut conditions, follow the [HoTT book's real-number chapter](https://github.com/HoTT/book/blob/master/reals.tex).
This formulation does not impose classical trichotomy or the assertion that
every inhabited bounded subset has a supremum on the constructive interface.

`complete_field_ordered` and `complete_field_limit` consume an already supplied
field certificate. They are accessors, not proofs that a particular construction
is a complete ordered field.

### Construction modules and checked results

| Module | Checked development | Additional assumptions |
| --- | --- | --- |
| [Constructive Dedekind cuts](../../archive/first-library/dedekind_cuts.cubist) | Proposition-valued cuts; principal cuts; preservation and reflection of strict order; injectivity of the principal-cut map; downward/upward closure, separation, irreflexivity and transitivity of cut order | The base order, density, and absence of endpoints are explicit parameters where needed. Truncation; no excluded middle or choice. |
| [Classical Boolean cuts](../../archive/first-library/boolean_cuts.cubist) | Boolean predicates with cut laws; decoding to constructive cuts; conversion back with proofs that both memberships are preserved | Decoding uses no classical principle. Encoding arbitrary proposition-valued cuts uses `LEM`; predicate equality also uses univalence and function extensionality. No choice. |
| [Ordinary Cauchy quotient](../../archive/first-library/cauchy_quotient.cubist) | Sequences with moduli; eventual-closeness relation; equivalence-relation laws under explicit reflexivity and radius-composition hypotheses; quotient carrier; mere existence of representatives | Constructive through the quotient construction. Simultaneous representatives use the explicit `RepresentativeChoice` argument. No global choice axiom is loaded. |

[set_quotients.cubist](../../archive/first-library/set_quotients.cubist) represents classes by
predicates with a **truncated** witness that the predicate describes a class.
It proves surjectivity of the class map and, for a proposition-valued equivalence
relation, that two classes are equal exactly when their representatives are
related. The generic carrier can be formed for other relations too; its name
does not certify setness or a quotient universal property for those relations.

`RepresentativeChoice(A, relation, sequence)` is the particular countable
choice instance that combines the individually inhabited representative fibers
of a sequence. It is a theorem parameter, not a new axiom and not a proof of
countable choice. Its conclusion remains truncated. Consequently, the axiom
list for `cauchy_sequence_representatives` does not include choice: the choice
hypothesis is visible in its type instead.

The ordinary quotient is distinct from the book's higher inductive-inductive
Cauchy completion. The latter avoids countable choice; that construction has
not been implemented here. The book discusses the role of countable choice in
the ordinary construction and compares Cauchy and Dedekind reals in the
[same chapter](https://github.com/HoTT/book/blob/master/reals.tex).

The [ordered Cauchy lemmas](../../archive/first-library/cauchy_ordered.cubist) now discharge
the self-closeness and radius-composition hypotheses from a supplied ordered
field. They use constructive halving and the proved triangle inequality.
[Limit laws](../tactical/analysis_limits.md) also establish uniqueness, addition, and
complex completeness over complete scalars. These do not yet construct the
rational field or finish the quotient's field and completeness certificates.

### Universes and foundational assumptions

`Q : U0` is small. Predicates `Q -> U0`, and hence proposition-valued cuts,
live in `U1`. The shared interface accepts a carrier `F : U1`, so these
cuts do not have to be replaced with Booleans to fit its universe.

[field_logic.cubist](../../archive/first-library/field_logic.cubist) specializes the **existing**
library truncation and function-extensionality axioms at `U1` using the new
explicit-universe primitives. [field_extensionality.cubist](../../archive/first-library/field_extensionality.cubist)
adds small-proposition extensionality via the existing univalence axiom and
equality lemmas for dependent pairs in `U1`.

There is a foundational qualification: the existing library `lib_Trunc` returns
a type in **U0 even for an input in a higher universe**. `FieldExists` retains
that signature. This is universe-lowering truncation; this development is not
claimed to avoid resizing strength. It adds no resizing axiom, classical axiom,
choice axiom, or unchecked kernel rule. Changing that existing foundation to
universe-preserving truncation would be a separate change.

### Remaining construction proofs

1. Construct the rational ordered field and discharge its order, arithmetic,
   density, and radius-composition obligations.
2. Prove setness and extensionality of the cut carrier, define its arithmetic
   and lattice operations, and prove all ordered-field laws.
3. Prove the Archimedean property, Cauchy completeness, and Dedekind completeness
   of the constructive cut construction.
4. Prove the Boolean conversion round trips and transport the full field
   certificate to the classical carrier.
5. Complete the quotient's setness and elimination interface, descend arithmetic
   and order to Cauchy classes, and prove completeness with the precisely stated
   choice assumption. Relate that assumption to set-level countable choice.
6. Exhibit the three named `CompleteOrderedField` certificates and compare them
   under their stated assumptions.

No item in that list is replaced by an axiom asserting that a candidate is a
complete ordered field. In the web source explorer, each real-number module
links to this status and checks its actual declarations.
