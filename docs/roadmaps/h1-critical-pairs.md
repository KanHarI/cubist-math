# H1 substitution stability and critical pairs

Status: review draft, 2026-09-30. This is the case analysis for Lemma H2
and the overlap analysis of the [H1 specification](h1-signature-specification.md),
sections 3.3–3.7. It supplies the argument requested by release checklist
item 2. The maintainer must review its coverage and joins; adding this draft
does not record that decision or discharge the model and canonicity gates.

The argument concerns well-typed admitted signatures and substitutions that
preserve the finite-level fragment. It assumes substitution stability and
the conversion congruences of the baseline kernel, as section 4.1 does.
The regression tests exercise representative instances of the joins in
`kernel/tests/test_signatures.c`.

## Reduction and substitution

Write `σ` for simultaneous capture-avoiding substitution of interval
formulas for free dimensions and finite level expressions for level
variables. Fresh bound dimensions may be renamed before substitution.
Stability means that if `t → v` by a generated rule, then `tσ` and `vσ`
have a common reduct, modulo bound names and baseline conversion. It does
not require the same one-step rule to remain applicable: substitution can
make a face true or a constructor formula an endpoint.

Substitution is homomorphic on the term nodes. The De Morgan operations and
face conjunction/disjunction are respected by their algebraic substitution.
An empty face stays empty; a nonempty face may become empty or true. The
arguments below therefore include cases where a structural rule hands over
to `Face` or to path boundary reduction. Levels never vary along a dimension.

## Lemma H2 by rule

### Data composition

Suppose the base and every nonempty tube expose the same constructor `c`.
Substitution preserves that constructor and substitutes its parameters and
argument telescope. Empty tubes may disappear. If no face becomes true, the
result is the same constructor applied to the substituted telescope
composition: telescope formation, tuple projections and iterated Sigma
composition commute with substitution by the baseline rules. A position is
composed by the Pi rule; its backward filling substitutes in the same way.

If a tube face becomes true, the baseline face rule selects its endpoint.
Taking the constructor rule first gives `c` applied to telescope components
whose compositions select those same tube arguments. Hence the result is
the selected constructor term. A previously neutral composition may start
computing after substitution; stability of an existing reduction does not
require it to remain neutral. This covers section 3.3 and CP04 below.

### Formal homogeneous composition

For a higher sort, homogeneous composition has only face selection and
empty-tube deletion. Substitution distributes through the type, base and
tubes. Empty deletion commutes with substitution. If a tube becomes true,
selecting its endpoint before or after substitution agrees. When several
tubes become true their endpoint restrictions agree by the checked system
compatibility. This covers section 3.4 and CP10.

### General higher composition

The section 3.4 reduct uses only parameter endpoint substitution, `∨`,
transport, homogeneous composition and fresh dimensions. These constructions
commute with `σ`, up to freshness. If a face becomes true, the outer `hcomp`
selects the transported tube at its composition endpoint. The transport's
constancy face there is `j = 1`, so `Face` returns the tube at `1`, exactly
the original composition's face reduct. This is CP05.

### Transport of a point constructor

The constructor head and its finite argument list remain the same. Transport
of the argument telescope is built from baseline composition and filling,
which commute with substitution. The target instance is `S(as(1))σ` in
either order. If `φσ` holds, telescope transport returns its base tuple and
the parameters agree at both endpoints on that face. Thus the constructed
target term equals the source term selected by `Face`. This is CP08 for
zero-dimensional constructors.

### Transport of a constructor at dimensions

Let the constructor have dimensions `r₁,…,r_d` and argument filler `θ(i)`.
The candidate target `v`, every boundary piece `b_{l,ε}(i)` and every
squeeze are constructed by capture-avoiding substitution into the admitted
constructor type. When each `r_lσ` remains non-endpoint and `φσ` is false,
the substituted correction is precisely the correction built from the
substituted data, modulo fresh dimension names.

If `r_lσ = ε`, the corresponding correction wall becomes true. At the
wall's endpoint `h = 1`, the squeeze is transport of `b_{l,ε}(0)`, so its
reduct is transport of the source constructor's boundary. Taking boundary
reduction before transport gives that same expression (CP06). If several
walls become true, the boundary pieces agree on the intersection by the
admitted cube's boundary typing. Applying the same squeeze to equal pieces
preserves conversion, so either wall gives the same transport (CP07).

If `φσ` holds, the correction's `φ` wall returns `u₀`. On its intersections
with constructor faces the squeeze is constant: its own constancy face
holds, and its boundary piece is the restriction of `u₀`. Consequently all
selected walls agree with the original `Face` reduct (CP08). This includes
simultaneous changes in `r₁,…,r_d` and `φ`, and every generated squash depth.

### Transport of formal homogeneous composition

Transport maps every tube and the base of the formal box through the same
parameter line. Substitution acts componentwise. If a tube becomes true,
the transported box selects transport of that tube's endpoint. Reducing
the source box first and then transporting gives the identical expression
(CP09). If `φσ` holds, each transported component returns its source
component, reconstructing the source formal box (CP08). Empty tubes may be
deleted in either order.

### Constructor elimination

Both point and dimensional `Iota` substitute the actual constructor
arguments into the same clause and build recursive results by lifting the
same eliminator over the position's Pi arguments and cube. These operations
commute with `σ`. Level substitution changes the annotated types, without
changing the constructor index or clause list.

If a constructor dimension becomes an endpoint, reducing `Iota` first
gives the displayed boundary `⟦β⟧` with the arguments and recursive results
substituted. Reducing the constructor boundary first gives `elim(β)`.
Lemma H1 identifies these by structural induction on the admitted boundary
expression: a position application uses its supplied recursive result; an
earlier constructor uses its earlier clause; path application and path
abstraction preserve this equality by congruence and the path rules. This
uses constructor order and the admitted boundary grammar, including path
abstraction. It is CP01. Several endpoints reduce consistently by CP02.

### Elimination of formal homogeneous composition

The generated reduct uses the homogeneous filler, the motive applied to
that filler, eliminated tubes and the eliminated base. Filler construction
uses `∧`, fresh dimensions and an added zero-face wall; it commutes with
`σ`. If a tube becomes true, the filler on that face is the original tube
throughout its dimension. Composition in the motive selects `elim(w(1))`.
Reducing the source box first also gives `elim(w(1))` (CP03). Empty-tube
deletion changes neither the filler nor its endpoint modulo conversion.

### Boundary reduction

Every applied constructor path carries a literal path-type annotation.
Substituting an endpoint in that annotation commutes with `σ` after fresh
dimensions are chosen. If `σ` makes another formula an endpoint, the
two boundary restrictions agree by the admitted cube's typing (CP02).
Clause annotations created by `Iota` obey the same invariant and use the
displayed boundary, giving CP01. Level substitution preserves the path
node and changes its family and endpoints componentwise.

## Overlap table

The table lists the nontrivial overlaps of the generated rules with the
baseline path and face rules. Its tests choose distinct reduction orders;
the existing transport property tests additionally vary constructor
formulas and parameter lines with a fixed seed.

| Pair | Peak and joining expression | Representative kernel test |
| --- | --- | --- |
| CP01 | `elim(c @ ε)`: Iota then Path gives `⟦β⟧`; Path then elimination gives `elim(β)`, joined by H1 | `elimination`, both circle endpoints with a dependent motive; `elimination_capture`, a path position in a boundary |
| CP02 | Two constructor boundaries at a corner: either restriction order gives the same typed corner | `boundaries`, N3, all torus corners and both path-step orders |
| CP03 | `elim(hcomp[ψ ↦ w] w₀)` where `ψ` becomes true: eliminate then Face, or Face then eliminate, gives `elim(w(1))` | `elimination`, CP03, a nonconstant loop tube and a dependent motive |
| CP04 | Data composition versus held tube: pushing the argument telescope then Face, or Face first, gives `c(θ_w(1))` | `critical_composition_pairs`, CP04, `succ(q @ i)` for `q : zero = m`, ending at `succ(m)` rather than its base `succ(zero)` |
| CP04 (empty) | Data composition versus empty-tube deletion: the empty wall contributes no telescope restriction; either order gives the constructor of the telescope composition with that wall deleted | Data composition argument above; no separate regression for this overlap |
| CP05 | Higher composition versus held tube: its generated hcomp selects transport at constancy face `1`, giving `w(1)` | `critical_composition_pairs`, CP05, `p @ i` for `p : base = x`, ending at `x` rather than `base` |
| CP06 | Corrected transport versus constructor boundary: correction wall at `h = 1` gives `transp(b_{l,ε}(0))` | `kan`, `commutes` on merid and squash faces; `transport_properties`, K10 |
| CP07 | Two correction walls selected at a corner: equality of boundary pieces gives equality of their squeezes | `kan`, CP07, both corner restriction orders for 2- and 3-dimensional squash |
| CP08 | Any structural transport case versus constancy Face: the telescope, correction or component transports restrict to `u₀` | `transport_properties`, K11, structural reduction before restriction to `φ` |
| CP09 | Transport of formal hcomp versus held tube: either order gives transport of `w(1)` | `kan`, CP09, a meridian tube along a nonconstant type line |
| CP10 | Empty-tube deletion versus selection of a held tube: the empty wall cannot be selected, and the surviving tube gives `w(1)` | `critical_composition_pairs`, CP10, an empty wall and `p @ i` ending at `x` rather than `base` |

CP03, CP04, CP05 and CP10 take the face-selection branch with an explicit
`CC_STEP_FACE` step after restriction. Their structural branch reduces
before restriction, independently of the normalizer's rule ordering.

Several held tubes are not separate rules indexed by syntactic tube order:
checked compatibility identifies their selected terms. Their intersections
are included in CP02, CP07 and the system compatibility premise of CP10.

## Coverage of other reductions

The generated root heads are an applied declared eliminator, composition
with a declared family, transport with a declared family, and formal hcomp.
An applied constructor has boundary reduction only at path application.
Different admitted signatures and different constructor indices do not
overlap. The point and dimensional cases differ by the saturated
constructor's declared dimension count; the transport cases differ by the
base's exposed head. Native Nat, sum, W, pushout, Pi, Sigma, universe and
Glue structural rules have different family heads.

Beta, level Beta, projections, definition unfolding and path Beta may occur
in parameters, arguments, clauses, motives, tubes or bases. At those
positions the generated schema carries a variable. Reducing that variable
first, or reducing all its copies after applying the generated rule, joins
by substitution congruence. When an exposed head selects another generated
case, the statement is about the same weak head; Lemma H2 and CP01–CP10
cover endpoint and face changes. Path eta and function eta use the same
annotation and substituted clause type, so expanding first joins after
application by their baseline Beta rules. No rule compares a level to
choose a reduct.

This is an overlap argument for the added rules, relative to the baseline.
It does not infer global confluence from termination or claim normalization:
the specification makes neither claim. Review must accept the completeness
of the head classification, the use of Lemma H1 and baseline congruence,
and the joins above before checklist item 2 is marked reviewed.
