# Finite types and counting

All constructions below are ordinary high-level `.cubist` source. The compiler
emits checked instructions for the same C/WASM kernel used by the workbench;
there is no counting oracle or theorem-specific kernel rule.

Run `make serve` and open:

- [Binomial types](http://127.0.0.1:8088/proof.html?proof=binomial_counting)
- [Permutations](http://127.0.0.1:8088/proof.html?proof=permutations)
- [Functions](http://127.0.0.1:8088/proof.html?proof=function_counting)

Click names to inspect definitions and **View source** to navigate to their
implementation. Result rows and the inspector show the axioms used by each
recorded derivation. These lists include type/context dependencies, rather than
claiming to compute a logically minimal axiom basis.

## Statements

The final results use the full `Equiv` type, including half-adjoint coherence:

```text
finite_binomial_equivalence(n, k) :
  Equiv(U0, Binomial(Fin(n), Fin(k)), Fin(choose(n, k)))

finite_permutation_equivalence(k) :
  Equiv(U0, Equiv(U0, Fin(k), Fin(k)), Fin(factorial_count(k)))

finite_function_equivalence(n, m) :
  Equiv(U0, Fin(n) -> Fin(m), Fin(power_count(m, n)))
```

`endofunction_count(k)` specializes the last construction to `k^k` and presents
it as a bijection record. Explicit checked examples count three-to-three
functions by `Fin(27)`, permutations of three elements by `Fin(6)`, and subsets
of size two in five elements by `Fin(10)`. Empty-to-empty functions have one
element, so the recursive convention is `0^0 = 1`. Choosing too many elements
produces an empty type.

## Natural numbers to types

[finite.cubist](../../archive/first-library/finite.cubist) defines `Fin(0) = Void` and
`Fin(succ(n)) = Unit or Fin(n)` by Nat induction. It constructs explicit
bijections between literal sums `two`, `three`, `four`, `five` and their `Fin`
counterparts. `choose_units_five_two` counts `Binomial(five, two)` itself,
using univalence to transport the general result to the literal sums.

## Binomial types

The construction follows the Boolean-predicate presentation of Rijke's
binomial types, described in [Introduction to Homotopy Type Theory,
section 17.6](https://arxiv.org/pdf/2212.11082#page=238).

```text
Bool = Unit or Unit
Selected(A, predicate) = exists a : A. Truth(predicate(a))
Binomial(A, B) = exists predicate : A -> Bool.
  Mere(Equiv(U0, B, Selected(A, predicate)))
```

`Truth(true) = Unit` and `Truth(false) = Void`. This is the decidable-predicate
presentation (equivalent to the fiber over true). `Mere` is propositional
truncation: a subset carries the mere existence of an equivalence, so different
orderings of its elements are not counted repeatedly.

The proof splits subsets by whether they contain the head element, constructs
inverse maps for the Pascal decomposition, and inducts on the ambient size and
chosen size. The empty cases prove uniqueness or impossibility. The separate
`Selections` construction in `binomial.cubist` is a recursive subset encoding;
the final theorem above concerns the actual truncated-equivalence definition,
not only that encoding.

## Permutations and functions

A permutation on `Fin(n+1)` determines the image of its head. Swapping that image
with the head leaves a permutation of the remaining `n` elements. The inverse
construction reinstates the head and undoes the swap, yielding
`Permutations(n+1) ≃ Fin(n+1) × Permutations(n)` and the factorial recurrence.

The equality lemmas prove that inverse laws and coherence do not add extra
multiplicity for maps between sets. Thus the final result counts the full
`Equiv` records, not merely an informal collection of forward maps.

A function on `Fin(n+1)` consists of its head value and a function on `Fin(n)`.
Combining this split with finite products gives the power recurrence. Both
constructions provide inverse maps and prove their inverse laws.

## Assumptions

Function and permutation counting use only `lib_funext` (function
extensionality). The general binomial count uses:

- `lib_funext`
- `lib_Trunc` (the original truncation type constructor)
- `lib_trunc_intro`
- `lib_trunc_is_trunc`
- `lib_trunc_elim` (elimination of truncation into propositions)

The literal Unit-sum example additionally uses `lib_univalence`.
These are per-result dependencies; the import closure can contain other unused
axioms. None of these results requires excluded middle or the axiom of choice.

**Truncation interface correction:** the original library accidentally required
`U -> P` instead of `A -> P`, for `A : U`. The Rust construction and the generated
axiom library now use the corrected `lib_trunc_elim` axiom. All bundled copies
have been regenerated. In [truncation.cubist](../../archive/first-library/truncation.cubist),
`mere_eliminate` is a checked definition wrapping that library axiom; it is no
longer a separate axiom. The result dependency list links to `lib_trunc_elim`.

## Source map

| Source | Contents |
| --- | --- |
| [equivalences](../../archive/first-library/equivalences.cubist) | Bijections, sums, products, and the full equivalence interface |
| [finite](../../archive/first-library/finite.cubist) | Iterated Unit sums, finite sums, decidable equality and setness |
| [function_counting](../../archive/first-library/function_counting.cubist) | Products and function counts |
| [finite_cancellation](../../archive/first-library/finite_cancellation.cubist) | Swaps, cancellation of one element, uniqueness of cardinality |
| [bijection_equality](../../archive/first-library/bijection_equality.cubist) | Extensional equality and uniqueness of inverse/coherence data |
| [permutations](../../archive/first-library/permutations.cubist) | Permutation decomposition and factorial count |
| [truncation](../../archive/first-library/truncation.cubist) | Explicit propositional truncation interface |
| [binomial](../../archive/first-library/binomial.cubist) | Numeric Pascal recurrence and structural selections |
| [binomial_types](../../archive/first-library/binomial_types.cubist) | Rijke predicate construction and true/false fiber maps |
| [binomial_pascal](../../archive/first-library/binomial_pascal.cubist) | Checked Pascal bijection and its inverse laws |
| [binomial_counting](../../archive/first-library/binomial_counting.cubist) | Base cases, induction, final equivalences and Unit-sum example |

In the CLI, run `prove archive/first-library/binomial_counting.cubist`, then
`use finite_binomial_equivalence` and `show`. Selection and reduction commands
remain available for inspecting the compiled proof.

## Bounds and definitions

Large developments are allowed up to 4,194,304 compiled instructions. WASM allows
16,777,216 nodes per expanded expression. Shared AST and judgment storage
grows by doubling as allocation permits, without fixed count caps. The heap
starts at 16 MiB and can grow up to 4 GiB in wasm32. Depth and browser
request-time limits still apply.
These bounds do not remove the need to control expansion: theorem bodies are
boxed, and `opaque def Permutations` keeps the concept named during ordinary
normalization. Checked type conversion can open its body when needed. Explicit
`unfold` is available for inspection and computation.
