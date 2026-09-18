# Puncture graphs and loop generation

The kernel now checks the statement that **every based loop in the finite
puncture graph merely has a finite signed-word representation**. It also checks
that loop invariants preserving concatenation are determined by generator
values, and that winding numbers do not classify all loops.

These are theorems about a constructed **homotopy type**. The comparison with
continuous paths in a punctured complex domain has not been proved. Neither
the free-group normal-form theorem nor the residue theorem is asserted here.

## The type and its paths

```text
def Bouquet(A : Type) = Suspension(Unit or A);
def PunctureGraph(n : Nat) = Bouquet(Fin(n));
```

The suspension has two points, `bouquet_base` and `bouquet_tip`, a distinguished
spoke from the `Unit` label, and another edge for each label in `A`. The
generator for `a : A` goes along its edge and returns along the inverse of the
distinguished spoke. There are therefore n labelled generating loops in
`PunctureGraph(n)`.

`bouquet_map` sends these generators to any supplied family of loops in another
small type. `bouquet_map_generator` proves its computation on each generator.
The graph, generators, maps, and computation theorem require no axioms; they
use the existing higher-inductive suspension kernel rules.

The underlying set of complex numbers minus a finite set is **not** being
identified with this higher type. Its continuous paths would first have to be
related to these identity paths by a geometric comparison theorem. In
particular, removing points from a set type does not create identity loops.

## The generation theorem

[bouquet_generation.proof](../web/proofs/bouquet_generation.proof) proves:

```text
theorem every_puncture_loop_generated(
  n : Nat, p : bouquet_base(Fin(n)) = bouquet_base(Fin(n))) :
  Mere(exists word : Word(Fin(n)),
    eval_word(Fin(n), PunctureGraph(n), bouquet_base(Fin(n)),
      puncture_loop(n), word) = p)
```

`Word(A)` is a natural length together with a finite snoc list of signed
letters. A positive letter traverses its generator; a negative letter traverses
the inverse. `word_backtrack_cancels` proves that appending a letter followed by
its reverse preserves the evaluated loop.

The statement quantifies over the **actual identity loop space** of the
suspension. It does not define loops to be words and then assert that they are
words. It neither assumes generation nor introduces a free-group axiom.

The proof proceeds as follows:

1. Construct an auxiliary family on the suspension, with the existing loop
   space as its fiber at each pole. Each labelled edge acts on the fiber by
   appending a generator, using its checked half-adjoint equivalence.
2. Define the proposition that a fiber element has a word representation.
   Appending generators or inverse generators preserves this proposition.
3. Use proposition extensionality and suspension induction to extend this
   predicate over the family.
4. Transport the proof that the constant loop is represented along any loop.
5. Decode transport back to the original loop and obtain its mere word
   representation.

`bouquet_connected` separately proves mere existence of a connector from the
base to every point. `bouquet_path_generated` handles paths with arbitrary
endpoints when connectors to those endpoints are supplied: close the path to a
based loop, represent that loop, and reopen it. No simultaneous selection of
connectors is made.

The conclusion is truncated. This proof does not select a word, compute a
canonical reduced word, prove uniqueness of reduced words, or prove that the
loop space is a set. Those stronger statements require further proofs.

## Loop invariants and the eventual residue argument

[bouquet_invariants.proof](../web/proofs/bouquet_invariants.proof) proves
`bouquet_maps_determined_by_generators`. Suppose `h` and `k` map loops into a
set `G`, preserve the constant loop and concatenation, and agree on each
positive generator. If the target operation has right cancellation, then
`h(p) = k(p)` for every loop `p`.

Right cancellation determines inverse-generator values; induction on word
length determines word values; the generation theorem extends the result to
all loops. Elimination of mere word existence is valid because the equality
being proved is a proposition (`G` is a set).

The target can live in `Type1`, which accommodates complex numbers built from
our intended proposition-valued Dedekind reals. The supporting
`small_mere_eliminate` lemma uses the existing universe-lowering truncation
signature, as explained in [the real-number foundation notes](reals.md).

This is an algebraic reduction for a future residue theorem. Applying it to
integration still requires constructing the integral, proving its homotopy
invariance and concatenation laws, relating analytic contours to the graph,
and calculating the generator integrals. No integral or residue is defined by
the modules in this development.

## Winding and a checked counterexample

[puncture_winding.proof](../web/proofs/puncture_winding.proof) maps the selected
generator to our existing `S1` loop and the other generators to the constant
loop. Applying the existing circle winding map gives an integer. The source
proves that the selected generator has winding +1, its reverse has winding -1,
and other generators have winding zero. Winding is additive under concatenation.
It follows that generators are nontrivial and distinct.

[puncture_noncommutative.proof](../web/proofs/puncture_noncommutative.proof)
constructs two generators `a`, `b` and their commutator `a b a⁻¹ b⁻¹`. It proves:

- The generators do not commute.
- The commutator is not the constant loop.
- Its winding is zero around **every** one of the two labelled punctures.

Nontriviality is witnessed by a local system with three states. Generator `a`
acts by swapping states 0 and 1, and generator `b` swaps 0 and 2. Transport
around the commutator sends state 0 to state 2. The constant loop fixes state 0,
and the two states are provably distinct. This uses explicit finite permutations,
not a postulated free-group classification.

## Assumptions and modules

No kernel rules or new axiom declarations were added. The generation proof uses
the existing univalence and its computation principle, function extensionality,
and propositional truncation (constructor, introduction, propositionhood, and
elimination). It uses neither excluded middle nor choice. The noncommutativity
witness only needs univalence and its computation principle; its zero-winding
proof additionally uses function extensionality.

| Module | Purpose |
| --- | --- |
| `path_actions` | Path append equivalences, functoriality, and closing/reopening paths |
| `loop_words` | Signed words, evaluation, backtrack cancellation, and folds |
| `puncture_graph` | Labelled bouquet, generators, and generator maps |
| `bouquet_cover` | Auxiliary loop-space family and decoding |
| `bouquet_generation` | Generation of all loops and paths with connectors |
| `bouquet_invariants` | Determination of invariants by generator values |
| `bouquet_actions` | Local systems from families of equivalences |
| `puncture_winding` | Integer winding around each label |
| `puncture_noncommutative` | Nontrivial commutator with zero winding vector |

Open `proof.html?proof=bouquet_generation` or
`proof.html?proof=puncture_noncommutative` in the web source explorer. Each proof
is checked from source, and its axiom dependencies can be inspected individually.

The next geometric milestone is a constructive comparison with a plane or disk
with a finite, labelled, pairwise separated collection of points removed.
Continuity, path gluing, controlled deformations, and their comparison with the
graph remain mathematical proof obligations. A general shape modality is not
part of the current kernel and is not assumed here.
