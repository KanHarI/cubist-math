# WNat is equivalent to Nat

Open **WNat ≃ Nat (isEquiv)** in the workbench, or run:

```text
open wnat_equiv
check WNatToNat_isEquiv wnat_to_nat_isEquiv
```

The closed theorem inhabits the existing `lib_isEquiv` definition, specialized
at universe U0, the existing W-natural-number type `lib_UNat`, primitive `Nat`,
and `wnat_to_nat`. The proof uses the definitionally unfolded W type; it does not
introduce an alternative encoding. Its inverse is `nat_to_wnat`.

## Mathematical construction

WNat is `W (i : Unit + Unit). B(i)`, where the left constructor has no children
and the right constructor has one child. The original library implements `B`
using its dependent eliminator for `Two`; the proof retains that definition.

* `wnat_to_nat` folds a left node to zero and a right node to the successor of
  its child's folded value.
* `nat_to_wnat` sends zero to `lib_zeroU`, and successor to `lib_succU`.
* `nat_roundtrip` proves `f(g(n)) = n` by dependent Nat induction.
* `wnat_roundtrip` proves `g(f(w)) = w` by dependent W induction. Function
  extensionality identifies the reconstructed child function with the original:
  Void elimination handles the zero case and Unit elimination handles successor.

The library's `isEquiv` means **half-adjoint equivalence**. Two round trips alone
are insufficient: it also requires `ap(f, eta(x)) = epsilon(f(x))`.
We derive path concatenation, inversion, naturality, cancellation, and preservation
of composition using equality induction. Then we adjust the Nat round trip:

```text
epsilon'(y) = inverse(epsilon(f(g(y))))
              · (ap(f, eta(g(y))) · epsilon(y))
```

`wnat_nat_coherence` proves the required identity using this adjusted round trip,
following the adjointification argument in the [HoTT Book, Equivalences chapter,
Theorem 4.2.3](https://github.com/HoTT/book/blob/master/equivalences.tex).
The final proof packages `(g, eta, epsilon', coherence)` into the nested Sigma
type specified by `isEquiv`.

## Axioms and replay

The saved proof contains **1,910 checked instructions and one axiom**: the
library's existing function-extensionality axiom. It does not use LEM, choice,
univalence, or a newly postulated equivalence. The generator verifies that its
single axiom is exactly the loaded `lib_funext` judgement.

[`tools/proofs/wnat_equiv.mjs`](../tools/proofs/wnat_equiv.mjs) is the readable
construction. [`paths.mjs`](../tools/proofs/paths.mjs) derives the path algebra;
[`builder.mjs`](../tools/proofs/builder.mjs) emits explicit kernel instructions
for abstraction, application, conversion, and fresh contexts. These helpers are
untrusted proof producers. All conclusions still pass through `tt_apply`.

`make proof-export` regenerates the JSON and `.math` artifacts. The generator
removes unused steps and duplicate checked judgements, then replays the result
in a fresh engine and verifies the closed theorem. Intermediate proof objects
are available via **Show intermediate steps** / `list all`.

The final term has 7,335 tree occurrences (the engine stores a shared DAG).
The workbench expression bound is now 65,536; its depth, arena, judgement,
instruction-count, and WASM memory limits remain in force.

## Kernel corrections and validation

Constructing this proof exposed three defects, corrected generally in the kernel:

1. `NatElim`, `NatCompZ`, and `NatCompS` must check the induction hypothesis
   against `P(n)` and the successor branch against `P(succ(n))`.
2. Nat beta reduction must distinguish the virtual binder levels retained by
   the recursive call from those removed around its predecessor and zero branch.
3. W beta and WComp must place the recursive child variable at index 2 under
   the kernel's node-wide binder-depth convention, and W beta must lower the
   supplied constructor arguments when leaving the original eliminator.

Native regressions accept correct dependent induction, reject incorrect branch
and hypothesis types for all three Nat rules, and compare reduction before and
after closing an external context. The W regression uses an arbitrary child
function. Original proofs and the compatibility trace are also checked; four
already-excluded W fingerprint records change as documented in
[compatibility.md](compatibility.md). WASM tests replay and verify the new
JSON and source, and Chromium tests open it in the actual workbench.
