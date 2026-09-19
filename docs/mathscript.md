# MathScript

MathScript is a mathematical source language checked by the existing C kernel,
compiled to WebAssembly. Authoring uses `.proof` text, not JSON. The parser and
elaborator are untrusted: they produce ordinary checked kernel instructions.

## Read and write

Run `make serve`, then open http://127.0.0.1:8088/proof.html. Use **Read** to follow
names and **Edit** to change the source. Check with the button or Ctrl/Cmd+Enter.
While checking, the source panel shows a progress bar with completed definitions
(including imports), the current definition, and the number of kernel steps.
Audit sources report completed construction statements. The bar measures work
completed, not estimated time; it clears on success or failure.
A rejected edit leaves the last checked proof available. Source files can be
opened and saved; per-proof drafts survive navigation within the browser session.

Click a lemma, then **View source**, to open its definition. Clicking the module
name in `import primes` opens the foundation source. Click a line number in a
structured proof block to inspect its goal and local assumptions. The inspector's
Back button retraces inspections; browser Back retraces source navigation.

Clicking `<` explains `isLt(a, b)`, equivalently `(isLt(a))(b)`, and links to its
source. The definition is `le(succ(a), b)`. Other arithmetic operators also expose
their named functions. A numeral such as `2` denotes `succ(succ(0))` of type `Nat`.
The source explorer makes both notation and numeral meanings inspectable.

## Mathematical syntax

```text
def identity(A : Type, x : A) = x;

def copy(n : Nat) = induction n as k return Nat {
  zero => 0;
  succ previous => succ(previous);
};

theorem copy_of_two : copy(2) = 2 {
  exact refl(2);
}
```

A definition may have an explicit result type and a block, or an expression
whose type is inferred. All parameters have explicit types. Functions can also
be written as `fun (x : A) => body`. Application `f(a, b)` is curried.
`theorem` uses an opaque checked proof definition; `def` remains transparent for
computation. Both are checked for closure.

Use `opaque def` to keep a checked concept named during ordinary reduction:

```text
opaque def Permutations(n : Nat) = Bijection(Fin(n), Fin(n));
opaque def successor(n : Nat) = succ(n);
def folded = successor(1);
def opened = unfold(folded); // 2
```

Opacity controls **definition unfolding (delta reduction)**, not beta reduction:
`(fun (x : Nat) => succ(x))(1)` still computes. Type conversion can unfold checked
opaque definitions when necessary to compare types; the resulting judgement is
restored to the requested named type. `unfold(expression)` explicitly unfolds
its definitions and normalizes it. This is not a secrecy boundary, and an opaque
definition is not an axiom. Theorem bodies remain boxed during ordinary checking.

An explicit assumption uses `axiom name(params) : T;`. It has no proof body;
the kernel checks its type and records an `Axiom` instruction. Every result and
the inspector list the names of the axioms used by its recorded derivation,
including dependencies in types and contexts. Click an axiom to inspect it and
view its source. An imported but unused axiom does not appear in that result's
list. The module-wide count is displayed separately. The CLI's `show` command
also lists dependencies.

Types include `forall x : A, B`, `exists x : A, B`, `A -> B`, `A and B`, and
`A or B`. A pair is `(a, b)`. Its expected type supplies the dependent family;
`typed(T, expression)` provides an annotation where inference needs one.
`left(value)` and `right(value)` introduce a disjunction. `refl(x)` proves
`x = x`; `absurd(impossible)` eliminates a proof of `Void` into the expected type.

Blocks support `intro`, `let`, `obtain`, `have`, `cases`, and `exact`. See
[Euclid](../web/proofs/euclid.proof) for the complete short argument. Induction
expressions carry an explicit motive:

```text
induction n as k return C(k) {
  zero => base;
  succ ih => step;
}
```

The base has type `C(0)`. In the successor branch, `k : Nat` and `ih : C(k)` are
available, and the result must have type `C(succ(k))`. The kernel checks this
substitution, including dependencies. Expression forms of case analysis are:

```text
match either return C {
  left x => left_result;
  right y => right_result;
}

unpack pair as (x, y) return C {
  result;
}
```

`pair_induction(C, branch, pair)` performs dependent pair elimination, where
`C` is a motive on the entire pair and `branch(a, b)` proves `C((a, b))`. Its
formation, substitution, and assumption discharge use the existing kernel rules.

Equality induction is available as
`path_induction(A, motive, reflexive_case, x, y, equality)`, where the motive is a
function of two endpoints and their equality proof. The foundational symmetry,
transitivity, and congruence proofs in [primes.proof](../web/proofs/primes.proof)
show its use. The lower-level `induct`, `cases`, and `unpack` function forms remain
available for proof-producing source tools.

## Modules and validation

### Explicit universe specialization

`Type` denotes U0; `Type1`, `Type2`, and `Type3` denote the next universes.
Definitions with an `A : Type` parameter still require a small type. The
following primitives apply the original prelude axioms at an explicitly named
universe; they introduce no new axioms:

```text
truncation_at(U, A)
truncation_intro_at(U, A, a)
truncation_prop_at(U, A)
truncation_elim_at(U, A, P, proposition_proof, map)
funext_at(U, A, B, f, g, pointwise_equality)
```

`A` and the elimination target `P` must belong to `U`; `B` is a family
`A -> U`. Smaller types can be lifted, but larger types cannot be lowered.
For example, `truncation_at(Type1, Type)` is valid and
`truncation_at(Type, Type)` is rejected. A family may need an explicit lift,
such as `fun (a : A) => typed(Type1, Unit)`.

The existing prelude truncation constructor returns U0 even when its input is
large. These wrappers preserve that signature; they do not promise
universe-preserving truncation. Elimination still requires evidence that its
target is a proposition. See the [real-number foundation notes](reals.md) for
the implications and current development status.

### Source checking

`import primes;` parses and checks the entire mathematical foundation source.
It does not trust a saved proof snapshot. Human-readable interface signatures are
also checked against the resulting definitions before use. All 42 declarations
in that module are axiom-free. `euclid.proof` owns both the proposition
`InfinitelyManyPrimes` and its proof `euclid`; neither is imported from `primes`. A regression test checks that the high-level Euclid
proposition matches the independently saved original proposition after reduction.

The mathematical source backend in `tools/proofs/readable_backend.mjs` migrated
proof-producing combinators into mathematical syntax. Its output is independently
checked and can be edited as ordinary source. Kernel instruction histories are
retained separately as `*.construction.proof`; these are audit artifacts, not
claimed mathematical translations of the older catalogue.

The CLI command `prove FILE.proof` checks the source and opens the result in the
existing selection/reduction workbench. JSON remains an optional checked replay
export. Source is limited to 1 MB, nesting to 128, numerals to 256, and compiled
programs to 4,194,304 instructions. The WASM kernel allows 16,777,216 nodes
per expanded expression and limits expression depth to 256. Shared AST and
judgment storage grows by doubling as needed, without fixed count caps.
The WASM heap starts at 16 MiB and may grow up to the wasm32 address-space
ceiling of 4 GiB, subject to successful allocation; it does not reserve
that whole amount as physical memory at startup. Mathematical
checking has a 300-second inactivity timeout. Advancing kernel-step or
completed-definition counters restart it; repeated progress messages with
unchanged counters do not. Other worker requests have a 30-second timeout.

The mathematical layer covers Euclid, the circle fundamental group,
[right inverses of surjections using choice](surjections.md), and
[finite counting](finite_counting.md), including functions, permutations, and
Rijke binomial types. Ports of the
older universe-polymorphic and W-type library are still in progress. Dedicated
calculation blocks, implicit arguments, and editor completion are future work.

A named proposition can be used directly as a theorem type:

```text
def InfinitelyManyPrimes = forall n : Nat, exists p : Nat, Prime(p) and n < p;

theorem euclid : InfinitelyManyPrimes {
  intro n;
  // Construct a prime above n, then finish with exact.
}
```

`intro n;` opens the outer `forall` (or implication) of the checked goal, including through a definition name. It records the new local assumption and remaining goal for source inspection. The kernel checks the resulting function against the named proposition.

For a goal `forall A : Type, IsSet(A) -> IsSet(A)`, `intro A;` introduces
`A : Type`, then `intro setA;` introduces `setA : IsSet(A)`. The remaining goal
is `IsSet(A)`, proved by `exact setA;`. The identifier `setA` is a name you
choose; its type is inferred from the next input of the goal. `IsSet` comes
from `import sets;` and asserts that any two equality proofs with the same
endpoints are equal. Click an introduced name to see its inferred type.
