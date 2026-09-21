# MathScript

MathScript is a mathematical source language checked by the existing C kernel,
compiled to WebAssembly. Authoring uses `.proof` text, not JSON. The parser and
elaborator are untrusted: they produce ordinary checked kernel instructions.

The [full language reference](../web/language.html) documents the current syntax,
proof statements, eliminators, universe restrictions, and axiom wrappers, with
examples. The proof workspace also includes a shorter quick reference linking
to that page. This document describes the workflow and implementation.

## Read and write

Run `make serve`, then open http://127.0.0.1:8088/proof.html. Choose a **Topic**,
then select a **Proof** from that topic's list. Browsing topics leaves your
current proof and draft in place until you choose another proof. Direct proof
links select the corresponding topic automatically. Use **Read** to follow
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
def identity(A : U0, x : A) = x;

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

Place `//` comments immediately above a declaration to document it in the
inspector, including when it is imported by another proof:

```text
// Returns its input unchanged.
def identity(A : U0, x : A) = x;
```

Consecutive comment lines form a paragraph; an empty `//` line starts another
paragraph. A physical blank line separates a file or section comment from a
declaration. Trailing comments are not used as documentation for the next
declaration. This also works for theorems, axioms, opaque definitions and
construction declarations. Documentation is displayed as plain text and does
not change the checked proof.

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
A tuple `(a, b, c, d)` is a macro for `(a, (b, (c, d)))`; the same notation
works in `obtain (a, b, c, d) = value;`. Explicit left-nesting is preserved:
`((a, b), c, d)` means `((a, b), (c, d))`. This introduces no new kernel type
or rule. Three-or-more-component tuple delimiters have macro styling; hover
to see the binary-pair expansion or click to inspect the checked tuple.
`f(a, b, c)` remains curried application; pass a tuple as `f((a, b, c))`.

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

`x =[T] y` specifies equality in the carrier `T`, while `x = y` infers it.
In particular, `A =[U] B` is equality of types `A : U` and `B : U` in the
universe `U`. With `import paths;`, `sym(p)` reverses
`p : x =[T] y` to give `y =[T] x`; it also reverses equalities of types.
`trans(p, q)` composes paths and `cong(f, p)` applies a function to a path.
These language conveniences call checked library definitions proved by path
induction and introduce no axiom. `refl(x)` supplies the reflexive path `x = x`.

Equality induction is available as
`path_induction(A, motive, reflexive_case, x, y, equality)`, where the motive is a
function of two endpoints and their equality proof. The foundational symmetry,
transitivity, and congruence proofs in [primes.proof](../web/proofs/primes.proof)
show its use. The lower-level `induct`, `cases`, and `unpack` function forms remain
available for proof-producing source tools.

## Modules and validation

### Explicit universe specialization

`U0` denotes U0; `U1`, `U2`, and `U3` denote the next universes.
Definitions with an `A : U0` parameter still require a small type. The
universe argument can also be a parameter declared as `U : Universe`.
For example, `def identity(U : Universe, A : U, x : A) = x;` is checked once
and can be specialized as `identity(U0)` or `identity(U2)`. `Universe` is a
universe-parameter sort, not an unrestricted ordinary type parameter.

The following functions specialize the library principles and their derived
operations. See [the single-axiom univalence development](univalence.md).

```text
Truncate(U, A)
TruncateIntro(U, A, a)
TruncateProp(U, A)
TruncateElim(U, A, P, proposition_proof, map)
FunExt(U, A, B, f, g, pointwise_equality)
Choice(U)(A, B, setA, setFibers, inhabited)
LEM(U)(A, double_negation)
Univalence(U)(A, B)
idtoequiv(U, A, B, path)
ua(U)(A, B, equivalence)
UnivalenceBeta(U)(A, B, equivalence, x)
UnivalenceEta(U)(A, B, path)
```

Each universe specialization is a first-class function. The two application
styles above are interchangeable. `Choice` still requires setness of the
index type and every fiber and returns only a truncated section.
`Univalence` asserts that the canonical `idtoequiv` map is an equivalence.
`ua` is its derived inverse: it accepts `Equiv(U, A, B)` and returns
`A =[U] B`. `UnivalenceBeta` and `UnivalenceEta` are derived theorems,
not separate axioms. All these operations also accept `U : Universe`.

`Equiv(U, A, B)` and `IsEquiv(U, A, B, f)` in `paths.proof` are ordinary
universe-parameterized definitions. `x =[T] y` explicitly selects the carrier
of equality; both endpoints are checked against `T`. Plain `x = y` still
infers the carrier. Neither notation asserts definitional equality.

`A` and the elimination target `P` must belong to `U`; `B` is a family
`A -> U`. Smaller types can be lifted, but larger types cannot be lowered.
For example, `Truncate(U1, U0)` is valid and
`Truncate(U0, U0)` is rejected. A family may need an explicit lift,
such as `fun (a : A) => typed(U1, Unit)`.

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
older universe-polymorphic library are still in progress. General W types now
use `W(A, B)`, `sup(T, label, children)` and `wrec(T, motive, step, tree)`.
The branch takes the label, its child function, and dependent recursive results
for all children. These elaborate to the existing checked W rules.

With `import binary_naturals;`, `0b110` denotes a binary natural number, expanding
to `binary_positive(binary_bit0(binary_bit1(binary_one)))`. `0b0` denotes
`binary_zero`. Leading zeroes are ignored; malformed digits are rejected.
There is a parser limit of 256 significant bits, subject also to kernel term
depth limits. No machine-number conversion or unary successor chain is used.
Decimal literals retain their existing unary `Nat` meaning. Import
`binary_arithmetic` for `binary_add`, `binary_mul`, `binary_of_nat` and the
axiom-free proof `binary_factorial_ten`. `radix_factorial` checks the same
generic radix algorithm at base 2 and base 10; its parameter is radix minus two.

Dedicated
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

For a goal `forall A : U0, IsSet(A) -> IsSet(A)`, `intro A;` introduces
`A : U0`, then `intro setA;` introduces `setA : IsSet(A)`. The remaining goal
is `IsSet(A)`, proved by `exact setA;`. The identifier `setA` is a name you
choose; its type is inferred from the next input of the goal. `IsSet` comes
from `import sets;` and asserts that any two equality proofs with the same
endpoints are equal. Click an introduced name to see its inferred type.

## Linearizing nested tuples

`npm run linearize:mathscript` scans the AST of every mathematical proof source
and converts right-nested pairs and `obtain` patterns to tuple notation.
It preserves left-nested pairs, function arguments, component order and comments.
Every proposed rewrite is checked against the fully expanded original AST
before any files are written, then formatted. Recorded construction sources
are skipped. Run it again and it makes no further changes.

```sh
npm run linearize:mathscript -- --check
npm run linearize:mathscript -- web/proofs/circle_group_identity.proof
```

`--check` reports remaining candidates without writing and exits nonzero if
any exist. The ordinary formatter performs this same AST-checked tuple linearization automatically.
All other formatting changes only whitespace. Programmatic callers can set
`linearizeTuples: false` for whitespace-only formatting.


### Selective conversion hints (native cubical backend)

`with_unfolding(name1, name2, ..., proof)` gives the checker a list of already
checked definitions to open during a preliminary conversion pass. It leaves
other definitions folded in that pass; normal conversion remains the fallback.
The hints apply while checking the enclosing declaration and are retained for
inspection/replay. They do not add an equality, a rewrite theorem, or an axiom.
An invalid proof stays invalid. Unlike `unfold(expression)`, this does not ask
for a fully normalized expression.

```mathscript
def identity(n : Nat) = n;
theorem identity_zero : identity(0) = 0 {
  exact with_unfolding(identity, refl(0));
}
```
