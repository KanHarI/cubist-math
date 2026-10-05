# Notation views and literals (L2.10)

Status: roadmap, revised 2026-10-05, with [decisions](#decisions) recorded
the same day. The direction is explicit notation views: select a
mathematical structure, then elaborate its operations as ordinary
applications. Nothing here is implemented. What the decisions settle is
settled; the rest of the syntax below is proposed, and the implementation
gates at the end still need their contracts and tests. This is an
elaborator and tooling change, with no kernel rule changes.

## Why now

Building the integers and rationals exposed these limitations:

- Numerals mean natural numbers only, in unary. A rational half is
  `rat(int(1, 0), 1)`, decimals such as `2.3` and numbers such as `5i` in
  the complex numbers have no spelling at all, and arithmetic quickly
  becomes difficult to read.
- An unscoped `+` means the `add` in scope. Naming a function `add` can change
  an operator's meaning without declaring any notation.
- `open` binds a model's notation in a proof block; sections bind the
  notation of their model parameters. Neither provides a small expression
  scope for a concrete model in a theorem statement.
- The grammar lacks binary `-`, `/` and `^`, and goals do not consistently
  display the notation used in their source.
- `-` already has two meanings, reversing a path and reversing a
  coordinate. Arithmetic negation would add a third on the same token, with
  one precedence for all three.
- `Field`'s inverse is total, and its value at zero is unconstrained. Every
  model picks its own `inv(zero)`, so `x / 0` is a different arbitrary
  element in each, and a ring homomorphism between fields may fail to be a
  field homomorphism over that value alone.

These are reasons to improve explicit notation scopes. They do not require
inferring a mathematical structure from an operand's type.

## Decisions

Settled on 2026-10-05:

1. **No name-based operators.** An operator means what the selected view
   binds, and nothing else. Today `+`, `*`, `<` and `<=` fall back to
   whatever `add`, `mul`, `isLt` and `le` are in scope; that fallback is
   retired ([L2.10j](#l210j-retiring-name-based-operators)). Code that used
   it selects the natural numbers' view with `using nat;`. Where that does
   not fit, it is explicit: `nat.(a + b)`, or `add(a, b)`.
2. **`~` reverses; `-` is arithmetic.** `~p` reverses a path and `~i` a
   coordinate, replacing `-p` and `-i`
   ([L2.10i](#l210i-the-reversal-token)). `-`, binary or unary, then means only
   what a view binds.
3. **Notation is declared as it is used.** A rule's left side is written
   as the notation is used, and its right side is an ordinary term: a named
   view is `notation nat { x + y := add(x, y); … }`, and theories keep
   their `notation` clauses, extended to unary operators and derived
   operations. An operand read in another view names it in the pattern,
   `x ^ nat.(n)`. `using v;` selects a view to the end of the enclosing
   block or file. `>` and `>=` are never declared: they are `<` and `<=`
   with the operands swapped.
4. **Literals are read by the library, at compile time.** The lexer fixes a
   numeric token's extent; the selected view reads it, as a natural number
   (`numeral(n : Nat)`) or from its characters, a `Lexeme`, with a total
   parser that the kernel checks by evaluation (`literal(s : Lexeme)`).
   `1/2`, `0.75` and `5i` are single literals
   ([L2.10c](#l210c-literals-in-a-selected-view)).
5. **A field's inverse is partial.** `inv` takes evidence that its argument
   is not zero. No field's view binds `/` between variables; a rational such
   as `1/2` is a literal
   ([L2.10k](#l210k-fields-with-a-partial-inverse)).

What remains undecided is listed under [Open questions](#open-questions).

## First principles

### A carrier does not determine its structure

The library already has two commutative monoids on `Nat`:
[`nat_additive` and `nat_multiplicative`](../../library/algebra.cubist).
Their carriers are the same, but their `mul` operations are addition and
multiplication respectively. More generally, two models can have
definitionally equal carriers and different operations.

A canonical interpretation for a concrete type is a useful convention,
but it is a choice. Keeping the spelling `G.M` can preserve that choice in
some expressions; unfolding it to its carrier can erase it. A type's head
is therefore not a sufficient foundation for notation that must express
arbitrary models on the same carrier.

The first release selects the model explicitly. Types then check that the
selected operations apply, and the existing argument elaborator infers the
arguments it can determine. It does not search for a model that makes the
expression work.

### Scopes can be small and composable

An expression scope can occur in a theorem statement and inside another
expression. A declaration scope can cover a statement and its proof.
Explicit scopes are not inherently limited to one structure per proof
block. The spellings are:

```
integers.(x + y)
rationals.(1/2 + 1/3 = 5/6)
G.(x * y)
O.(2 ^ n)
```

For the rest of a file or block, choose once:

```
using integers;

def add_comm(x, y : Z) : x + y = y + x := int_add_comm(x, y);
```

The cost is one explicit choice per region, with additional qualifiers
where structures change. The first library pilots will measure that cost
before any automatic selection is proposed.

### The contracts

| Part | Contract |
| --- | --- |
| Parsing | A fixed grammar parses a file without loading its imports or executing user code. The lexer fixes a literal's extent; reading its characters is elaboration. Existing expressions keep their grouping, with `~` spelling reversal. |
| Selection | A lexical view supplies one exact binding per operator. Operand and result types do not choose another view. |
| Elaboration | Select the operation and its operand views first; elaborate ordinary applications and have the kernel check them. Missing bindings and type mismatches are errors, not reasons to try another structure. |
| Imports | Imports make named views available. They do not activate a view, extend an already defined view, or replace its bindings. |
| Printing | In the stated context, re-elaborating printed source gives a term definitionally equal to the original, preserving the selected operation and model. |

Notation cannot bypass kernel checking. A well-typed term can still be
presented misleadingly, so the printing and selection contracts matter
independently of kernel soundness. Explicit views expose the mathematical
choice; they do not promise that every operation has the meaning a reader
might assume. For example, where a view binds `/`, it is that view's
declared division, including its behavior at zero; no field's view binds it
(L2.10k).

## L2.10a. Explicit notation views

### What a view contains

A view is elaboration metadata attached to a named declaration or a model.
It contains:

- an exact function binding for each supported operator, including the
  model arguments applied to it;
- optional literal rules, specified in L2.10c;
- an operand-view recipe for each operator argument, specified below.

A named view is declared by listing its rules. Each rule's left side is
written as the notation is used; its right side is an ordinary term over the
pattern's variables:

```
notation nat {
  x + y := add(x, y);
  x * y := mul(x, y);
  x <= y := le(x, y);
  x < y := isLt(x, y);
  numeral(n : Nat) := n;
}
```

Each rule is compiled once, when the view is declared, into an ordinary
checked function, so a use is an application of that function and the
printer recognizes exactly those applications. `>` and `>=` have no rules:
`x > y` is `y < x`, and `x >= y` is `y <= x`.

A view has at most one binding for an operator. Conflicting bindings in a
view declaration are rejected, with explicit renaming or separate views
required. A theory supplies views from its declared notations and its model
projections; its inheritance and renaming determine those bindings when the
theory is declared. Its `notation` clauses are the rules, so every model of
the theory has the view, and `integers.(x - y)` needs no declaration of its
own. A child's view does not combine competing meanings by testing operand
types.

`integers` and `rationals` name existing models. `nat` will export the named
view above. This does not add a primitive natural-number type or require
constructing an algebraic model for the prelude. A named view and a model's
view have the same contract.

A model need not have numerals to have notation. For example, a group's
multiplication view works on variables without defining what `3` in an
arbitrary group would mean.

### Scope and binding

`v.(e)` elaborates `e` using the selected view. `using v;` selects the
same view for every later declaration's statement and body, to the end of
the enclosing block or file, as `open G;` does for names in a proof block.
A section groups the declarations a selection should cover, so there is no
separate `using` block. The view selector may name a model parameter or a
qualified model member, such as `A.additive.group`. Its binding is resolved
normally and recorded; the parser does not need to know whether the name
denotes a view or a model.

A `using` statement introduces no implicit parameters and no model field
names. Its declarations keep their ordinary names and visibility; the
notation selection ends with the enclosing block or file. A declaration
referring to a model parameter still declares that parameter normally.
`open` remains the separate facility for bringing field names into scope.

Nested expression and declaration scopes override the view locally. A
selected view is complete for its extensible arithmetic operators: a
missing operator is an error, with no fallback to an outer view, a function
named `add`, or another model. Fixed language forms, including equality and
path application, retain their own rules.

An explicit nested qualifier takes precedence over a surrounding operand
recipe. The resulting term must still have the operation's parameter type;
a qualifier is not a cast.

### Imports and aliases

Views are defined with their contents and exported as such. There is no
global `(operator, type-head)` registration table in this release. Another
module can define a new named view, but cannot add a binding to an existing
one by importing an extension. Two independently named views may support
the same operators on the same carrier without conflict.

Normal name resolution still applies to view selectors. Adding an
unrelated import cannot modify the contents of a resolved view; explicitly
rebinding or editing that view is a source change. The inspector and printer
retain declaration identity rather than relying on a possibly shadowed
short name.

A type alias has no effect on view selection. An explicit alias for a view
refers to the same bindings. Nothing unfolds a type in order to find a
different arithmetic interpretation.

## L2.10b. Operators, operand views and derived operations

### Select before checking arguments

Once `O` is selected, `O.(2 ^ n)` selects `O.pow` before considering the
types of `2` or `n`. The operation's ordinary signature checks its
arguments. A natural-number exponent therefore cannot select natural
exponentiation in place of the ordinal operation.

The notation declaration also records how to interpret each operand's
syntax. Typical recipes are:

| Binding in a view | First operand's view | Second operand's view |
| --- | --- | --- |
| Homogeneous `x + y`, `x * y`, `x - y`, `x / y` | current view | current view |
| Comparison `x < y` | current view | current view |
| Natural power `x ^ n` | current view | the explicitly named `nat` view |

These recipes belong to the selected binding, not globally to the token.
For instance, another explicit view could declare ordinal exponents with
its own view on both operands. A scalar action may declare distinct scalar
and vector views. That is unambiguous because the containing view has
already selected one operation; it does not introduce an overload set.

An operand recipe applies to the **whole operand expression**, not just its
digits. Thus the natural-power binding gives:

```
O.(2 ^ (2 + 3))
```

the schematic expansion:

```
O.pow(O.numeral(2), add(2, 3))
```

Here `add` denotes the exact declaration in `library/nat.cubist`, and the
digits in the expansion denote ordinary natural numeral data. The
exponent's addition and numerals use `nat`; the power and its base's
interpretation use `O`. This distinction survives even if `O.M` is
definitionally equal to `Nat`.

Recipes retain the identity of views and their model arguments. A recipe
refers to the current view or an explicitly named view, including one
supplied by a specified model projection. The theory or view declaration
records that choice; a bare carrier type is not a recipe. Do not recover
recipes later by normalizing operand types or comparing carriers.

A rule names an operand's view in its pattern, as a use would:

```
def pow(x : M, n : Nat) : M := … notation x ^ nat.(n);
```

An operand whose type is the theory's sort is read in the current view
without saying so. Any other operand must name its view, or the declaration
is refused. The sort is a variable when the theory is declared, so this
never compares carriers. How recipes are inspected remains an
implementation gate.

Ordinary function calls have no new parameter-view inference in this
release: their arguments inherit the surrounding view unless explicitly
qualified. Inside a rational view, a function requiring an ordinary natural
literal may therefore need `f(nat.(3))`. Its expected `Nat` parameter type
checks the term but does not silently change the literal's interpretation.
Parameter-view annotations for ordinary functions may be considered after
the pilots measure this cost.

### The fixed grammar

Add binary `-`, `/`, `^`, `>` and `>=`. `x > y` is `y < x` and `x >= y`
is `y <= x`; a view cannot declare them, so they never disagree with `<`
and `<=`. Keep every precedence and associativity relationship between
existing operators.

Reversal first moves to its own token, `~` (L2.10i), so `-` never has to
mean both arithmetic and reversal. `~` keeps the grouping that `-` has for
reversal today:

```
~p @ i       means (~p) @ i, as -p @ i does today
p @ ~i & j   means p @ ((~i) & j), as p @ -i & j does today
```

`~` is a fixed language form, as `++`, `&` and `|` are; no view binds it.
The existing evidence,
[`tests/path-operators.test.mjs`](../../tests/path-operators.test.mjs) and
[`cubist-tests/path_operators.cubist`](../../cubist-tests/path_operators.cubist),
moves to `~` with L2.10i and keeps its groupings.

Binary `-` shares addition's precedence and left associativity; `/` shares
multiplication's. The new comparisons join the existing comparison level.
With reversal on `~`, arithmetic unary `-` no longer needs to bind tighter
than `@`. The proposed order, from loosest, is `+ -`, then `* /`, then
unary `-`, then right-associative `^`, then `@`, as in Python's `-x**2`:

```
-x^2         means -(x^2)
-x * y       means (-x) * y
-p @ i       means -(p @ i), negating a point on a path
p @ i^2      means (p @ i)^2
```

Call and member syntax keep their tight binding. Parser and formatter tests
must cover these new combinations as well as the existing parses.

Unary and binary `-` mean only what the selected view binds. In a view that
binds no negation, such as `nat`, `-x` is an error, and nothing retries it
as reversal. Path concatenation `++` remains a fixed language form, and
this release does not move paths into a view.

### Derived operations

Theories may supply derived definitions and attach notation to them. For
example, a ring's subtraction is derived from addition and negation, and
its numerals from zero, one and addition:

```
theory CommRing extends additive : AbelianGroup(
  M := R, mul := add notation x + y, inv := neg notation -x, ...
), multiplicative : CommMonoid(M := R) {
  law mul_add(x, y, z : R) : x * (y + z) = x * y + x * z;
  def sub(x, y : R) : R := add(x, neg(y)) notation x - y;
  def of_nat(n : Nat) : R := match n {
      zero => zero;
      succ(k) => add(one, of_nat(k));
    } notation numeral;
}
```

A field's division is not among them: its inverse is partial (L2.10k), and
`x / y` has nowhere to carry the evidence that `y` is not zero. These
definitions are checked over the model; models do not gain redundant fields
or obligations to supply those definitions again.

Their bodies can use named operations while the view is being defined, so
constructing a view does not depend on its own unfinished notation. Derived
operations are ordinary definitions and do not add primitive fields to the
theory's generated homomorphism signature. Their elaboration and recursive
definitions use the existing checking and termination requirements.

## L2.10c. Literals in a selected view

A view reads a literal in one of two ways, each an ordinary checked
function:

- `numeral(n : Nat) := e` reads a plain numeral as a natural number, and no
  parser runs. For a ring, the derived `of_nat` above sends zero to the
  ring's zero and successors to addition of one; it is defined once over
  the model.
- `literal(s : Lexeme) := e`, with `e : Parsed(T)` for the view's carrier
  `T`, reads any numeric token from its characters.

A view with neither rejects literals rather than inventing an element.

### The token

The lexer fixes a numeric token's extent, without imports. A token starts
with a digit and continues with letters, digits and `_`; with `.` or `/`
only when a digit follows; and with `+` or `-` only directly after `e` or
`E` and before a digit.

| Tokens | Not one token |
| --- | --- |
| `42`, `0b1011`, `0xFF`, `1_000_000` | `2.3+5i`: three tokens, `2.3`, `+` and `5i` |
| `1/2`, `2.3`, `6.02e23`, `2.5e-3` | `p.2.1`: a digit right after `.` is a projection index |
| `5i`, `3j`, `2.5e-3i` | `0` and `1` in a coordinate position keep their meaning |

The library, the tests and the archive chain projections, as in `p.2.1`, 328
times. The parser builds them from separate tokens, so a decimal
never starts right after a `.`. Apart from `0b` literals, no source has a
digit directly followed by a letter today, so the wider shape changes no
existing parse. The formatter spaces binary operators, so a tight `e-`
occurs only inside a literal. `1/2` without spaces is one literal, as in
Scheme, Common Lisp and Clojure; `1 / 2` is division, where a view binds it.

### Reading a lexeme

The library defines `Glyph` (digits, letters, `.`, `/`, `_`, `+` and `-`),
`Lexeme`, a list of glyphs, and `Parsed(A)`, either `ok(a : A)` or
`error(position : Nat)`. For `5i`, in a view whose rule is
`literal(s : Lexeme) := complex_literal(s)`:

1. The translator builds the `Lexeme` for `5i` and evaluates
   `complex_literal` on it with the kernel's evaluator, under its step
   limit.
2. If the result is `ok(v)`, it emits a term holding the lexeme and `tt` as
   evidence that the parse succeeded. The kernel checks that evidence by
   evaluating the parse itself, so nothing new is trusted, and the term
   computes to `v`.
3. If the result is `error(k)`, the literal is refused at its `k`th
   character. An exhausted step limit is reported as such.

The parser is a total Cubist function, so it terminates. Its input is one
token whose extent is already fixed, so reading a file's structure never
runs it. A shared library module supplies small parsers, for digits,
decimals with an exponent, and suffixes, so a view's parser is a few lines:

```
notation complex {
  x + y := c_add(x, y);
  x * y := c_mul(x, y);
  -x := c_neg(x);
  literal(s : Lexeme) := complex_literal(s);
}

complex.(2.3 + 5i)
quaternions.(1 + 2i + 3j + 4k)
rationals.(1/2 + 0.75 = 5/4)
```

`complex_literal` reads a decimal and makes it imaginary when it ends in
`i`; the quaternions' parser reads `i`, `j` and `k`. The rationals' parser
reads `1/2`, `0.75` and `1_000/3`, and refuses `1/0` at its denominator.
Neither complex numbers nor quaternions are in the library; the examples
show the shape. C++'s raw literal operators and Coq's `Number Notation`,
whose parsing function may refuse, are the closest precedents; Go's `5i`
and Python's `5j` are imaginary literals.

### Choosing a rule

The active view or an operator's declared operand recipe chooses the rule.
Expected types check the resulting term; they do not choose a different
literal rule when two carriers happen to agree. An explicit `nat.(3)`
always uses natural numerals, including inside another view.

Outside the new syntax, legacy source keeps today's natural numerals and
existing operator rules until L2.10j retires them. Within the explicit `nat`
view, both operators and numerals are fixed by that view. It has no division
binding and no lexeme rule, so `nat.(1/2)` is an error. There is no rule
that defaults by examining all surrounding operators and no retry in
another view after an error.

Equality remains built in. Both endpoints elaborate in their lexical or
explicitly nested views. An explicit `=[T]` supplies the carrier for
checking; otherwise an endpoint whose type is determined supplies it. If
neither endpoint determines a carrier, require an annotation. The carrier
does not change any operation or numeral binding. In particular, for
`n : Nat`, `integers.(n = 2)` is a type mismatch, not a request to switch its
literal to `Nat`. Likewise, `=[Q]` alone does not activate rational notation.

A numeral rule's argument is the existing natural numeral term. That
argument is still unary; wrapping it in one application does not make its
size constant or lift the 256 limit. A lexeme parser can return compact
data, a mantissa and an exponent, but a carrier built from unary naturals
still meets those limits. Larger numerals belong to L2.10f.

## L2.10d. Faithful printing

A printer needs the current view, operand-view recipes, and binding
identities, as well as the term and its checking context. It uses notation
only for structurally recognized applications of the exact selected
operations, with the actual model arguments. Matching the carrier type is
insufficient.

For example, a standalone closed integer goal can print:

```
integers.(2 + 3 = 5)
```

Inside an explicitly displayed `using integers;` context it can omit that
qualifier. It must not emit an unqualified `2 + 3 = 5` in a context where
that text instead means natural arithmetic. An equality carrier annotation
alone is also insufficient when different models share that carrier.

The printer carries each declared operand view through recursive printing.
It adds nested qualifiers where needed, retains carrier annotations when
the printed endpoints cannot determine the carrier, and uses a qualified
binding when a shorter view name would be shadowed. Where a notation pattern
does not apply, it prints explicit function applications with the arguments
and annotations needed for checking. This fallback also preserves the view
of raw natural numeral data: inside another view, `f(nat.(3))` must not
become `f(3)` merely because that model's carrier equals `Nat`. A carrier
annotation cannot distinguish those numeral interpretations.

Numeral printing recognizes an application of the selected numeral rule
to known natural numeral data. It does not invert arbitrary functions or
guess digits from a normalized value. Reducing an interpreted numeral may
therefore produce an ordinary explicit term rather than a numeral spelling.
A literal read from a lexeme holds that lexeme, so it prints exactly as it
was written, `5i` or `0.75`, until reduction replaces it with its value.

The acceptance property, for representable terms and sufficient checking
fuel, is:

```
elaborate(print(term, context), context) is definitionally equal to term
```

This is verified in round-trip tests. The printer itself does not repeatedly
invoke elaboration to search for a short spelling. Truncated output and
inspector-only diagnostic forms must be marked as such, rather than
presented as replayable source.

## L2.10e. Library pilots and migration

First migrate small examples in `integers`, `rationals` and `algebra`,
including the cases in the acceptance table below. Measure the qualifiers
needed in mixed arithmetic and in ordinary function arguments. Update the
reference and inspector examples with each released slice. A library-wide
rewrite is not a prerequisite for evaluating the design.

Proposed examples, to become checked acceptance fixtures when implemented:

```
import integers;

using integers;

def add_comm(x, y : Z) : x + y = y + x := int_add_comm(x, y);
def mixed(n : Nat, x : Z) : Z := x * int(nat.(n + 1), nat.(0));
```

```
import rationals;

def half : Q := rationals.(1/2);           // one literal, read by the rationals' parser
def sum_value : Q := rationals.(1/2 + 1/3);
// A theorem's target can be rationals.(1/2 + 1/3 = 5/6).
// Its first proof uses existing explicit proof facilities, not decide.
// rationals.(1/0) is refused at its denominator.
```

```
import algebra;

def square_one{{U < UU0}}(G : Group.Model(U)) :
  G.(G.one * G.one = G.one) := G.one_mul(G.one);

// Same carrier, different operations, with no competing registrations.
def additive_product(x, y : Nat) : Nat := nat_additive.(x * y);
def multiplicative_product(x, y : Nat) : Nat := nat_multiplicative.(x * y);
```

For a future ordinal model whose view declares natural powers and a
numeral interpretation:

```
def cantor(O : Ordinal.Model(U0)) : O.M := O.(O.w^2 + O.w + 1);
def power(O : Ordinal.Model(U0), n : Nat) : O.M := O.(2 ^ n);
def next_power(O : Ordinal.Model(U0), n : Nat) : O.M := O.(2 ^ (n + 1));
```

`Ordinal` is schematic, not an existing library declaration. The first
implementation uses a small suitable model fixture to test the power
recipe; it does not depend on completing an ordinal library.

### Existing source keeps its meaning

Until L2.10j, existing `open`, model-parameter sections, natural literals
and the name-based operator fallback keep their released behavior outside
the new explicit regions. Path and coordinate reversal change spelling with
L2.10i, not meaning. In particular, adding derived negation or numeral
metadata to a theory must not silently activate arithmetic `-` or model
numerals in old `open` blocks or sections. New view metadata is consumed
only at explicit view sites during this transition.

Within a new explicit view region, legacy `open` may still bind field names;
its operator bindings do not replace the selected view. A different
arithmetic interpretation requires an explicit nested view. Entering a view
does not itself open names. These interactions need fixtures covering both
directions of nesting.

The view slices force no migration: the archive and other released sources
keep checking unchanged. Retiring the name-based fallback is decided, and is
its own slice, L2.10j, with its own migration; it is not hidden in the view
slices. Retiring `open`'s and sections' operator binding is not decided. New
examples should teach explicit views.

This extends the [core theories](core-theories.md) principle that scope
chooses operations. It also agrees with the explicit structure selection
of [computation notation](computation-notation-roadmap.md)'s `do using M`;
neither feature requires instance search.

## L2.10i. The reversal token

`~p` reverses a path, as `sym(p)` does, and `~i` reverses a coordinate, as
`flip(i)` does, replacing `-p` and `-i`. Cubical Agda writes coordinate
reversal `~ i`. The two agree: `(~p) @ i` and `p @ ~i` are the same point.
`~` takes unary `-`'s present precedence, tighter than `@`, and the lexer
does not use `~` today.

This slice comes first, before any view: it changes spelling, not meaning,
and it frees `-` for L2.10b. The change is small:

| Where | Coordinates, `-i` | Paths, `-p` |
| --- | --- | --- |
| `library/` | `hlevels`, `contractible_maps`, `univalence` | `univalence` |
| `cubist-tests/` | `path_operators`, `printer_lint` | `path_operators` |
| `archive/` | none | none |

That is 17 coordinate and 9 path uses, against 55 uses of `flip` and 904
of `sym`. Beyond them, the reference pages `cubical.html` and `paths.html`
describe `-`, `tests/path-operators.test.mjs` tests its parses, the goal
printer writes a reversed coordinate as `-i`
([`web/cubical-source-text.mjs`](../../web/cubical-source-text.mjs)), and
the translator's messages name `-i`.

It lands in two commits, as the retirement of `cases` did: first `~` is
accepted beside `-`, and every source moves to it and is checked while `-`
still parses; then `-` stops reversing, with a message naming `~p` and `~i`.
The rewrite that reads historical sources in today's syntax
([`web/cubist/legacy-syntax.mjs`](../../web/cubist/legacy-syntax.mjs)) may
turn `-` into `~` only for revisions before the swap, because arithmetic
`-` returns with L2.10b. Until then, unary `-` is an error.

## L2.10j. Retiring name-based operators

Today `x + y` means `add(x, y)` for whatever `add` is in scope, and `*`,
`<` and `<=` likewise mean `mul`, `isLt` (or `succ(x) <= y` through `le`)
and `le` ([`web/translator/translate.mjs`](../../web/translator/translate.mjs)).
Naming a function `add` changes what `+` means without declaring any
notation. After this slice an operator means only what the selected view,
an `open` or a section binds. Anywhere else it is an error that suggests
`using nat;`.

Once the `nat` view exists (L2.10a–c), the slice lands in two commits, as
L2.10i does:

1. Every module that relies on the fallback gains `using nat;` after its
   imports. Where that does not fit, a use becomes explicit, `nat.(a + b)`
   or `add(a, b)`. The migration is checked while the fallback still
   exists, so every declaration elaborates to the same term.
2. The fallback is removed.

The three test modules that declare their own `add`
([`patterns`](../../cubist-tests/patterns.cubist),
[`declared_match`](../../cubist-tests/declared_match.cubist) and
[`declared_match_operator_call`](../../cubist-tests/declared_match_operator_call.cubist))
move to explicit calls or a view of their own. How a section or `open`
inside a `using nat;` region binds operators must be settled first
([open question 2](#open-questions)).

## L2.10k. Fields with a partial inverse

`Field`'s inverse is total today, `inv(x : R) : R`: `mul_inv` assumes `x`
is not zero, and nothing is said of `inv(zero)`. It becomes partial. A
generated `Hom` requires every operation to take and return sorts
([`web/cubist/morphisms.mjs`](../../web/cubist/morphisms.mjs)), so an
operation `inv(x : R, nonzero : x = zero -> Void) : R` would cost `Field`
its homomorphisms. Invertibility becomes a law instead, and `inv` is
derived from it:

```
theory Field extends CommRing {
  law inverses(x : R, nonzero : x = zero -> Void) : exists y : R. x * y = one;
  law zero_ne_one : zero = one -> Void;
}

section {{U < UU0}}(F : Field.Model(U)) {
  computable def inv(x : R, nonzero : x = zero -> Void) : R := inverses(x, nonzero).1;
}
```

- `exists` is a dependent pair, so `inv` computes.
- The law is a proposition, as a law must be, because inverses in a
  commutative ring are unique and `R` is a set. The library proves that
  once.
- Being a field becomes a property of a ring, so `Field.Hom` is
  `CommRing`'s, which is the right notion.
- Division between variables is `div(x, y, nonzero)`, and no field's view
  binds `/`. The rationals' literals (L2.10c) write `1/2` without evidence,
  because their parser checks the denominator.

This changes [`library/algebra.cubist`](../../library/algebra.cubist) and
the rationals' model in
[`library/rationals.cubist`](../../library/rationals.cubist). It does not
depend on views and can land before them.

## Acceptance cases

These are implementation requirements, not claims that this documentation
change implements or passes them.

| Case | Required result |
| --- | --- |
| Two models with the same carrier | `nat_additive.(x * y)` and `nat_multiplicative.(x * y)` expand to their respective operations. Type aliases do not switch them. |
| Statements and nested views | A concrete-model theorem uses notation in its signature; nested views can mix structures when the selected functions' types allow it. |
| Import stability | Adding an unrelated view, including another view on the same carrier, cannot alter an already selected view. No imported extension mutates its bindings. |
| Missing operation | An operator missing from an explicit view fails even when an outer view or a local `add` could provide one. |
| Heterogeneous power | `O.(2 ^ n)` uses `O.pow`; `O.(2 ^ (n + 1))` uses natural addition in the exponent. No exponent type selects the outer operation. |
| Equal carriers, distinct numeral roles | A fixture with a model carrier definitionally equal to `Nat` retains the model adapter for the base and the natural adapter for the exponent. |
| Inherited recipes | An inherited, renamed operation rebinds its current-view role to the child's selected view while preserving an explicitly named `nat` role's declaration identity. |
| Comparison and equality | A comparison's proposition result does not select a view. `x > y` elaborates as `y < x`, and a view that declares `>` is refused. A carrier annotation checks endpoints without changing their views; mismatched carriers fail. |
| Ordinary function argument | In a rational view, a function requiring a natural numeral accepts `f(nat.(3))`; an unqualified rational numeral is not silently converted. |
| Literal and qualifier refusals | A view without literal rules rejects literals. A lexeme parser's error refuses the literal at its position, as for `rationals.(1/0)`. A nested qualifier overrides an operand recipe, but a resulting argument of the wrong type is rejected. |
| Lexemes | Tokens split as L2.10c's table says: `2.3+5i` is three tokens, `p.2.1` still projects, and `0` and `1` in a coordinate position keep their meaning. A literal read from a lexeme prints as that lexeme. |
| Closed goals and printing | Closed integer and rational numeral equations round-trip with their selected views. Test both standalone output and output inside a displayed view context. |
| Model identity in printing | Terms using different operations on the same carrier remain distinct after print/re-elaborate; shadowed view names are qualified. |
| Natural data in printer fallbacks | An ordinary call containing natural numeral data round-trips inside a different numeral view even when that view's carrier equals `Nat`; print `f(nat.(3))` when required. |
| Reversal | After L2.10i, `~p @ i` and `p @ ~i & j` group as `-p @ i` and `p @ -i & j` did, and check to the same terms. `-x^2`, `-x * y`, `-p @ i` and `p @ i^2` follow the arithmetic order of L2.10b; `-p` on a path is an error, not reversal. |
| Scope compatibility | Existing `open`/section fixtures keep their meanings, and new view/legacy-open nesting follows the explicit-region rule. |
| No name-based operators | After L2.10j, `x + y` outside any view, `open` or section is an error that suggests `using nat;`, even where a function named `add` is in scope. |
| Partial inverse | A field's `inv` requires evidence that its argument is not zero; `Field.Hom` is generated as before; the rationals' literals need no evidence. |

## Deferred work

### L2.10f. Large numerals

L2.10c reads literals of any shape; what remains is their size. Compact
binary natural data can make a numeral's input logarithmic in its value
without adding a kernel primitive. It does not make normalization of
ordinary unary `Nat` results logarithmic or remove evaluation limits by
itself. This slice needs its own representation, resource limits and
print-back contract. The archive's `BinaryNat` notation is a useful pilot.

### L2.10g. Decidable propositions

A `decide` proof statement is separate work. It needs a contract for an
explicitly supplied decision procedure, its checked proof result and its
computation budget. The notation pilots use existing proof facilities and
do not depend on this slice.

### L2.10h. Notation rules

Proposed, not decided. Forms that are neither operators nor single tokens,
such as a surreal number's cut `{0 | 1}`, absolute values or big sums,
would be further rules in a view. A rule is a pattern over the existing
tokens with typed holes, including repeated holes (`l : No, ...`, read as a
list) and binding holes (`sum x < n, body`, with `body : Nat -> R`),
compiled into an ordinary checked function. It may carry a side condition,
`when ok : d` with `d : Decidable(P)`, whose evidence the elaborator
supplies by evaluating `d`, as for a lexeme's parse:

```
notation surreals {
  x + y := s_add(x, y);
  numeral(n : Nat) := s_of_nat(n);
  { l : No, ... | r : No, ... } := finite_cut(l, r, ok) when ok : ordered(l, r);
  w := omega;
}

surreals.({0 | 1} + 1 = {1 | 2})
```

Parsing would never run user code: rules are data for one fixed parser,
which reports an ambiguous use as an error, as Agda does. A use is an
application of the rule's function, so it cannot capture names, and the
printer recognizes it as it does an operator. The cost is the parsing
contract: inside a view's region, parsing needs that view's rules. A tool
can read them from the imported source without checking or running it,
provided every view selector has a declared type. Programmable parsers are
not part of L2.10.

### Optional automatic selection, after the pilots

No type-driven view selection is needed for L2.10a–e. If measured use shows
that explicit qualifiers are too costly, a later proposal may let a type's
defining module supply one canonical view. That proposal must specify:

- ownership: the type and its canonical view arrive together; a downstream
  import cannot add an earlier alias match or replace the choice;
- aliases: what they inherit, and whether a distinct choice requires a new
  named view rather than another registration;
- the precise operation signatures and positions that can determine a
  choice, including heterogeneous arguments and proposition-valued results;
- ambiguous cases, where the author supplies an explicit qualifier rather
  than the elaborator trying candidate models;
- printing that retains the selected model even for equal carriers.

A per-registration rule saying which operand selects it is not sufficient:
the elaborator would need to select the registration before knowing which
operand to inspect. Restricted protocols or additional explicit evidence
must settle that circularity. Automatic selection has a separate review
gate and remains optional. Explicit views are always available.

## Open questions

1. **Numerals outside any view.** A numeral outside any view reads as
   whatever `Nat` is in scope, as `+` reads as whatever `add` is. Should
   that reading retire with the operator fallback in L2.10j? Recommended:
   yes. `using nat;` covers both.
2. **Sections and `open` inside a view region.** A legacy `open` inside a
   view region binds names, not operators. With `using nat;` at the top of
   `library/algebra.cubist`, its sections' `*` would then be the naturals'.
   Recommended: a section's model parameter and an `open` select their
   model's view, innermost first, so that L2.10j's migration leaves
   sections as they are. This must be settled before L2.10j.
3. **Notation rules.** L2.10h is proposed, not decided.
4. **The arithmetic order.** L2.10b proposes unary `-` between `*` and `^`,
   and `^` looser than `@`.

## Roadmap and implementation gates

| Slice | Content | Depends on |
| --- | --- | --- |
| L2.10a | Named views (`notation v { … }`) and model views, `v.(e)` and `using v;`, immutable bindings, scope/import rules and inspection; existing source unchanged | L2.4 |
| L2.10b | Binary `-`, `/`, `^`, and `>`, `>=` derived from `<`, `<=`; arithmetic unary `-`; operand views named in patterns; derived operations without new model fields | L2.10a, L2.10i |
| L2.10c | Literal rules, `numeral(n : Nat)` and `literal(s : Lexeme)`; the numeric token's shape; `Glyph`, `Lexeme`, `Parsed` and shared parsers; evidence checked by evaluation; role-preserving elaboration and equality checking | L2.10a, L2.10b |
| L2.10d | Context-aware source printing, lexemes included, qualified fallback and round-trip checks preserving operations and model arguments | L2.10a–c |
| L2.10e | Small integer, rational and abstract-model pilots; all acceptance cases, reference updates and measurement of qualification costs | L2.10a–d |
| L2.10f | Large numerals: compact binary natural data and its printing contract | L2.10c, L2.10d |
| L2.10g | Explicit decidability and a checked, bounded `decide` proof statement | Separate proof-statement contract; not required by L2.10a–e |
| L2.10h | Notation rules: patterns with typed, repeated and binding holes, and side conditions. Proposed, not decided | Separate grammar and tooling contract; L2.10a–d |
| L2.10i | `~` for path and coordinate reversal, migrated while `-` still parses, then `-` retired as reversal | None: first |
| L2.10j | Retiring the name-based operator fallback: a `using nat;` migration, then removal | L2.10a–c; open question 2 |
| L2.10k | `Field` with invertibility as a law and a derived partial `inv`; the rationals' model | L2.4; independent of views |

The explicit-view direction is chosen. Before implementation, settle and
review these concrete contracts without reopening it by default:

1. The grammar's remaining details: nested qualifiers, member selectors,
   and the arithmetic order proposed in L2.10b. The forms of `v.(e)`,
   `using v;`, `notation v { … }` and operand views in patterns are decided.
2. The representation of model-specific view metadata, inherited recipes,
   derived definitions and literal rules; no recovery by carrier equality
   and no change to old `open`/section behavior before L2.10j.
3. Diagnostics for missing operators, absent literal rules, a lexeme
   parser's errors, wrong argument types and qualifications needed at
   ordinary function calls.
4. The printer's supported source forms and context data, and checked
   fixtures for every acceptance case, before presenting generated goals in
   the new notation.

L2.10i can land first, on its own, and L2.10k independently of views.
L2.10a–e form the first coherent delivery, developed through the small
pilots with tests and reference updates at each slice, and L2.10j follows
them. L2.10f–h and any automatic selection are later work; none is required
to validate the explicit-view design.
