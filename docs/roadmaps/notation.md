# Notation views and literals (L2.10)

Status: roadmap, revised 2026-10-05. The direction is explicit notation
views: select a mathematical structure, then elaborate its operations as
ordinary applications. Nothing here is implemented. The syntax below is
proposed; the implementation gates at the end still need their contracts
and tests. This is an elaborator and tooling change, with no kernel rule
changes.

## Why now

Building the integers and rationals exposed four limitations:

- Numerals mean natural numbers only. A rational half is
  `rat(int(1, 0), 1)`, and arithmetic quickly becomes difficult to read.
- An unscoped `+` means the `add` in scope. Naming a function `add` can change
  an operator's meaning without declaring any notation.
- `open` binds a model's notation in a proof block; sections bind the
  notation of their model parameters. Neither provides a small expression
  scope for a concrete model in a theorem statement.
- The grammar lacks binary `-`, `/` and `^`, and goals do not consistently
  display the notation used in their source.

These are reasons to improve explicit notation scopes. They do not require
inferring a mathematical structure from an operand's type.

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
block. The proposed spellings are:

```
integers.(x + y)
rationals.(1/2 + 1/3 = 5/6)
G.(x * y)
O.(2 ^ n)
```

For several declarations, choose once:

```
using integers {
  def add_comm(x, y : Z) : x + y = y + x := int_add_comm(x, y);
}
```

The cost is one explicit choice per region, with additional qualifiers
where structures change. The first library pilots will measure that cost
before any automatic selection is proposed.

### The contracts

| Part | Contract |
| --- | --- |
| Parsing | A fixed grammar parses a file without loading its imports or executing user code. Existing expressions keep their grouping. |
| Selection | A lexical view supplies one exact binding per operator. Operand and result types do not choose another view. |
| Elaboration | Select the operation and its operand views first; elaborate ordinary applications and have the kernel check them. Missing bindings and type mismatches are errors, not reasons to try another structure. |
| Imports | Imports make named views available. They do not activate a view, extend an already defined view, or replace its bindings. |
| Printing | In the stated context, re-elaborating printed source gives a term definitionally equal to the original, preserving the selected operation and model. |

Notation cannot bypass kernel checking. A well-typed term can still be
presented misleadingly, so the printing and selection contracts matter
independently of kernel soundness. Explicit views expose the mathematical
choice; they do not promise that every operation has the meaning a reader
might assume. For example, `/` uses the selected model's declared division,
including its behavior at zero.

## L2.10a. Explicit notation views

### What a view contains

A view is elaboration metadata attached to a named declaration or a model.
It contains:

- an exact function binding for each supported operator, including the
  model arguments applied to it;
- an optional default numeral interpretation;
- an operand-view recipe for each operator argument, specified below.

A view has at most one binding for an operator. Conflicting bindings in a
view declaration are rejected, with explicit renaming or separate views
required. A theory supplies views from its declared notations and its model
projections; its inheritance and renaming determine those bindings when the
theory is declared. A child's view does not combine competing meanings by
testing operand types.

`integers` and `rationals` name existing models. `nat` will export a named
view of its ordinary arithmetic functions and natural numeral
interpretation. This does not add a primitive natural-number type or require
constructing an algebraic model for the prelude. A named view declaration's
surface syntax remains an implementation gate; its contents have the same
contract whether supplied by a module or a model.

A model need not have numerals to have notation. For example, a group's
multiplication view works on variables without defining what `3` in an
arbitrary group would mean.

### Scope and binding

`v.(e)` elaborates `e` using the selected view. `using v { ... }` selects
the same view for every declaration's statement and body in the block.
The view selector may name a model parameter or a qualified model member,
such as `A.additive.group`. Its binding is resolved normally and recorded;
the parser does not need to know whether the name denotes a view or a model.

A `using` block introduces no implicit parameters and no model field names.
Its declarations keep their ordinary names and visibility after the block;
the notation selection ends at the closing brace. A declaration referring
to a model parameter still declares that parameter normally. `open` remains
the separate facility for bringing field names into scope.

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
recipes later by normalizing operand types or comparing carriers. The
syntax for writing and inspecting recipes is an implementation gate.

Ordinary function calls have no new parameter-view inference in this
release: their arguments inherit the surrounding view unless explicitly
qualified. Inside a rational view, a function requiring an ordinary natural
literal may therefore need `f(nat.(3))`. Its expected `Nat` parameter type
checks the term but does not silently change the literal's interpretation.
Parameter-view annotations for ordinary functions may be considered after
the pilots measure this cost.

### The fixed grammar

Add binary `-`, `/`, `^`, `>` and `>=`. Keep every precedence and
associativity relationship between existing operators. In particular:

```
-p @ i       means (-p) @ i
p @ -i & j   means p @ ((-i) & j)
```

The first form reverses a path before applying it; it must not become
negation of the point on that path. Existing evidence is
[`tests/path-operators.test.mjs`](../../tests/path-operators.test.mjs) and
[`cubist-tests/path_operators.cubist`](../../cubist-tests/path_operators.cubist).

Binary `-` shares addition's precedence and left associativity; `/` shares
multiplication's. The new comparisons join the existing comparison level.
Place right-associative `^` above existing unary minus, leaving unary minus
above `@` and the interval operators. Then `-x^2` means `-(x^2)`, while a
path application used as a power's base is written `(p @ i)^2`. Call and
member syntax keep their tight binding. Parser and formatter tests must
cover these new combinations as well as the existing parses.

Arithmetic unary minus is an explicit binding in a new arithmetic view.
Legacy code keeps path reversal. In an arithmetic view, use `sym(p)` for
path reversal; `-p` does not retry as reversal if arithmetic negation fails.
Interval reversal retains its existing syntax in interval positions, and
path concatenation `++` remains a fixed language form. This release does
not move paths into an arithmetic registration table.

### Derived operations

Theories may supply derived definitions and attach notation to them. For
example, a field's division is derived from multiplication and inverse,
and a ring's subtraction from addition and negation. These definitions are
checked over the model; models do not gain redundant fields or obligations
to supply those definitions again.

Their bodies can use named operations while the view is being defined, so
constructing a view does not depend on its own unfinished notation. Derived
operations are ordinary definitions and do not add primitive fields to the
theory's generated homomorphism signature. Their elaboration and recursive
definitions use the existing checking and termination requirements.

## L2.10c. Numerals in a selected view

A view's numeral interpretation is an ordinary checked function, initially
from the library's `Nat` to the view's chosen carrier. For a ring, a derived
function sends zero to the ring's zero and successors to addition of one.
It is defined once over the model. Views without an interpretation reject
bare numerals rather than inventing an element.

The active view or an operator's declared operand recipe chooses that
function. Expected types check the resulting term; they do not choose a
different numeral adapter when two carriers happen to agree. An explicit
`nat.(3)` always uses natural numerals, including inside another view.

Outside the new syntax, legacy source keeps today's natural numerals and
existing operator rules. Within the explicit `nat` view, both operators and
numerals are fixed by that view. It has no division binding in this release,
so `nat.(1/2)` is an error. There is no rule that defaults by examining all
surrounding operators and no retry in another view after an error.

Equality remains built in. Both endpoints elaborate in their lexical or
explicitly nested views. An explicit `=[T]` supplies the carrier for
checking; otherwise an endpoint whose type is determined supplies it. If
neither endpoint determines a carrier, require an annotation. The carrier
does not change any operation or numeral binding. In particular, for
`n : Nat`, `integers.(n = 2)` is a type mismatch, not a request to switch its
literal to `Nat`. Likewise, `=[Q]` alone does not activate rational notation.

The initial representation is an interpretation applied to the existing
natural numeral term. That argument is still unary; wrapping it in one
application does not make its size constant or lift the 256 limit. Compact
literal data and larger numerals belong to L2.10f.

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

Inside an explicitly displayed `using integers` context it can omit that
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

Numeral printing recognizes an application of the selected numeral adapter
to known natural numeral data. It does not invert arbitrary functions or
guess digits from a normalized value. Reducing an interpreted numeral may
therefore produce an ordinary explicit term rather than a numeral spelling.

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

using integers {
  def add_comm(x, y : Z) : x + y = y + x := int_add_comm(x, y);
  def mixed(n : Nat, x : Z) : Z := x * int(nat.(n + 1), nat.(0));
}
```

```
import rationals;

def half : Q := rationals.(1/2);
def sum_value : Q := rationals.(1/2 + 1/3);
// A theorem's target can be rationals.(1/2 + 1/3 = 5/6).
// Its first proof uses existing explicit proof facilities, not decide.
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

Existing `open`, model-parameter sections, natural literals, name-based
operator fallback and path syntax keep their released behavior outside
the new explicit regions. In particular, adding derived negation or numeral
metadata to a theory must not silently activate arithmetic `-` or model
numerals in old `open` blocks or sections. New view metadata is consumed
only at explicit view sites during this transition.

Within a new explicit view region, legacy `open` may still bind field names;
its operator bindings do not replace the selected view. A different
arithmetic interpretation requires an explicit nested view. Entering a view
does not itself open names. These interactions need fixtures covering both
directions of nesting.

The three old custom-`add` test modules need no forced migration. The
archive and other released sources likewise keep checking unchanged. A
later retirement of the name-based fallback or old operator-binding behavior
needs a separate corpus migration and compatibility decision; it is not
hidden in this release. New examples should teach explicit views.

This extends the [core theories](core-theories.md) principle that scope
chooses operations. It also agrees with the explicit structure selection
of [computation notation](computation-notation-roadmap.md)'s `do using M`;
neither feature requires instance search.

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
| Comparison and equality | A comparison's proposition result does not select a view. A carrier annotation checks endpoints without changing their views; mismatched carriers fail. |
| Ordinary function argument | In a rational view, a function requiring a natural numeral accepts `f(nat.(3))`; an unqualified rational numeral is not silently converted. |
| Literal and qualifier refusals | A view without a numeral adapter rejects bare numerals. A nested qualifier overrides an operand recipe, but a resulting argument of the wrong type is rejected. |
| Closed goals and printing | Closed integer and rational numeral equations round-trip with their selected views. Test both standalone output and output inside a displayed view context. |
| Model identity in printing | Terms using different operations on the same carrier remain distinct after print/re-elaborate; shadowed view names are qualified. |
| Natural data in printer fallbacks | An ordinary call containing natural numeral data round-trips inside a different numeral view even when that view's carrier equals `Nat`; print `f(nat.(3))` when required. |
| Legacy paths | Existing path-operator parse tests remain unchanged, including `-p @ i` and `p @ -i & j`. Test `-x^2` and `(p @ i)^2` separately. |
| Scope compatibility | Existing `open`/section fixtures keep their meanings, and new view/legacy-open nesting follows the explicit-region rule. |

## Deferred work

### L2.10f. Richer literals and large numerals

Decimal digits and exponents, and compact binary natural data, may be
passed to declared total interpretation functions. The parser treats the
literal as data; it does not execute a user parser. Binary construction can
make the input representation logarithmic in its value without adding a
kernel primitive. It does not make normalization of ordinary unary `Nat`
results logarithmic or remove evaluation limits by itself.

This slice needs its own representation, resource limits and print-back
contract. The archive's `BinaryNat` notation is a useful pilot. Literal
interpreters that require evidence also need a specified, bounded way to
check or supply it; this release adds no proof search for such evidence.

### L2.10g. Decidable propositions

A `decide` proof statement is separate work. It needs a contract for an
explicitly supplied decision procedure, its checked proof result and its
computation budget. The notation pilots use existing proof facilities and
do not depend on this slice.

### L2.10h. Mixfix notation

Declarative mixfix may be considered when a concrete library needs forms
such as absolute values or factorials. Its effect on parsing, imports,
ambiguity and tooling needs a separate contract. Programmable parsers are
not part of L2.10; literal interpretation functions do not require them.

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

## Roadmap and implementation gates

| Slice | Content | Depends on |
| --- | --- | --- |
| L2.10a | Named and model views, expression qualifiers and declaration blocks, immutable bindings, scope/import rules and inspection; existing source unchanged | L2.4 |
| L2.10b | New operator tokens with compatible precedence; declared operand-view recipes; derived operations without new model fields | L2.10a |
| L2.10c | Numeral adapters in views, role-preserving elaboration and equality checking; explicit natural-number boundaries | L2.10a, L2.10b |
| L2.10d | Context-aware source printing, qualified fallback and round-trip checks preserving operations and model arguments | L2.10a–c |
| L2.10e | Small integer, rational and abstract-model pilots; all acceptance cases, reference updates and measurement of qualification costs | L2.10a–d |
| L2.10f | Compact binary and decimal literal data, bounded total interpretations and their printing contract | L2.10c, L2.10d |
| L2.10g | Explicit decidability and a checked, bounded `decide` proof statement | Separate proof-statement contract; not required by L2.10a–e |
| L2.10h | Mixfix notation when a library demonstrates a need | Separate grammar and tooling contract |

The explicit-view direction is chosen. Before implementation, settle and
review these concrete contracts without reopening it by default:

1. The fixed grammar for `v.(e)`, `using v`, named view declarations and
   operand recipes, including nested blocks and member selectors.
2. The representation of model-specific view metadata, inherited recipes,
   derived definitions and formal numeral roles; no recovery by carrier
   equality and no change to old `open`/section behavior.
3. Diagnostics for missing operators, absent numeral adapters, wrong
   argument types and qualifications needed at ordinary function calls.
4. The printer's supported source forms and context data, and checked
   fixtures for every acceptance case, before presenting generated goals in
   the new notation.

L2.10a–e form the first coherent delivery, developed through the small
pilots with tests and reference updates at each slice. L2.10f–h and any
automatic selection are later work; none is required to validate the
explicit-view design.
