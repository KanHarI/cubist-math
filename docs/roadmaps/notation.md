# Notation and literals (L2.10)

Status: roadmap, 2026-10-05. Nothing here is implemented. It reasons from
first principles about operators, numerals and the extensibility of syntax,
compares what other languages do, derives one design, gives each part's
motivation, and orders the work. The decisions it asks for are listed at the
end.

## Why now

Building the library's integers and rationals (#157, #158) showed where
today's notation stops:

- **Numerals are `Nat`'s only.** One half is `rat(int(1, 0), 1)`, and
  1/2 + 1/3 is `rationals.add(rat(int(1, 0), 1), rat(int(1, 0), 2))`.
  The library's purpose is mathematics read by people, and this does not
  read as mathematics.
- **`+` means whatever is named `add` in scope.** The meaning of an operator
  depends on a naming accident, not on what it is applied to. A module that
  names its own `add` changes `+` for `Nat` too, and two structures' `+`
  cannot meet in one expression.
- **Notation does not reach statements about a concrete structure.** `open`
  binds operators in a proof block, and a section only for models it takes as
  parameters. So `def comm(x, y : Z) : x + y = y + x` cannot be written,
  although statements are what readers read first.
- **The operator set is too small.** There is no binary `-`, `/` or `^`.
  Unary `-` is path reversal, so a ring has no `-x`. Ordinals' `w^2 + w + 1`
  cannot be written.
- **Goals print `G.mul(x, y)`** where the source says `x * y`, so the
  workspace shows a different text from the one written.
- **Numerals are unary.** They stop at 256, and evaluating 2^10 already hits
  the evaluator's depth limit.

## First principles

### What a notation is

A notation is an abbreviation of a term. The kernel checks the term, never the
notation, so no notation can make a false statement provable: soundness does
not depend on how notation is resolved. What notation can do wrong is subtler.
It can make a statement **mean something other than what its reader reads**.
Lean's `(1 / 2 : Nat) = 0` is the standard example: a well-typed, true
statement that a reader takes for a false one. Notation is a contract between
the source text and its reader, and the elaborator is that contract's
interpreter.

### The three jobs, and what each must guarantee

| Job | From → to | Must be | Because |
| --- | --- | --- | --- |
| Parsing | characters → a syntax tree | decidable, fast, unambiguous, and the same for every tool: the checker, the formatter, the highlighter, the file explorer, the training corpus | every tool reads files, most without checking them; a parse that needs the imports, or runs code, couples them all to the checker |
| Resolution | a tree's symbol → the function it denotes, a literal → a term | deterministic; **local**, decided by the subterm and its types; stable, so that adding an import cannot silently change existing meaning; explainable, so that the inspector can say why `+` meant `int_add` | a reader must be able to tell what a line means from the line and the types it mentions |
| Printing | a term → notation | **faithful**: what is printed elaborates back to the same term in the same place | a goal is read as a statement; if it re-reads differently, the workspace misleads |

Three further constraints come from this project:

- **The language stays small.** One mechanism should serve `Nat`, concrete
  structures and abstract models: every extra mechanism has to be learned,
  documented, tooled and taught to the learned prover.
- **The elaborator does not search.** Proof search belongs to the learned
  prover; elaboration is predictable and fuel-bounded. An operator's meaning
  must not be found by search, or its failures become the prover's noise.
- **The kernel term is what the learner sees and the checker trusts.**
  Notation is surface only: two spellings of one statement elaborate to one
  term.

### Where an operator's meaning can come from

| Source | Example | Local? | Mixes structures in one expression? | Reaches statements? | Searches? |
| --- | --- | --- | --- | --- | --- |
| Fixed by the language | `=`, `->`, `++` today | yes | no: one meaning | yes | no |
| A name in scope | `+` is the `add` in scope, today | no: any `add` in scope | no | yes, for one structure | no |
| An explicit scope | `open G;`, sections, Coq's notation scopes, OCaml's local open | no: an earlier statement decides | no: one meaning per block | only through a scope around the statement | no |
| Types, by instance search | Lean's and Coq's type classes, Agda's instance arguments | yes | yes | yes | **yes**: unification and backtracking, with their own divergence, diamonds and cost |
| Types, by a table keyed by the type's head | Haskell's instance heads without backtracking, Coq's `Bind Scope`, canonical structures | yes | yes | yes | no: one lookup |

Only the last row meets every requirement. An operand's type has a **head**: the
definition or former at its outside. `x : Z` has the head `Z`. `x : G.M`, a sort
of a model `G : Group.Model(U)`, has the head `Group.M`, with the model `G` as
its argument. A table maps an operator and a head to a function. The entry for
`*` and `Group.M` says: `Group.mul`, applied to the same model. So one
mechanism serves concrete types and abstract structures alike, which is also
how a mathematician reads `x * y in G`.

### Numerals, from the same principles

A numeral's digits are data. Its meaning is that number's image in some type:
for a ring, `n` is `one + … + one`. So a numeral has no type of its own; the
context gives one, by the type expected of it or by the other operand. Every
language below that overloads literals does the same. In this design it is
one more column of the same table: a head's **numeral interpretation**.

Faithfulness constrains the default. When nothing gives a numeral a type, it
may be `Nat` only where `Nat` has a meaning for every operator around it. So
`2 + 3 = 5` is about `Nat`, as today. But `1/2 + 1/3 = 5/6`, where nothing
gives a type, is refused ("nothing determines the type of `1/2`"), since
`Nat` has no `/`. It is never silently truncated.

### How far syntax should extend

Mathematics needs operators beyond a fixed handful: `|x|`, `n!`, `⌊x⌋`, `∑`.
Three levels of extensibility are possible, each costing more than the last:

1. **A fixed grammar with a rich operator set:** `+ - * / ^ < <= > >=` and
   unary `-`, with fixed precedence. Only their meaning extends, through the
   table. Every file parses without its imports. This covers the algebra and
   the ordinals' `w^2 + w + 1`.
2. **Declarative mixfix notations,** as in Agda and Coq: a module declares a
   pattern such as `| x |` with a precedence. Parsing then depends on the
   imports' notation tables. That is still decidable and evaluates no code,
   but every tool must read the imports before it can read a file, and
   ambiguity must be refused when a notation is declared.
3. **Programmable parsers,** as with Lean 4's macros, Racket's readers and
   Rust's procedural macros: a module defines a parser, monadic or otherwise,
   that runs while the file is read. Made safe, such a parser would be a total
   Cubist function on tokens, terminating by structural recursion, whose
   output is a syntax tree that the elaborator then checks. Even then,
   soundness is untouched but everything else pays:
   - parsing a file means evaluating code from its imports, so the formatter,
     the highlighter, the explorer and the training corpus all depend on an
     evaluator and on fuel;
   - error messages degrade;
   - one text can parse differently as its imports change.

   It also needs Cubist's syntax as a Cubist datatype, a reflection layer this
   language does not have.

The safe core of level 3 is narrower, and it is what numerals actually need: a
**literal interpretation function**. The parser hands a literal over as data,
and a declared total function turns it into a term, as Coq's number notations,
C++'s user-defined literals and Scala's `FromDigits` do. No user code runs in
the parser.

**Conclusion:** level 1 now, with literal interpretations for numerals;
level 2 when a concrete notation needs it; level 3 not.

## Prior art

### Literals

| Language | A numeral means | Without a type | Large numerals |
| --- | --- | --- | --- |
| Lean 4 | `OfNat.ofNat α n` for an instance `OfNat α n`, found by instance search; `OfScientific` for `0.5` | `Nat`, by a default instance, which gives `(1 / 2 : Nat) = 0` its meaning | the kernel computes on `Nat` literals with GMP |
| Agda | `fromNat n` from a `Number A` instance, when `FROMNAT` is bound; its `Constraint n` lets a type refuse a literal, so `5 : Fin 3` is rejected | `Nat` | the builtin `NATURAL` is bound to Haskell's `Integer` |
| Haskell | `fromInteger n` for `Num a`; `fromRational` for `0.5` | the `default` declaration's list, `Integer` then `Double`, with a warning | `Integer` is arbitrary-precision |
| Coq / Rocq | per scope: `Number Notation Z of_num_int to_num_int : Z_scope` names a function from the parsed digits, and its inverse for printing | the open scopes decide; `Bind Scope Z_scope with Z` makes an argument of type `Z` read its literal in `Z_scope` | binary `positive`, `N` and `Z` |
| Isabelle/HOL | `numeral (Bit0 (Bit1 One))`, in any type of the class `numeral` | it stays polymorphic in the class `numeral`, and a statement about it holds in every such type | binary by construction |
| Rust | integer literals are inferred | `i32`, and `f64` for floating literals | machine integers; libraries otherwise |
| Swift | any type conforming to `ExpressibleByIntegerLiteral` | `Int` | machine integers |
| C++ | `123_km` calls `operator""_km`, a user-defined literal | built-in types | per literal operator |
| Scala 3 | with generic number literals enabled, a `FromDigits` instance | `Int` | per instance |

### Operators

| Language | An operator means | Extending the operator set |
| --- | --- | --- |
| Lean 4 | a type class method, such as `HAdd.hAdd`, found by instance search; `binop%` elaborates a tree of arithmetic together and inserts coercions to a common type, so `n + x` with `n : Nat` and `x : Int` elaborates | `infixl`, `notation`, `syntax`, `macro_rules` and `elab`: programmable, import-dependent parsing; `scoped notation` is active only under `open` |
| Agda | an ordinary name with underscores, `_+_`, resolved by scope; overloading is by instance arguments or by renaming on import | any name is mixfix (`if_then_else_`), with `infixl 6 _+_` fixity declarations; parsing depends on the operators in scope |
| Haskell | a type class method; instance resolution matches instance heads and commits, without backtracking, and coherence allows one instance per type | user operators from symbol characters, with `infixl` fixities from 0 to 9; `RebindableSyntax` rebinds even literals and `do` |
| Coq / Rocq | per notation scope, opened with `Open Scope`, delimited as `(x + y)%Z`, or bound to a type with `Bind Scope`; canonical structures resolve by head symbol; type classes search | `Notation` extends the grammar, with levels from 0 to 200; "notation clutter" is a known cost |
| Isabelle/HOL | type class constants, settled by type inference; `adhoc_overloading` picks by type after inference | mixfix annotations and syntax translations |
| OCaml | no overloading: `+` for `int`, `+.` for `float`; a local open, `Float.(x + y)`, rebinds operators for a subterm | operators from symbol characters, with fixity by their first character; ppx preprocessors run code on the syntax tree |
| Rust | traits from `std::ops`, by type | no new operators; `macro_rules!` matches patterns, and procedural macros run arbitrary code at compile time |
| Swift | overloads, resolved by the type checker | custom operators in precedence groups. Overloaded operators mixed with untyped literals make type checking exponential, the known "expression too complex to be solved in reasonable time" |
| Scala | methods: the left operand's type decides; extension methods and `given` instances add more | operators are method names |
| C++ | overloads by argument types and argument-dependent lookup | no new operators |
| Racket | functions and macros | `#lang` readers replace the parser itself |

### What we take from them

1. **A literal is polymorphic, with a default,** everywhere. Silent defaults
   are the known hazard, as Lean's `1/2 = 0` and Haskell's defaulting
   warnings show. We take the polymorphism, and refuse a default wherever it
   would change a statement's meaning (L2.10c).
2. **One meaning per type.** Haskell's coherence, one instance per type, is
   what makes its overloading predictable. We take it as one table entry per
   operator and head, with conflicts refused (L2.10a).
3. **Search is the cost of the powerful systems.** Lean and Coq meet
   instance-search timeouts and divergence, and Swift's checker goes
   exponential when overloads meet untyped literals. Haskell's head matching
   without backtracking, and Coq's `Bind Scope`, select by type without
   search. We take the lookup, with no overload sets (L2.10a).
4. **Scopes converge on types.** OCaml's local opens and Coq's scopes are
   explicit but coarse. Coq added `Bind Scope` so that a scope follows a type,
   and Lean makes `scoped` notation a second tier beside type classes. We
   retire operator scopes and keep `open` for names (L2.10a).
5. **Implicit coercions buy convenience with faithfulness.** Lean's `binop%`
   inserts `↑n`, and the reader does not see the cast. We keep casts explicit
   for now (L2.10a, "Not planned").
6. **Large numerals are never unary.** Lean and Agda bind the kernel's
   numbers to big integers; Coq and Isabelle build binary numerals in the
   object language. A binary representation fits Cubist's source-declared
   `Nat`, with no kernel change (L2.10f).
7. **Literals may need evidence.** Agda's `Constraint n` refuses `5 : Fin 3`
   at the literal. An interpretation can carry a decidable condition, checked
   by computation (L2.10c, L2.10f).
8. **Extensible grammars pay in tooling.** Lean must load its imports'
   compiled environments before it can parse a file, since its syntax lives
   there; Rust's procedural macros run arbitrary code at build time, a known
   security and tooling concern; and Coq's notations crowd its grammar. Agda's mixfix-by-name is the
   most constrained declarative form. Literal interpretations, as in Coq, C++
   and Scala, are the safe slice. We take that slice, and defer mixfix until a
   library needs it (L2.10f, L2.10h).

## Relation to earlier decisions

- **Core theories (L2.4).** [core-theories.md](core-theories.md) decided that
  "an operator means one thing in a scope, chosen by `open` or `section`,
  never by the types of its operands", and deferred numerals in a model,
  type-directed overloading and instance search. This roadmap **revises the
  first decision**: an operator would take its meaning from its operands'
  types. It keeps what that decision protected: there is no instance search,
  every choice is one visible lookup, and a model's notation is still
  declared by its theory. *Why revise:* the scope rule is what leaves
  statements about concrete structures without notation and mixes nothing in
  one expression. Its purpose, avoiding hidden search, is met by the table.
- **Computation notation.** The [monadic `do` and arrow
  roadmap](computation-notation-roadmap.md) selects its monad explicitly,
  `do using M`, and is unaffected. A monad's type constructor could later key
  the same table, if that roadmap chooses.
- **The archive's binary literals.** `0b110` reads as a `BinaryNat`. It
  could become `BinaryNat`'s literal interpretation (L2.10f), one mechanism
  for both.

## The design

### L2.10a. Notation by type

**Motivation.** The failures listed at the top all have one cause: the meaning
of an operator comes from a name in scope or an explicit scope, not from what
it is applied to. Meaning by type is local, mixes structures in one
expression, reaches statements, and needs no `open`. A table keyed by heads
keeps it free of search (lessons 2–4).

- **The table.** A notation table maps `(symbol, head)` to a function. The
  symbols are the fixed operators and `numeral`. A head is a definition, a
  declared type, or a theory's sort projection such as `Group.M`.
- **Theories** register their notations against their sorts.
  `mul(x, y : M) : M notation x * y` in `Group` registers `(*, Group.M) ↦
  Group.mul`, applied to the model in the operand's type. A child theory
  registers its own sorts, inherited notations included. *Why:* a theory
  already declares its notation, and its sorts are exactly the types its
  notation is about.
- **Concrete types** register explicitly, at top level:

  ```
  notation Nat { x + y := add(x, y); x * y := mul(x, y); x < y := isLt(x, y); x <= y := le(x, y); }
  notation Z from integers;
  ```

  `notation T from m` registers, for the head `T`, every notation of `m`'s
  theory, applied to `m`. *Why:* a concrete type has no theory sort for its
  head; the declaration says once, where the type is defined, which structure
  its operators come from. This replaces `Nat`'s hard-wired fallback with the
  same mechanism everyone else uses.
- **Resolution.** For a binary operator, the elaborator infers the left
  operand, else the right, else takes the expected type. It finds the type's
  head; if the table has no entry for it, it unfolds one definition and tries
  again; the first entry found decides. The other operand is checked against
  the function's parameter type, so a numeral exponent in `w^2` is a `Nat` by
  `pow`'s signature. No entry means an error that names the operator and the
  type. *Why:* this is bidirectional elaboration as it already works for
  calls, so the operator adds one lookup, not a new algorithm. Unfolding finds
  the structure of a type written through an alias.
- **Imports.** A module's registrations are exported with it, and imports
  merge them. Two different entries for one key are refused where they meet,
  so adding an import never changes a meaning silently. *Why:* stability, the
  third guarantee of resolution.
- **Paths become registrations of the path type's head.** `-p` is `sym(p)`
  and `p ++ q` is `trans(p, q)`, so `-x` at `Z` is negation and `-p` at a path
  is reversal by the same rule. An interval's `-i` keeps its own syntax, in
  interval positions. *Why:* it resolves the clash over unary `-` without a
  second symbol, and turns two special cases into entries of one table.
- **What retires:**
  - the name-based fallback, where `+` meant the `add` in scope;
  - `open` binding operators: `open m;` keeps binding a model's field names,
    so `one_mul(x)` still reads as `m.one_mul(x)`.

  *Why:* each is a second mechanism for something the table now does.

### L2.10b. The operator set

**Motivation.** Fields need `/` and `-`, rings need unary `-`, and ordinals,
powers and polynomials need `^`; order needs `>` and `>=` beside `<` and `<=`.
A fixed set keeps parsing independent of imports (level 1); the table gives
each operator its meaning.

The fixed grammar gains binary `-`, `/` and `^`, and the relations `>` and
`>=`. Precedence, loosest first, extending today's:

```
-> < or < and < = < <= > >= < ++ < + binary- < * / < unary- < ^ < @ < | < &
```

`^` associates to the right; `-x^2` is `-(x^2)`. These are the conventions of
mathematics, which every language above keeps. Unary `-` keeps its place in
interval arguments.

**Theories may declare derived operations** with notation, as definitions
inside the theory:

```
def div(x, y : R) : R := x * inv(y) notation x / y;
def sub(x, y : R) : R := x + neg(y) notation x - y;
```

Each becomes a definition over the model, readable as `m.div` and registered
like a field's notation. A model need not provide it. `neg(x)` gets
`notation -x` the same way. *Why:* `/` and binary `-` are defined from a
field's operations, not given with them. Making them fields would burden every
model with proofs of their definitions.

### L2.10c. Numerals by type

**Motivation.** A numeral means a number in whatever structure it is about.
The integers', the rationals' and the ordinals' code cannot be written
readably without that (lesson 1). Its default must be faithful (lesson 1),
and a literal may need evidence (lesson 7).

- **Interpretation.** A numeral is checked against a type: from its context,
  from the other operand, or from the expected type. The table's
  `(numeral, head)` entry interprets it.
- **Theories** declare their interpretation as a derived operation, once,
  for example in a semiring:

  ```
  def numeral(n : Nat) : R := match n { zero => zero; succ(k) => numeral(k) + one; } notation numeral;
  ```

  *Why:* the canonical map from `Nat` is defined by the structure's own
  operations, so every model has numerals for free, and they agree with its
  `+` and `one`.
- **Concrete types** register one, as `Nat`'s identity, or through
  `notation Q from rationals;`.
- **The default.** A numeral nothing types is a `Nat` when `Nat` has a
  meaning for every operator around it, and an error otherwise.
- **Equations.** An equation takes its carrier from whichever side has a
  determined type, and `=[T]` gives it outright: `1/2 + 1/3 =[Q] 5/6`.
  *Why:* `=` is built in and takes no notation; it needs one carrier, and
  either side may be the one whose type is known.
- **Representation.** A numeral's term is `numeral(m, n)`, with `n` the `Nat`
  literal: one application whatever the size, printed back as `n`. *Why:* a
  compact term reads back faithfully, and its value computes on demand.
- **Evidence.** An interpretation may take a decidable condition on the
  literal, checked by computation, as Agda's `Constraint` does, so that a
  numeral too large for `Fin n` is refused where it is written. This is
  optional, and not needed for `Z`, `Q` or ordinals.

### L2.10d. Faithful printing

**Motivation.** A goal is read as a statement. If it prints `G.mul(x, y)`
where the source said `x * y`, or prints notation that would re-read
differently, the workspace misleads its reader and the learner's displayed
goals.

The printer reverses the table. `int_add(a, b)` prints as `a + b` when `a`'s
type has the head `Z` and `(+, Z)` maps to `int_add`, because `a + b`
elaborates back to `int_add(a, b)` there. `Group.mul(G)(x, y)` prints as
`x * y`, and `numeral(m, 3)` as `3`. A term the table does not produce is
printed as written.

### L2.10f. Literals beyond naturals (deferred)

**Motivation.** Decimal literals and large numbers are part of mathematics.
Every system above avoids unary representations at scale (lesson 6). The safe
way to read richer literals is a total function on the literal's data
(lesson 8).

- **Decimal literals.** A literal interpretation function per head: `0.5`
  is passed as its digits and exponent to `of_decimal`.
- **Large numerals.** They are passed in binary, as Isabelle's `num`, to the
  interpretation: Horner's rule with `one` and doubling. That gives terms
  logarithmic in the number, in any semiring, with no kernel change, and
  lifts the 256 limit. `Nat` itself could use the same representation.

The function is total and ordinary, and no user code runs in the parser.

### L2.10h. Mixfix notations (deferred, on demand)

**Motivation.** `|x|`, `n!` and `⌊x⌋` will be wanted once analysis and
combinatorics resume. Declarative mixfix covers them without running code
(lesson 8).

Level 2 above. Notation tables would be collected syntactically from the
imports before parsing, using a fixed symbol alphabet, with ambiguity refused
at declaration. This is not planned until a library needs it, because it makes
every tool read imports before it can read a file.

### Not planned, and why

- **Programmable or monadic parsers:** they make every tool depend on
  evaluating imported code (level 3 above). The literal-interpretation slice
  gives their benefit for literals.
- **Instance search:** it is a second, hidden search, and the elaborator does
  not search (lesson 3).
- **Implicit coercions:** casts stay explicit, as `int(n, 0)`, because an
  inserted cast changes what a statement says without showing it (lesson 5).
  An explicit cast notation can come later.

## Worked examples

```
import integers;

// Statements about a concrete structure, with no open and no section.
def add_comm(x, y : Z) : x + y = y + x := int_add_comm(x, y);
def mixed(n : Nat, x : Z) : Z := x * int(n + 1, 0);   // n + 1 at Nat, x * … at Z
```

```
import rationals;

def half : Q := 1/2;                                 // numerals and / at Q
def sum : 1/2 + 1/3 =[Q] 5/6 { decide; }             // decide: see L2.10g
```

```
import algebra;

def square_one{{U < UU0}}(G : Group.Model(U)) : G.one * G.one = G.one := G.one_mul(G.one);   // * at G.M
```

```
theory Ordinal {
  sort M : set;
  add(x, y : M) : M notation x + y;
  w : M;
  pow(x : M, n : Nat) : M notation x ^ n;
  def numeral(n : Nat) : M := … notation numeral;
  …
}

def cantor(O : Ordinal.Model(U0)) : O.M := O.w^2 + O.w + 1;   // 2 at Nat by pow, 1 at O.M
```

## Safety

- **Soundness:** unchanged. Every notation elaborates to an ordinary term,
  which the kernel checks.
- **Determinism:** one table entry per key, conflicts refused, and a fixed
  lookup order. No search, no backtracking and no overload sets, so Swift's
  exponential case cannot arise.
- **Faithfulness:**
  - printing reverses only what resolution produces;
  - a numeral is never silently a `Nat` where `Nat` gives an operator no
    meaning;
  - registrations do not shadow each other;
  - no cast is inserted.
- **Termination and cost:** parsing is unchanged in kind. Resolution is a
  lookup and a bounded number of unfoldings, each a kernel question on the
  declaration's fuel.
- **Tooling:** every file still parses without its imports. The formatter,
  the highlighter and the explorer change only for the new operator tokens.
- **The learner:** kernel terms are unchanged, and notation stays surface. One
  printed form has one meaning in its place.

## What changes for existing code

- **The archive** uses `+` and `*` on `Nat` only, so `nat`'s registration
  keeps its meaning.
- **Test modules that define their own `add` on their own types** relied on
  the name-based rule: `cubist-tests/declared_match.cubist`,
  `declared_match_operator_call.cubist` and `patterns.cubist`. Each gains a
  `notation` declaration for its type.
- **Library code using `open` for operators** keeps working when the
  operands' types are the model's sorts, as they are in `algebra`'s sections.
  Statements no longer need sections for notation.
- **The reference's text:** "+ means the `add` in scope" and "`open` binds a
  model's notation" are replaced, and so are the theories chapter's examples
  of operators under `open`.

## Roadmap

| Slice | Content | Motivation | Depends on |
| --- | --- | --- | --- |
| L2.10a | The notation table:<br>• theories register their sorts;<br>• `notation T { … }` and `notation T from m`;<br>• resolution by the operands' and expected type's head;<br>• `nat` registers `Nat`;<br>• the name-based fallback and `open`'s operator binding retire;<br>• path reversal and `++` as registrations;<br>• the three test modules migrated. | Meaning by type, locally, in statements, without search; one mechanism in place of three | L2.4 |
| L2.10b | The operator set (binary `-`, `/`, `^`, `>`, `>=`, unary `-` by type), its precedence, the formatter's and the highlighter's tokens, and derived operations with notation in theories | Fields, rings, powers and ordinals need these operators; derived operations spare models extra fields | L2.10a |
| L2.10c | Numerals by type: interpretations, the faithful default, equations' carriers, the `numeral` derived operation in `algebra`'s theories, `notation Z from integers` and `notation Q from rationals` | Numbers in every structure, read as written, and never silently `Nat` | L2.10a, L2.10b |
| L2.10d | Faithful printing with the table | Goals read as the source, and re-read the same | L2.10a–c |
| L2.10e | The library and the reference in notation: `integers`, `rationals` and `algebra`'s statements and proofs rewritten, the examples above checked | The library is the first reader of notation, and the reference teaches it | L2.10a–d |
| L2.10f | Literal interpretation functions: decimal literals, and large numerals in binary | Decimals and large numbers, without unary terms or kernel changes | L2.10c |
| L2.10g | A `decide` proof statement for decidable propositions, by computation, so that `1/2 + 1/3 =[Q] 5/6` is proved by `decide;` | Closed facts about computable structures are proved by computing them; separate from notation, listed for the example | L2.10c |
| L2.10h | Mixfix notations, on demand | `\|x\|`, `n!` and `⌊x⌋`, once a library needs them | a library that needs them |

L2.10a to L2.10e are one coherent change. They are done in order, each
slice releasing with its tests and reference. L2.10f to L2.10h are
independent.

## Decisions requested

1. **The numeral default:** a `Nat` when nothing else types it and every
   operator around it has a `Nat` meaning (recommended, keeping `2 + 3 = 5`
   as it is while refusing Lean's `1/2 = 0`), or always an error without a
   type (stricter, but it breaks every `Nat` statement written today).
2. **Conflicting registrations across imports:** refused where they meet
   (recommended, so meaning is stable), or the later import wins (convenient,
   but an import could change a meaning silently).
3. **`open`:** binds names only (recommended, one mechanism), or keeps a
   local operator override as well (a second mechanism, useful only to read a
   structure through another's notation, which a model's parents already
   allow).
4. **Path reversal and `++`:** registrations of the path type (recommended,
   which settles unary `-`), or kept as fixed syntax beside the table (unary
   `-` would then need another symbol for rings).
5. **Head lookup:** through one definition unfolded at a time, outermost
   entry first (recommended, so an alias of `Z` keeps `Z`'s notation), or the
   type exactly as written (simpler, but an alias loses its notation).
6. **Registration syntax:** `notation T { … }` and `notation T from m`, or
   another spelling.
