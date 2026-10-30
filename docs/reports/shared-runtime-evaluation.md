# Shared runtime execution: first implementation

This is an internal EVAL3/EVAL4 query implementation for ordinary data. No
checker, REPL or page uses it yet. It returns observations, not kernel evidence
or full typed normal forms. Cubical execution, deep typed readback and the
rational full-normalization gates remain open.

Update of 2026-10-26: the REPLs and `print(evaluate(e))` now compute value
forms through this query ([REPL integration](runtime-repl-evaluation.md)),
which adds a synchronous `observeNow` and extends the observations below to
the kernel's weak head: η, partially applied constructors with their arity,
level functions, path abstractions and types. Update of 2026-10-28: the
supported signature fragment includes the point constructors of higher and
truncated declared types, with their eliminators' clauses for them, by the
same descriptors and the same elimination rule as ordinary data
([higher sorts' point constructors](runtime-repl-evaluation.md#higher-sorts-point-constructors));
path constructors, the squash among them, stay unsupported. Since
[#324](https://github.com/KanHarI/cubist-math/pull/324) the query copies
no closure when it is made: it reads each node, definition and signature
from the kernel when its walk first demands it, counted in its work and
cells, and definition and constructor types are no longer copied for
typed readback. It holds the kernel to do so, and a read after any call
that can move the kernel's handles (a checkpoint's rollback or commit, or
freeing the session, however it is made, as the bridge's `cb_generation`
tells) fails as `expired`; what it copied and computed before stays
observable
([report](runtime-repl-evaluation.md#the-query-copies-only-what-the-walk-reaches)).
Update of 2026-10-29: the query reads its values back into closed kernel
terms, W1 of [typed readback](../roadmaps/runtime/typed-readback.md), with
the correspondence it implements ([below](#typed-readback-w1)); no checker,
REPL or page reads a value back yet. Update of 2026-10-30: W2 reads back
in production, inside the query: a node the runtime does not execute, which
an observation reported unsupported, is now read back and its weak head
asked of the kernel, and the walk goes on
([the fallback per node](#the-fallback-per-node-w2)). The rest of this
report describes the query as #289 added it.

## Boundary and representation

`RuntimeQuery(kernel, judgement, options)` accepts an existing typing judgement
with empty context. Context is checked before execution, including assumptions
that computation would ignore. The query copies the reachable syntax graph,
checked definition dependencies and admitted signature descriptors before
running. Definition and constructor type syntax is retained for future typed
readback; ordinary execution uses the compiled arity descriptors rather than
traversing those types. After this snapshot it holds no live kernel handles;
later kernel disposal or declaration transactions cannot change its values.
Snapshot indices are meaningful only inside that query. The `signature` number
in a constructor observation is its snapshot-time index; it must not be treated
as an index into a subsequently mutated kernel or another query.

The root and observed fields have opaque query-local handles. There is no
public operation to apply arbitrary unchecked arguments. `observe(handle,
{signal, milliseconds})` forces only enough computation to expose a saturated
constructor, pair, injection, Unit value or function. Lambdas, level lambdas,
partially applied constructors, unapplied eliminators and lifted recursive
hypotheses uniformly observe as `{kind: "Function"}` without a public domain or
application operation. Types, motives, function bodies and constructor fields
remain suspended. A handle to an annotation preserves its computation; it does
not imply this fragment can execute that annotation. Unsupported demand has an
explicit `unsupported` outcome, with no native fallback or repeated restart.
`dispose()` invalidates every escaped handle.

Syntax thunks contain code and a lexical environment. Application binds the
argument thunk in the function's environment; it does not substitute through
the body or annotations. Each thunk caches its successful value. Updating a
thunk drops its old code/environment edges. Definitions share one root thunk
per definition identity per query, including when identical definition
references are stored at different syntax handles. Environments are linked and
lookups are budgeted one link at a time. Failed forces reset pending cells;
already completed siblings remain valid. A concurrent observation on the same
query is rejected.

## Reduction correspondence for the fragment

Interpret an environment as simultaneous, capture-avoiding substitution of the
terms represented by its bindings. A syntax thunk represents its code under
that substitution; an application thunk represents application of its two
represented terms. This interpretation is a semantic argument, not an
implementation that expands the substitution.

- Lambda application extends the saved environment, implementing beta.
  Lexical lookup chooses the nearest binding; entering a closure does not
  use the caller's environment. Level application uses the analogous rule.
- Pair projections, sum elimination and Unit elimination select the
  corresponding fields/branches of their represented values. They need not
  force an unused sibling, motive or annotation.
- A constructor retains its admitted signature, index, instance and argument
  thunks. Its arity comes from admitted metadata, not a source name or a
  special natural-number layout.
- Ordinary elimination selects the constructor's clause, applies all data
  fields and recursive positions in the admitted order, then supplies the
  induction hypotheses. A first-order position `q` receives `elim(q)`.
  A position with type `Pi y1 ... yn. S` receives a closure representing
  `lambda y1 ... yn. elim(q(y1, ..., yn))`. Its implementation accumulates
  those arguments without forcing the position early.
- Returning a completed thunk replaces its suspended representation by the
  corresponding value. Other references keep the same cell and therefore
  share this computation. Pending computations are never cached as values.

The machine uses a loop and continuation array for all these transitions;
recursive eliminations do not recurse on the JavaScript stack. The supported
signature fragment is untruncated ordinary declared data with term-valued
recursive positions, including higher-order Pi positions. Higher constructors,
paths, composition, Glue, transport and other cubical demand are unsupported.
An unsupported constructor or recursive position is refused when demanded, not
merely because its signature occurs in an unused argument or annotation. The
snapshot supplies the metadata needed by this ordinary fragment; cubical
execution/readback will also need independent formula and higher-signature
metadata snapshots. Opaque retained cubical fields are not yet readable proof
objects, and no operation can return them as kernel evidence.

Shallow observation preserves the components of the represented weak-head
value, but is not a reconstruction of a kernel term. Complete typed readback
must additionally interpret environments in annotations and function bodies,
preserve binder scopes and validate its interaction with cubical computation.
That correspondence and implementation remain EVAL5/EVAL8 work. These
observations must not enter conversion or establish an equality.

## Resources and remaining integration work

Work and cumulative allocation counters include snapshot traversal, thunk
forces, environment lookup, continuations, constructor arguments and public
handles. The allocation unit is an abstract object/reference cell, not a byte.
Work and allocation caps are cumulative across the query. Construction, each
observation and each retained-memory walk have separate deadlines and
cancellation signals; idle time is excluded. The constructor's signal applies
to its snapshot operation. An observation's cancelled signal or elapsed
deadline does not expire the query: completed siblings remain usable and
pending cells can be retried within the remaining cumulative limits. An
exhausted work budget prevents further observations and retained-memory walks.
An allocation stop permits later operations only if they fit the remaining
cumulative limits; already cached values may need no new allocation. Disposal
invalidates the query, including results awaiting publication after a force has
completed. Execution yields after a configurable number of transitions using
Node's `setImmediate` or a browser `MessageChannel`, checking cancellation and
the deadline again on resumption. Each MessageChannel closes both ports.

Snapshot copying is synchronous to prevent native handle movement during a
copy. It checks work, allocation and time bounds, but cannot receive a new
event-loop cancellation while copying. Retained-object measurement is also
synchronous and budgeted. This responsiveness limitation needs a specified
solution before user-facing integration; the implementation does not yet
complete all EVAL4 obligations. A snapshot must not start yielding without also
protecting against rollback, compaction and disposal during the copy.

`retainedObjects()` counts reachable runtime objects separately from the copied
syntax nodes. It walks root, type and definition thunks; every observable field
remains reachable from those roots. It includes deliberately retained
annotation and certificate syntax computations. It does not estimate exact heap
bytes or peak live memory; walking the graph itself also uses temporary memory.
Whole-process memory measurements must be reported separately. Captured
environments can retain substantial work, so successful execution alone is not
evidence that memory behavior is ready for production. The default
20-million-cell cap is not a calibrated heap-byte limit. Closed-environment
pruning, memory calibration, and avoiding continuation growth for unshared tail
calls remain integration work; none is claimed solved here.

## Initial checks

`node --test tests/cubical-runtime.test.mjs` checks closed-input rejection,
capture/shadowing, ignored unsupported arguments, sharing across pair fields,
failure recovery, level application, sums/Unit, parameterized constructors,
multiple recursive positions with asymmetric field/hypothesis-order checks,
two-argument recursive hypotheses with distinguishable arguments, partial
constructor/eliminator/lift function observations, definition sharing with
syntax interning disabled, handle isolation, disposal, budgets, mid-force
cancellation, deterministic deadline recovery, disposal before a completed
force publishes, and cached observations after an allocation stop. The
MessageChannel branch is exercised in a separate Node process, including
process exit after ports close; this is not a browser integration test.
Tractable observations are compared against native full reduction.

Run `node tools/shared-evaluation-probe.mjs` to measure each of the unchanged
archive workloads in a fresh Node process (or pass `4`, `5` or `6` for one).
(Update of 2026-10-28: the archive's Euclid was deleted, and this probe with
it, in EVAL7's part two ([report](binary-euclid.md#part-two)); the library's
Euclid, over binary `Nat`, falls back from the runtime at NUM1's
compositions. The figures below remain as measured; the probe runs in a
checkout from before the deletion, such as `27c0cc38`.)
The tool records the revision, a modified-tree flag including untracked files,
runtime/kernel source hashes, Node/platform, separate
checking/snapshot/observation times, work, allocations, retained objects,
native syntax allocation and process memory. A local exploratory run on base
`89f73ea1` plus this PR's uncommitted files (`modified: true`), Node 24.13.0,
macOS arm64, runtime SHA-256
`8695e28492377655aa8ad09f1f8f2a7a0b2df10b46fe5fe6801567645ca2e000` found:

| Fixed archive workload | Result | Runtime work | Allocated cells | Maximum continuation frames |
| --- | --- | ---: | ---: | ---: |
| Prime from `euclid(4)` | 5 | 469,195 | 267,068 | 364 |
| Prime from `euclid(5)` | 11 | 28,187,972 | 15,566,576 | 1,744 |
| Prime from `euclid(6)`, 2M work limit | Controlled budget stop | 2,000,001 | 1,107,592 | 7,646 |

The successful observations allocated no native syntax. After observation, the
4 and 5 cases retained 52,498 and 3,382,827 runtime objects respectively, plus
2,933 and 2,934 snapshot nodes. These are exploratory single samples in
separate processes, not a statistically established performance baseline.
Process RSS was about 144 MiB after the 4 case and 667 MiB after the 5 case,
including each retained-graph measurement. These totals include the Node
process, the native kernel and temporary measurement memory; they are not
runtime-only retained or peak-live heap sizes. The reported maximum process RSS
is a separate process-wide high-water mark. These observations show that
eliminating native substitution chains does not eliminate memory cost. The work
count includes snapshot and observation, but precedes the retained graph walk.
The bounded case counts the attempted step that exhausted its limit. None of
these results forces the final prime certificates.

## Typed readback (W1)

W1 of [typed readback](../roadmaps/runtime/typed-readback.md), 2026-10-29,
on main `bfca6cad`, with its first two reviews' fixes on 2026-10-30, main
`b05b4c5d` merged. `RuntimeQuery.readback(handle, options)` gives the
closed kernel term a value stands for, R of the note's section 3. It is
internal: no checker, REPL or page calls it, so no value form, observation,
display or verdict changes, and no verdict will consume it (D1). The term is
admitted to the kernel's normalize queries as derived (D3, the
`derivedHandles` guard); only tests type it by instructions. The note gives
the argument; this section records what the code does, and where it reads
the note more precisely than the note's text.

### What the machine keeps

- An environment frame records the node of the function its β applied
  (`binder`): a readback telescope binds the frame as that function's
  binder, a term or level λ, at the domain written in that node.
- Term and level functions and path abstractions keep the node they were
  made from, and so does a type value, where it kept none before. A
  constructor's instance is read from its instance cell: unforced, its code
  and environment; forced, those its type value keeps. So a constructor
  value keeps no copy of its own.
- Readback reads only a query made for readback, `{ readback: true }`,
  which keeps what readback reads beyond what an observation needs:
  - of a type value's environment, the bindings its node uses: the frames
    a readback telescope of the node would bind, copied in order, each the
    parent of the next (`#pruned`). Lookup there finds what lookup in the
    whole environment found, since no frame dropped binds a variable nearer
    than the one kept for it, and a node with no children, such as `Unit`,
    keeps none;
  - after η, an observation's head, which is no cell's value, by the cell
    asked, for `readback(handle, { head: true })`; `retainedObjects`
    counts it;
  - with `{ origins: true }`, which implies `{ readback: true }`, each
    forced cell's code and environment, or an application cell's two
    cells: its origin (3.4).

  Value forms make no such query, and keep a type value's node alone: the
  bindings a type mentions can hold whole computations.

A value form keeps main's values, counters and retained objects: what a
query made for readback adds is none of its own. Main's query and a value
form's, walking the same value form, give the same value, counters and
retained objects for every one of the constructs' 156 runtime value forms
(A40, A49 and A46b among them, which paid the pruning's work when value
forms pruned too), on seven workloads the runtime computes, `unary-510`
to the wide binary-integer product, and on two recursions whose result is
a type: `traverse(100 * 100)`, down to `Unit`, and `traverse2(n, n)` at
`n = 100 * 100`, down to `Tag(n)`, each retaining 13 objects. Pruned to
the bindings its node uses, a query made for readback retains 13 for the
first too, where the environment kept whole retains 71,228; the second's
`Tag(n)` keeps `n`'s binding, which its readback reads, and with it the
computation of `100 * 100`, 71,230 objects. The evaluation baseline
(`tools/evaluation-baseline.mjs`, one cold sample per workload, at
`6ad47c39`, with main's `b05b4c5d` merged) gives every one of its 45
workloads the outcome, kernel counters, phases and runtime counters
recorded in `tests/fixtures/evaluation-baseline.json`, exactly. A frame
records the applied function's node rather than the function value:
recording the value, as the note's 3.3 words it, kept each applied
function's domain cell alive, and retained 17 to 36% more runtime objects
on those seven workloads.

### The correspondence as implemented

`R(cell)` reads in one of three modes: by value (origins off); a normal-form
readback, `{ origins: true }`, which reads forced data by value outside
every non-data part and a non-data cell by its origin; and, inside an
origin, every cell that has an origin by it, data included. A forced cell
with no origin, an eliminator or lifted hypothesis the eliminate frame made
ready, is read by value. An unforced cell is its closure, and an
application cell the application of its two cells. A normal-form readback
cannot tell an unforced cell's value data, so it reads an unforced cell,
an annotation such as a pair's type among them, as inside an origin, and
so too a constructor's instance, a type: data reaches it by value only
through forced cells. And it reads the fields of a pair that, as written,
pairs `t.1` and `t.2` of one term under one environment as inside an
origin: the kernel's `weak` contracts such a pair to `t` by syntax
(surjective pairing), which a field read by value would hide.

By value: a constructor from its index and instance cell, rebuilt one level
into a literal `Sort` that must be of the value's signature, applied to its
arguments in the kernel's order; a pair, an injection and the point from
their fields; a term or level function as the closure of the λ its symbol,
body and node's domain make, under its environment; a path abstraction as
the closure of its node with its body; a type as the closure of its node
under its environment; an eliminator rebuilt from its signature, motive and
clause cells. A lifted hypothesis is refused as `unsupported` (3.7).

`closure(code, env)`, in order:

1. a variable is the cell its nearest binding holds, as the machine's lookup
   takes it;
2. a definition whose cell is forced is that cell, by value; in a
   normal-form readback only where its value is data, and otherwise, and
   inside an origin, the reference is kept;
3. a code with no variable bound in `env` and no forced definition outside
   its term binders is the code itself;
4. a spine node (`App`, `LApp`, `Fst`, `Snd`, `PApp`), or a node no term
   binder that references a forced definition outside its term binders, is
   rebuilt one level;
5. anything else is the telescope of the frames it needs, applied to their
   cells: the nearest binding of each variable free in it and, for each
   frame, the nearest binding above it of each variable free in its binder's
   domain, outermost first.

Inside an origin no definition is read as its cell, so rules 3 and 4
consider none there.

Rebuilt one level, a node keeps its kind and payload, and each child is read
back under the same environment: a term as its closure, a level as below,
and these parts rebuilt one level in turn: a `Sort`'s parameter and level
lists and an eliminator's clause list, a list's next cell, the tubes of a
composition, a homogeneous composition, a transport and a glue value and a
tube's next one, a `Glue` type's system and a system's next piece, and the
annotations the kernel reads by node kind without reducing them, a path
application's `Path` type, an `unglue`'s and a glue term's `Glue` type and
a constructor's `Sort` instance. Variables free in a node, bound as
`ck_term_free` binds them, and the definitions it references outside its
term binders, are computed once per copied node; a definition inside a
term binder stays as written.

A level that is a variable is the level its frame binds; one with no
variable is itself; and any other is read off the kernel's weak head of the
universe at that level, closed by its telescope, which
`ck_level_instantiate` substitutes and canonicalizes.

Readback keeps its own stack, as the machine does, so a value deeper than
the host's stack is refused by the kernel's own syntax depth (K344) when its
term is built: a unary 10,000 fails there, as does the pair of two 510s.
Its work and cells count against the query's limits.

The memo is by mode, of cells and of closures by environment and code. An
entry is stable when every cell it read was forced and every definition the
closure rules consulted has a forced cell; only a stable entry answers a
later readback, and within one readback every entry is reused, so a cell
reached twice is one handle. The machine never forces a level cell, nor
does a value form force a pair's or an injection's type cell, so entries
that read one are unstable.

### Where the code reads the note more precisely

1. **Definitions under origins.** Read literally, 3.3's rule 2 makes a
   forced definition, inside an origin, its cell's origin: the definition's
   body, not its reference. Then `(fun x => (tt, x.1))(certPair(tt))` would
   fold to `fun y => tt`, not the `certPair(tt).1` that 3.4 shows and that
   the kernel's folded normal form keeps. 3.4 requires a closure of an
   origin to β-reduce to the kernel's term at that position, which is the
   reference; so inside an origin a reference is kept, and in a normal-form
   readback a forced definition is read by its cell only where its value is
   data.
2. **A constructor's instance** is read from its instance cell, whose code
   survives forcing in the type value (above), rather than from a copy on
   the constructor value.
3. **An `unglue`'s and a glue term's `Glue` type** are rebuilt one level
   besides the two annotations 3.3 names, by 3.3's own rule for
   annotations the kernel reads by node kind: `weak` reads the first, as
   section 5 says, and the glue term's typing rule the second
   (`cc_instr_glue_term_base`). As a closure, `(λ A. Glue(A))(Unit)`, a
   glue term's annotation made its readback untypeable. Of the other
   annotations an instruction reads by kind, a pair's `Σ` and an
   injection's sum are reduced to their former by the instruction driver
   first (`former` in `web/cubical-instruction-driver.mjs`), and a
   homogeneous composition's and a transport's family by the kernel
   (`formal_family`), so they stay closures, and typed so in the tests; a
   composition's family is read by no kind check, and a path
   application's `Path` type and a constructor's `Sort` are rebuilt
   already.
4. **A frame records the applied function's node**, not the function value
   3.3 names: the node is all a telescope reads, and the value kept its
   domain cell alive (above).
5. **A type value keeps its environment only in a query made for
   readback, and there only the bindings its node uses.** 3.2 asks it to
   keep the environment it was made in, "with origins off too". Kept
   whole, a value form whose result is a type retained the whole
   computation that chose it; pruned, it still retained the computation of
   an input the type mentions, `traverse2(n, n)`'s `n`, which is exactly
   the binding readback reads. So a value form keeps none, and readback
   reads only a query made for it. The pruning is 3.5's free-variable
   sets, which the note names as what EVAL4's closed environments need for
   retention. W2, whose fallback reads back in production, decides how
   value forms switch readback on: they do not
   ([decision 1](#the-two-decisions-w1-left-to-w2)).
6. **Unforced cells in a normal-form readback.** 3.4 has data reach the
   result by value only outside every non-data part, and 3.2 an unforced
   cell read as its closure; but an unforced cell's value may be no data,
   as an annotation's is. Read with forced data inside it by value,
   `Marked(x.1)` in a constructor's instance and a pair's type lost the
   `certPair(tt).1` that the kernel's folded normal form keeps. So an
   unforced cell and a constructor's instance are read as inside an
   origin. The note's own regression of a `Box(x)` constructor whose
   instance "reads `x` by value first" thus reads it by origin; its memo
   case, one cell read in both modes, is tested by `x` itself beside
   `(fun y => y.1)(x)`.
7. **Observed heads** are kept only by a query made for readback (above),
   which the note does not say: no value form reads them.
8. **A pair of two projections of one term**, one more of the cases 3.4
   expects ("Others may remain"): `(cp(tt).1, cp(tt).2)`, with
   `cp(tt) = (fun y => tt, tt)`, folds in the kernel to
   `(fun y => tt, tt)`, since its surjective pairing contracts the pair to
   `cp(tt)`, which computes. Read with its second field by value, the
   readback `(cp(tt).1, tt)` kept the first folded. A normal-form readback
   now reads such a pair's fields as inside an origin, which keeps the
   redex; a pair whose fields project terms that are alike only after
   substitution, `x.1` and `y.2` with `x` and `y` bound to one cell, is
   not recognized, and remains a case the folded target can miss.

### Session safety

As section 7 of the note has it, a readback checks the kernel's handle
generation (`handlesHeld`) when it starts, before each write, the level's
head query included, and before it returns a handle; after any rollback or
commit it fails as `expired` and drops its memo, for a readback that would
write and for one that writes nothing, a closed code's own handle or a
memoized one. The asynchronous `observe` can hold a query across a session
operation, and its outcome there is `expired`: what was copied and computed
stays observable, and reads and readback fail. No user path holds a query
across one, so this has no diagnostic code.

### Tests

- `tests/runtime-readback.test.mjs`: capture and shadowing, with one symbol
  bound twice and with an inner domain naming the outer binder, written as
  kernel syntax since the elaborator names a shadowing binder apart; an
  unused argument never read back, nothing written; a cell reached twice
  one handle; a level argument mentioning a bound level variable, which
  comes back as `3`; typing by instructions of a closure capturing
  `A : U0` and `x : A`, of the type value of
  `(fun (A : U0) => A -> A)(Unit)`, whose full normal form is
  `Unit -> Unit`, and of a constructor of `Box(A)` read back from a closure,
  which `kernel.head` eliminates, where the same constructor with its
  instance a redex is refused, as are the domains closed one by one, and
  of a pair with a path between glue terms over a forced `f(A, a)`, whose
  `Glue(A)` annotations stay literal, and of a pair and an injection whose
  types mention a bound variable; the
  heads η computed, kept and counted only by a query made for readback,
  and readback refused on any other; a value form's query keeping no
  environment for a type value, so that `traverse(100 * 100)` and
  `traverse2(n, n)` at `100 * 100`, whose result `Tag(n)` mentions its
  input, retain 13 objects, as the runtime did before W1, not 71,230, and a
  query made for readback keeping the bindings a type uses, which read
  back to the kernel's `Tag(3)` and `Unit -> Unit`;
  the four folding regressions of the note by origin, and two more, data
  read in both modes and `Marked(x.1)` in an instance and a pair's type,
  each folding away by value, and a pair of `cp(tt).1` and `cp(tt).2`,
  written so or reached by a β, folding as the kernel's surjective pairing
  makes it fold; expiry after a rollback and after a commit; a
  lifted hypothesis refused and K344 at the 511th successor; readback's
  work and cells counted in the query's, stopping at its limits; the scaling
  test, n closures over n variables for n = 4, 8 and 16, within 3.5's bound
  and growing as n²; and the note's eighteen mutations, each a change to
  `web/cubical-runtime.mjs` at one site, the memo's at two, imported as a
  module of its own, each failing an oracle the unchanged runtime passes
  while the runtime's own walk completes; and the differential's heads
  compared past an undecided one, so that the η-produced index mutation is
  caught after two heads the kernel cannot normalize (K344).
- The differential (`tests/runtime-readback-oracle.mjs`), run where the
  value forms are checked, each by a query made for readback and otherwise
  the one the runtime makes: every value form the runtime computes is read
  back by value, its full normal form compared with the kernel's of the
  term, as are those of every head the walk observed, an undecided one
  counted apart; a query made with origins walks it again, and its
  readback's folded normal form is compared with the kernel's; and a
  readback of at most 400 nodes as a tree is typed at the term's type. Each
  normal form, and each comparison, has 2M steps.
  No comparison disagrees, and no readback is refused:
  - the constructs' 156 runtime value forms
    (`tests/evaluation-demand-marks.test.mjs`): 153 agree by value, and the
    3 whose full normal forms that test already calls slow are undecided;
    every observed head decided agrees, 13 of A46b's undecided; all 156
    fold as the kernel's folded normal forms; 144 readbacks are small
    enough to type, and type;
  - the binary contracts' 40 (`tests/runtime-evaluation.test.mjs`): 36
    agree by value and the 4 widest are undecided; every head decided
    agrees, 4 of the wide inverse's undecided; 39 fold as the kernel's,
    1 undecided; 37 type. The same file reads back its other runtime value
    forms, the points of higher sorts and the binary integers and
    rationals, among them `bint_decide` of a wide integer and `-1`, whose
    full normal form the kernel itself cannot build (K344): undecided;
  - the Cubist test modules' 97 (`tests/cubist-tests-inlined.mjs`): 94
    agree by value, 3 undecided; every head decided agrees, 1 of
    `1/2 + 1/3`'s undecided; all 97 fold as the kernel's; 88 type.

### M1, readback

`node tools/runtime-repl-probe.mjs NAME readback` makes the value form's
query for readback, and reads its root back by value after the value
form's walk, before the query is disposed of. Each workload ran in a
process of its own at `6ad47c39`, main's `b05b4c5d` merged, with a clean
tree, Node 24.13.0, macOS arm64, runtime SHA-256 prefix
`953396c045ff51a9`; `80577185` gave the same figures. Steps are
readback's own work in the query's budget; writes are its kernel syntax
calls, and the arena's growth the nodes they added, interning merging the
rest; cells, rebuilt nodes and telescope bindings are its counters; the
DAG and tree sizes are R(root)'s. Each readback took at most 7 ms.

| Workload | Value form | Readback steps | Writes | Arena growth | Memo hits | Cells | Rebuilt | Bindings | DAG | Tree |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `euclid-3` | falls back (`Comp`) | 926 | 32 | 30 | 13 | 11 | 17 | 5 | 204 | 1,747 |
| `euclid-4` | falls back (`Comp`) | 1,012 | 37 | 31 | 13 | 18 | 17 | 5 | 223 | 2,413 |
| `euclid-4-prime` | falls back (`Comp`) | 2,239 | 7 | 7 | 0 | 4 | 7 | 0 | 544 | 3,137 |
| `euclid-5-prime` | falls back (`Comp`) | 2,242 | 7 | 7 | 0 | 4 | 7 | 0 | 545 | 3,140 |
| `euclid-6-prime` | falls back (`Comp`) | 2,245 | 7 | 7 | 0 | 4 | 7 | 0 | 546 | 3,143 |
| `euclid-7-prime` | falls back, then K344 | 2,248 | 7 | 7 | 0 | 4 | 7 | 0 | 547 | 3,146 |
| `euclid-10-prime` | falls back (`Comp`) | 2,219 | 7 | 7 | 0 | 4 | 7 | 0 | 540 | 3,139 |
| `binary-factorial-40` | falls back (`Comp`) | 1,837 | 6 | 6 | 0 | 4 | 6 | 0 | 458 | 2,695 |
| `binary-rational-equal` | falls back (path constructor) | 17,173 | 731 | 421 | 254 | 330 | 251 | 149 | 2,245 | 12,487,305 |
| `count-into-510` | runtime | 4,088 | 1,021 | 255 | 0 | 511 | 0 | 0 | 513 | 1,532 |
| `unary-doubling-8` | runtime | 2,056 | 513 | 248 | 0 | 257 | 0 | 0 | 259 | 770 |
| `binary-product` | runtime | 1,049 | 261 | 130 | 0 | 131 | 0 | 0 | 136 | 392 |
| `binary-rational` | runtime | 14,850 | 575 | 378 | 205 | 252 | 194 | 129 | 2,048 | 3,036,253 |
| `binary-rational-wide-inverse` | runtime | 14,628 | 824 | 437 | 164 | 385 | 170 | 98 | 2,028 | 3,077,891 |
| `binary-rational-distinct` | runtime | 14,379 | 557 | 378 | 196 | 237 | 166 | 140 | 2,008 | 2,477,494 |
| `binary-integer-wide-product` | runtime | 6,050 | 623 | 360 | 28 | 310 | 16 | 39 | 887 | 8,851 |
| `binary-integer-distinct` | runtime | 9,457 | 406 | 234 | 30 | 337 | 299 | 43 | 966 | 38,267 |

A value form that falls back is read back as far as the runtime's walk
went, the rest as closures. `unary-510`, the pair of two 510s, is 513 deep:
its readback is refused with the kernel's K344 after 8,189 steps and 2,043
writes, as the kernel refuses to build the pair. `list-parity-200000` and
`duplicated-calls-24` stop at the runtime's allocation cap (E488), and so
do their readbacks, within two steps. `euclid-3-expecting`,
`euclid-5-expecting` and `euclid-5-folded` make no runtime query. The
rationals' terms keep their sharing: about 2,000 nodes as a DAG for 2.5 to
12.5 million as a tree. At `804841d4`, before main's merge, the Euclid
prime rows and `binary-factorial-40` read back 11 nodes fewer, in 52
steps fewer; the readback before the review's fixes gives this table's
figures on the merged tree, so main's merge, not the fixes, changed them.

## The fallback per node (W2)

W2 of [typed readback](../roadmaps/runtime/typed-readback.md), 2026-10-30,
on #337's W1 with main `d27ad60d` merged. A node the runtime does not
execute no longer abandons the value form's walk: the runtime reads it
back, asks the kernel for its weak head and goes on with that head, the
note's option c (D4). The whole walk is computed again on the kernel's head
queries only where that readback refuses. Every value form is what it was,
the constructs', the binary contracts', the Cubist test modules' prints,
the reference's examples and the evaluation baseline's 45 outcomes. No
verdict reads anything the fallback computed (D1), the kernel does every
substitution (D2), and the kernel is unchanged.

### What the runtime does

`#run` (`web/cubical-runtime.mjs`) sends to `#fallback` every node it does
not execute: a composition (`Comp`, `HComp`, `Trans`), a path applied
(`PApp`), `Glue`, a glue value, `unglue`, `abort`, and a constructor it
refuses, a path constructor, the squash among them, or one with a cubical
recursive position. `#fallback` forces none of the node's parts.

1. **Syntax-only conditions**, as `ck_expose` and `weak` read them
   (`kernel/src/term_expose.c`, `kernel/src/term_normalize.c`), each formula
   read with `kernel.inspectFormula`: a path applied at the formula 0 or 1
   under a `Path` annotation goes on with that endpoint of the annotation,
   under the node's environment; a `Comp` or `HComp` with a tube on the
   total face reads that tube alone back and goes on with
   `cc_kernel_endpoint_term` of it at its dimension's end, in the empty
   environment; a `Trans` on the total face goes on with its base; and an
   `unglue` whose `Glue` type has a piece on the total face pushes an
   application to the value and a first projection, and forces the piece's
   equivalence, under the node's environment. Nothing the rule discards is
   read back. These count as `shortcuts`.
2. **Otherwise the node's closure is read back** (`#read`, W1's readback
   machine), by value, and, in a query made with origins, as a normal form.
3. **The kernel's head** (`#headOf`): `kernel.head`, `cc_kernel_whnf` under
   its growing step budget, asked once a query for each term read back
   (`#asked`), a head recorded as its own head. These count as `fallbacks`,
   and each spends a query of the evaluation's fuel, as the head query it
   is.
4. **Going on** (`#settle`): a head whose root the machine makes a value of
   at once, a λ, a level λ, a path abstraction, a pair, an injection, the
   point, an eliminator or a type former other than `Glue`, or a
   constructor it executes applied to at most its arity, goes on as its
   syntax in the empty environment, copied as the walk reaches it. Any
   other head is opaque: its cell holds `{ tag: "Opaque", head }`, never
   asked again.

A frame that consumes an opaque head, a projection, a unit or sum
elimination, a term or level application or an eliminator, rebuilds the
node it stands for with the head in the consumed place and its other parts
read back, and sends that through steps 3 and 4 (`#consume`, `#consumed`).
The unit and sum frames keep their node and environment for this, in the
frame they already push, so no cell is added. Where an opaque head is the
value asked, its observation is `{ kind: "Opaque", head }`, and
`runtimeQueries` (`web/translator/translate.mjs`) gives the walk that
kernel handle as the part's head: `valueForm` goes on with the kernel's
spine, constructor names and glue systems, and the kernel's head queries
for its parts (`demandQueries`), as the kernel's walk shows a whole value.
So `glue(1 + 1)` at `Glue(UNat)` shows `glue(2)`, and a base transported
around the circle `<composition>`.

η of a path abstraction whose body is a path applied reads the abstraction
back and asks its head (`#eta`); a head that is the term read back means
that the kernel keeps the abstraction, and so does the runtime.

Each cell a readback reads gives a handle, and the first cell to give one
is recorded (`#standsFor`); a cell in the empty environment whose code is
such a handle, as the kernel's answers hold them, goes on with that cell
instead of computing its syntax again. A composition whose total tube is
a variable bound to a computed 200 goes on with that variable's cell, and
copies none of the 200 successors its readback wrote.

**Restarts.** A readback the fallback asks for that refuses, as
`unsupported`, abandons the walk, and `valueFormOf` computes it again on
the kernel's head queries, recording the reason, as every fallback did
before: at a higher-order recursive hypothesis (3.7, the one restart
section 5 names); at a term past the kernel's syntax depth, the kernel's
K344 when the readback writes it, which 3.7 lists among readback's
refusals; and at a type value whose environment the query does not keep
(below). A stop in the kernel's head query, K344, its budget or the
declaration's time limit, is reported as the kernel's.

### The two decisions W1 left to W2

1. **Value forms make no query for readback.** The fallback reads back, by
   value, from what a value form's query keeps: environment frames record
   the applied function's node, functions and path abstractions keep their
   node and environment, and a constructor's instance cell, which no value
   form forces, keeps its code. The one gap is a forced type value's
   environment, which W1 keeps only in a query made for readback; the heads
   η computed and the origins the fallback never reads. A fallback whose
   readback reaches a forced type value whose node mentions a variable
   refuses, and the walk restarts: in
   `(fun (T : U0) => (T, comp(fun (i : Interval) => U0, T)))((fun (A : U0) => A -> A)(Unit))`
   the first field forces T to `A -> A`, and the composition reads T's
   cell. No value form of the 193 constructs, the Cubist test modules (106
   value forms) or the six binary, radix and least-element contract files
   (65) restarts so. Made for readback instead, value forms would cost, on
   the 193 constructs, the same values, more retained objects in 7 (λ-η's
   kept head and the pruned bindings: 3 in B02, 1 in B31 and A27, 2 in
   A40 and A55, 8 in A49 and A46b) and the pruning's 199, 210 and 223
   steps in A40, A49 and A46b; nothing on the probe's twelve runtime
   workloads, from `count-into-510` to `binary-factorial-40`; and, as W1
   measured, `traverse2(n, n)` at `100 * 100`, whose result `Tag(n)`
   mentions its input, retaining 71,230 objects where it retains 13. Kept
   plain, a value form keeps main's retention, and the gap costs a restart
   that no corpus meets. Making value forms' queries for readback would
   remove that restart at the retention above.
2. **The stability rule** lets a memo entry answer a later readback only
   where it read forced cells and definitions with forced cells. On M2's
   workloads (below) it turns away 46 to 516 entries of earlier fallbacks
   per value form, against 86 to 5,267 hits, and the readbacks write at
   most 27,586 nodes in all, where the kernel spends 23,906 to 37.6M ticks:
   the rule costs little. The readback across forcing shows what it buys:
   reusing the first readback's closure of `x` would hand the kernel a
   computation it stops with K344.

### Where the code reads the note more precisely

1. **Restarts.** Section 5 keeps the whole restart for a node whose rebuild
   reaches a `Lift`. Every readback refusal restarts: also a term past the
   syntax depth, which 3.7 lists as a refusal, and a type value whose
   environment the query does not keep (decision 1). A restart shows
   today's value form, where a reported refusal would not.
2. **The readback's mode.** Section 5 reads the node back "as its closure".
   A value form's fallback reads it by value, as the readback across
   forcing needs: by origin, the forced `x` would be its computation, which
   the kernel stops with K344. A query made with origins, the oracle's
   folded walk and W3's `!!`, falls back by origin, so that the parts its
   walk takes from the kernel's heads keep the definition spines that
   folding watches: the 37 constructs that fall back fold as the kernel's
   folded normal forms do.
3. **Which heads are opaque.** Section 5 names examples, a formal
   composition at a higher sort and a glue value. The machine goes on with
   a head only where it makes a value of its root at once (step 4), so it
   never sends a head back through the fallback; every other head is
   opaque, among them a path constructor applied, `Glue`, and a stuck
   projection or elimination.
4. **A constructor the runtime refuses** falls back as the nodes section 5
   lists do: a path constructor is opaque, and the applications to its data
   are rebuilt around it, so it shows as the kernel's walk shows it, as
   section 5 expects (`relate(1, 3, tt)`). At an endpoint, a path
   constructor applied is its annotation's endpoint, by syntax.
5. **The total tube** is read for `HComp` as for `Comp`, as `ck_expose`
   reads both.
6. **A read-back handle met again** maps back to its cell only in the empty
   environment, where the kernel's answers and definitions' values are;
   any other code is the program's, under its environment.
7. **No node asked twice:** each term is asked once a query, a head is its
   own head, and an opaque head goes to the kernel's walk as its part's
   head, which `demandQueries` does not ask again. In `euclid(3)`, 56
   readbacks asked the kernel 23 heads.

### Tests

- `tests/runtime-fallback.test.mjs`, the note's W2 cases, each print
  compared with the kernel's queries alone: the `slow` composition shows
  `<fun>` in 13 ticks, `slow` neither demanded nor copied;
  `(expensive, comp(fun (i : Interval) => Unit, expensive))` shows
  `(tt, tt)`, its base read from the definition cell the first field
  forced, where the kernel's queries stop with K344; the readback across
  forcing, for a suspended `x` and for a definition first read back before
  it has a cell, shows `(<fun>, tt, tt)` where the kernel's queries stop
  with K344; `p @ 0` under its annotation shows `tt`, `p` neither forced
  nor read back, and a total tube goes on with its variable's cell; the
  higher-order `Tree` induction's discarded hypothesis shows `tt` in the
  runtime, and the composition whose base is the hypothesis restarts and
  shows `tt`; `comp^i hold(swapped @ i) [] (tt, 3)` shows `(3, tt)`; an
  `unglue` over the environment computes, through the kernel with an empty
  system and by syntax on the total face; the transported circle base
  shows `<composition>`, and `to_nat` of it `3`; `glue(1 + 1)` shows
  `glue(2)`; the type value and a value past the syntax depth restart;
  `euclid(7).1`'s K344 is the kernel's; and over `euclid(4)` and
  `glue(1 + 1)` no handle is asked of the kernel twice, the opaque head
  never after it is returned.
- Updated for W2: `tests/cubical-runtime.test.mjs` (a cubical sibling, a
  path abstraction's η, path constructors and the library Euclid's prime
  through the fallback), `tests/runtime-evaluation.test.mjs` (what computed
  each value form, now `per node` where it was a restart),
  `tests/evaluation-demand-marks.test.mjs` (all 193 constructs in the
  runtime: 6 settled by syntax alone, 31 asking the kernel, none
  restarting), `tests/evaluation-baseline.test.mjs` with its fixture at
  version 11, and the η mutation's site in `tests/runtime-readback.test.mjs`.
- The readback oracle (`tests/runtime-readback-oracle.mjs`) runs on every
  value form the runtime computes, those that fell back per node included,
  whose readbacks hold the kernel's heads. No comparison disagrees: of the
  constructs' 193, 190 agree by value and the 3 slow ones are undecided,
  all fold as the kernel's and 180 type; of the binary contracts' 41, the
  4 widest are undecided by value, as before; of the Cubist test modules'
  106 (97 before, and 9 that restarted), 103 agree by value and 3 are
  undecided, all 106 fold and 96 type.

Before W2, main restarted 37 of the constructs, 9 of the Cubist test
modules' value forms (8 at a composition, one at a path applied) and 10 of
the contract files' (9 at a composition, one at a path constructor); W2
computes each of them per node.

### M2, the fallback

`node tools/runtime-repl-probe.mjs NAME runtime` records a fallback's
readback counters as `fallback`, and the workloads now include
`euclid-8-prime` and `euclid-9-prime`. One sample each, a process of its
own: the restart at main `d27ad60d`, whose runtime is W1's, and the
fallback per node at `d103a2b5`, Node 24.13.0, macOS arm64, load average
about 5. Steps are the runtime's, its readbacks included; ticks are the
kernel's query steps; fallbacks are the heads asked of the kernel; writes,
hits and turned away are the readbacks' kernel syntax calls, memo hits and
unstable entries of earlier readbacks. No workload restarts at a `Lift`.

| Workload | Value form | Restart: steps, ticks | Per node: steps, ticks | Fallbacks | Writes, hits, turned away | Ticks saved | Time: restart, per node, kernel alone |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `euclid-3` | `(7, (tt, <fun>), tt)` | 3,711, 26,944 | 51,449, 23,906 | 23 | 760, 269, 63 | 11% | 9, 18, 7 ms |
| `euclid-4` | `(5, (tt, <fun>), tt)` | 3,956, 61,786 | 58,377, 59,718 | 32 | 894, 276, 144 | 3% | 12, 20, 11 ms |
| `euclid-4-prime` | `5` | 3,959, 57,053 | 26,661, 48,357 | 23 | 348, 86, 59 | 15% | 11, 16, 9 ms |
| `euclid-5-prime` | `11` | 4,198, 160,432 | 33,113, 142,099 | 29 | 447, 97, 63 | 11% | 17, 23, 16 ms |
| `euclid-6-prime` | `7` | 4,437, 133,848 | 35,488, 111,595 | 31 | 459, 98, 86 | 17% | 16, 22, 14 ms |
| `euclid-7-prime` | K344 | 634,130 ticks | 507,391 ticks | 31 | 439, 103, 90 | 20% | 44, 45, 43 ms |
| `euclid-8-prime` | K344 | 725,642 ticks | 570,491 ticks | 37 | 521, 100, 146 | 21% | 51, 50, 45 ms |
| `euclid-9-prime` | `19` | 5,154, 722,978 | 54,509, 493,553 | 53 | 814, 126, 135 | 32% | 46, 56, 41 ms |
| `euclid-10-prime` | `11` | 3,944, 423,409 | 57,940, 315,592 | 57 | 863, 131, 110 | 25% | 30, 37, 27 ms |
| `binary-factorial-40` | 40! | 3,765, 38,346,979 | 464,858, 37,596,441 | 311 | 27,586, 5,267, 46 | 2% | 1,199, 1,298, 1,195 ms |
| `binary-rational-equal` | `left(relate(…))` | 44,542, 77,516 | 69,653, 36,358 | 4 | 1,361, 521, 516 | 53% | 51, 54, 45 ms |
| the 37 constructs that fall back | as the kernel's | 1,362, 5,689 | 8,850, 4,299 | 139, and 6 shortcuts | | 24% | |

**Slower rows, plainly.** In wall time the fallback per node is slower than
the restart on every workload above but `euclid-8-prime`: by 2 to 100% on
the library Euclid's values, 8% on `factorial(40)` and 6% on the equal
rationals' decision. The runtime now computes what the restart left to the
kernel, 23,000 to 461,000 steps more, and the kernel's ticks it saves are
fewer. Nine of the 37 constructs take more ticks per node than the
restart did, by 1 to 9 each (B39, B46, B75, B77, B79, B80, B82, A33, A36:
small transports at data sorts, whose readback terms cost the kernel a
few more steps than its own walk). In the baseline, `winding-minus-2` takes
85 ticks more (0.08%).

**Where the kernel's work goes.** Most of the remaining ticks are in a few
fallbacks: in `factorial(40)`, 153 of its 311 are compositions at a data
sort, which take nearly all of its ticks, up to about 720,000 each. The
kernel's rule for a composition at a
data sort reads the weak head of its base (`data_sort_composition`,
`kernel/src/inductive_composition.c`); the fallback forces nothing, so a
transport's base reaches the kernel as a closure, and in NUM1's strong
recursion that base is the rest of the computation. The kernel then
computes it with its own substitution, as the restart did: so
`factorial(40)` saves 2%, and `euclid(7).1` still stops with K344, in the
head of a transport whose base is the rest of the search. Section 5's
condition for option (b), round trips that cost more than they save, is
not met in the kernel's ticks, which fall on every workload but the
winding number; in time it is, on the small Euclid values, where the
runtime's own work dominates.

**A measured variant, not adopted.** Section 5 forces none of a node's
parts, since forcing one the kernel's rule does not read adds demand. A
scratch variant asked the kernel first for the weak head of a
composition's family, and where it was a data sort, `Unit` or a sum,
whose rule reads the base's weak head, computed the base in the runtime
and read it back by value: `factorial(40)` took 218,261 ticks and 275 ms
(against 37,596,441 and 1,298 ms), `euclid-9-prime` 57,836 ticks,
`euclid-10-prime` 29,549 and `euclid-3` 18,151, with the same values;
`euclid-7-prime` and `euclid-8-prime` still stopped with K344, after
70,296 and 802,592 ticks, in a head whose substitution the kernel took past
its syntax depth. It reads the rule the kernel will take from the
family's head, which section 5 leaves to the kernel; it is a decision for
the note (D4), not taken here.
