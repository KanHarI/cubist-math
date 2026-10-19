# Shared runtime execution: first implementation

This is an internal EVAL3/EVAL4 query implementation for ordinary data. No
checker, REPL or page uses it yet. It returns observations, not kernel evidence
or full typed normal forms. Cubical execution, deep typed readback and the
rational full-normalization gates remain open.

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
