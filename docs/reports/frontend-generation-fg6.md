# FG6 preservation release gate

The normal suite now includes eight deterministic source configurations
(seeds 0–7). `npm run test:generation:audit` checks 32 configurations, then
runs the full mutation/probe manifest. Generation accepts at most 64 seeds;
helper depth is bounded by the seed, and every check retains the normal
declaration/search limits. Additional audit ceilings are 50,000 kernel
queries, 500,000 instructions and 30 seconds per invariant test. They do
not raise any checker limit.

Each configuration composes several transformations: local alpha renaming
under intentional shadowing with public parameters unchanged; unrelated
declarations using generated-name stems; direct/imported theories;
inheritance with an explicit field-name correspondence; a changed caller
`use` selection; nested helper inlining through complete dependent
telescopes; earlier recursive value calls; initial/free generation;
recursive wildcard coherence; and an ordinary safe lint rewrite.

Independent source proofs state the intended helper equation, inherited
law boundary, changed child's notation, identity/composition, earlier-call
computation, generated operation and free-fold computation. The captured
equation must fail E606. The test additionally checks no assumptions,
public artifacts, inherited origin identities, all written law-binder
links and hover labels, exact nonrecursive-wildcard diagnostic spans and
zero search calls, named generated arguments, and preservation of checked
types/artifacts after the safe lint edit. Printed output is not the sole
semantic oracle: the ordinary kernel checks the independent proofs.

Failures record the seed, source/module map and a greedy reduced
configuration in `build/frontend-generation-failures/`. The reducer tries
at most twelve dependency-aware reductions in a fixed order. Mutation
reports retain reduced cases before disposing of their isolated copy.
This is a bounded counterexample search, not a proof of compiler correctness.

## Mutation gate

`npm run test:generation:mutations` copies the relevant sources and stamped
WASM into a temporary directory. For each exact single-site patch it first
runs the named test unmodified, requires an actual passing test, applies
the patch, then restores the original. Only an assertion failure counts as
a kill. Syntax/import errors, process failures, timeouts and unclassified
failures cannot pass the gate. Each subprocess is limited to 60 seconds,
each test to 45 seconds, and output to 8 MiB. Source digests and exact
patches are recorded. CI runs this gate and uploads its report and saved
counterexamples even on failure.

| Contract mutation | Distinguishing observation |
| --- | --- |
| Drop the registered public label | G9 binder/use names and original definition targets in `frontend-provenance` |
| Drop the label during alpha freshening | The same observations, including derived parameters and imported source |
| Discard lexical `use` capture | Seed 3's independent inherited helper/law equations under the changed caller selection |
| Lower a reference by spelling | `references`: lowering retains the captured binding independently of spelling |
| Skip the derived telescope region | G11's intended equation checks while the captured equation fails |
| Omit the generated universe contribution | G2's fixed-domain Hom and composition clients |
| Retain stale evidence during refinement | Native checked evidence type/model after refinement and face restriction |
| Bypass a declaration reservation | Mixed definition/inductive ownership retains the earlier usable declaration |
| Commit a failed publication | G7 checks absence from the actual native kernel and frontend observers |
| Ignore synthetic provenance | Imported initial/free notation does not emit links at copied source offsets |
| Attempt nonrecursive wildcard coherence | G8 keeps its primary E606 and spends zero search calls |
| Suggest the destructive interface lint edit | G5 rechecks named Hom and initial clients after the proposed edit |
| Ignore the explicit path head | A two-value match must reject an explicit `p(y) @ i, _ => tt` with E606 and no generated obligation |

The final item distinguishes the separately reported explicit-head probe:
single-value explicit clauses bypass pattern compilation, but a two-value
match enters it. Treating that explicit head as a wildcard incorrectly
accepts its written body through optional coherence. The valid explicit
recursive-body control and invalid single-value control also remain active.

## Historical audit disposition and limitations

The preserved reviewer report says 20 mutations: 13 killed, one skipped,
six surviving. It provides descriptions of the six survivors and the
separate explicit-head probe, but no exact mutation manifest, individual
list of the thirteen kills, or identification/reason for the skipped case.
Those historical counts are attributed evidence, not a reproduced run.
The requested original manifest remains outstanding; the unidentified
skipped case cannot honestly be declared resolved.

| Named historical survivor/probe | Current disposition |
| --- | --- |
| Binding label removal | Required kill: the source alias now keeps its key and label separately, and G9 checks every observation. |
| Label supplied only to `scope.fresh` | The analogous single-binder probe still survives all FG5 observations. After FG5, aliases and parameter metadata supply public labels independently of the kernel name's seed. This is an internal-name preference for those observations. The distinct alpha-freshening label-loss mutation is killed. The report does not misclassify the historical fresh-name probe as killed. |
| Initial-model `notationScope` aliases | Removed in FG2 with its producer, AST traversal exception and retained-record plumbing. Captured notation is the sole source; the synthetic-provenance mutant distinguishes the remaining inspection boundary. |
| Branch private `RECURSIVE` update | Retained as defensive context maintenance. The probe survives ordinary/generated recursion, generalized parameters, dependent/nested evidence, shadowing and an added predecessor-destructing nested match. Source aliases and clause recursion records still carry the supported calls. These results do not prove the update dead; it is excluded from the required-kill set rather than tested against its own implementation. |
| `recursiveCall` source guard | Defensive producer assertion. The parser cannot create this node; the generated self-call producer names the same declaration installed in private recursion state. Earlier recursive values use checked projections, not this node. Ordinary/generated structural and shadowed recursion controls still pass without the guard. Malformed internal ASTs are not a supported source distinction. |
| Re-add `IsSet`/`IsProp` to generated globals | Survives the source tests using those exact parameter names. Evidence dependencies are captured identities; conservative extra freshening does not change the retained public labels or checked clients. Retained as an equivalent extra-avoidance probe for the supported interface. |
| Explicit-head guard | Now killed by the two-value explicit-path case described above. |
| Unidentified skipped mutation | Pending original manifest; neither guessed nor included in a claimed kill rate. |

The four surviving probes are retained in the repeatable audit with explicit
expected outcomes, separate from the thirteen required CI kills. A change
in a probe's outcome fails the audit and requires revisiting its disposition.
This records a justified scope limit rather than weakening an assertion
to match a mutant. No production guard is removed to satisfy a score.

## Producer and consumer audit

The source generator emits only existing supported syntax. Its client
equations are authored independently of the frontend's generated types.
The checker, source-alias inspector, dependency graph, linter and export
observations consume the resulting programs. The test runner discovers the
eight-case file automatically; CI separately executes exact mutations in
an isolated copy. Counterexample/report consumers preserve seeds, limits,
patches and source digests. This phase adds no AST kind, proof axiom, kernel
rule or language capability. FG1–FG5 reports contain their corresponding
production producer/consumer audits and before/after measurements.
