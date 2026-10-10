# FG4 contextual evidence and wildcard diagnostics

G4 and G8 are active regressions. A scope now carries checked model evidence
as terms with types, contributing model and declaration/field identities.
Model parameters, opened models and source aliases acquire evidence only
from already checked projections. H-level search consumes these candidates;
the completed proof is still checked by the ordinary kernel.

Binding and dimension scopes preserve evidence. Match refinement substitutes
its term, type and model together, including generalized model parameters;
face restriction applies the same dimension substitution to all three.
Native checks in `frontend-evidence.test.mjs` verify the transformed proof
types, and source tests refuse evidence belonging to a different model.
Private structural recursion state remains separate from source aliases.

A written wildcard body is checked against its actual clause type first.
Only a constructor with recursive positions can try optional coherence.
Failure retains the original located endpoint mismatch; success publishes
the checked coherence and buffered inspection records. Explicit path bodies
and independently generated obligations keep their existing behavior.
Resource failures propagate separately, and abandoned attempts share the
declaration's work/search fuel rather than receiving free retries. The old
test requiring abandoned work to be free now asserts the total attempted
work. Syntax/lattice budget errors retain their messages and acquire the
resource category needed by this distinction. No limits changed.

## Producer and consumer audit

| Boundary | Contract and evidence |
| --- | --- |
| Model evidence acquisition | `Scope.bind`, opened models and nonvariable source aliases identify checked model types and projections; unpublished reservations supply no candidate. |
| Context transformations | `withUnit`, `withEnv`, binding, generalized match refinement and `onFace` retain or transform evidence consistently. Nested/dependent matches and native endpoint checks distinguish stale evidence. |
| H-level search | Both direct and quantified candidate enumeration consume the context; matching never conceals fuel/budget/deadline failures. Completed proof terms remain kernel checked. |
| Patterns and clause checking | `implicitPathSite` is origin metadata, not a new AST kind. The original body owns the primary error; constructor positions determine fallback eligibility. |
| Speculation and observers | Shared fuel charges every attempt once. References/proof steps are buffered; failed fallback publishes no generated obligation. Successful Unit-valued coherence publishes its checked inspection witness. |

Seven focused tests cover imported/renamed inheritance, nested shadowing,
dependent motives, generalized model parameters, quantified evidence,
wrong-model refusal, native dimension/refinement checks, failed fallback
with its exact body range, search fuel, and successful recursive coherence.
G8 additionally asserts that a nonrecursive boundary starts no search.
The full suite at `d0abfe5a` passes: 819 tests, 817 pass, two tracked FG5
TODOs, zero failures (119.5 seconds). Existing explicit-path, recursion,
initial/free and earlier-recursive-value controls remain active.
Inspector and built static-site browser checks pass, as do the diagnostic
catalog and diff checks. The initial static-site check found no built site
(HTTP 404); building the artifact resolved that setup failure. No corpus
timeouts occurred.

## Resources

Clean `d0abfe5a` is compared with FG3's clean `71e460ce`, using the same
three workloads, three fresh sessions each, unchanged defaults and WASM
build, without concurrent test load. Raw [FG4 measurements](frontend-generation-metrics/fg4.json)
retain revision/build/frontend/source stamps and all counters.

| Workload | Median ms, FG3 → FG4 | Instructions, before → after | Queries | Peak arena nodes, before → after |
| --- | ---: | ---: | ---: | ---: |
| Algebra import | 1157.8 → 1112.8 | 117,745 → 118,890 | 14,471 | 36,087 → 36,214 |
| Captured inheritance | 296.7 → 295.4 | 51,455 → 51,844 | 3,879 | 17,538 → 17,625 |
| Generated fold | 1169.8 → 1159.7 | 124,742 → 125,893 | 14,964 | 36,087 → 36,214 |

Evidence acquisition adds under 1% instructions and arena nodes on these
workloads. Query counts and allocated arena bytes are unchanged; byte peaks
are 4,593,664 / 2,624,512 / 4,593,664. Recovered kernel exhaustions remain
5/0/5; there are no deadline failures or gaps. Arena samples exclude
JavaScript memory. Timings are observations, not a regression budget.
