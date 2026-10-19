# Rational full-normalization failure

Status on 2026-10-19: unresolved. The binary-rational field in #283 remains
unreleased; the default `Z`/`Q` migration is pending. The structural work is
part of the [runtime roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#rational-full-normalization-completion-path),
not a separate language-feature or real-number project.

## Small reproduction on main

The [fixture](../../tests/fixtures/generic-prop-normalization.cubist) contains an
arithmetic-free reproduction and a control. The function that exhausts the
fixed diagnostic budget is:

```cubist
import quotients;
import propositions;

def Same(a, b : Unit) : U0 := Unit;

computable def to_prop(h : IsSet(U1, Prop(U0)),
  q : Quotient(U0, Unit, Same)) : Prop(U0) :=
  descend(U0, U1, Unit, Same, Prop(U0), h,
    fun (a : Unit) => typed(Prop(U0), (Unit, unit_is_prop)),
    fun (a, b : Unit, r : Unit) =>
      refl(typed(Prop(U0), (Unit, unit_is_prop))), q);
```

This definition checks successfully. The expensive request is full
normalization of the function, including its body under the `h` and `q`
binders. No inhabitant is being searched for. Setness is a parameter, so
the example does not spend its budget expanding `prop_type_is_set`.
This isolates one necessary workload; the concrete setness argument used by
rationals needs a separate full-normalization check as well.
The control `to_unit` uses the same trivial quotient and a constant Unit map.
This is a small isolated reproduction, not a claim of absolute syntactic
minimality.

From the repository root, after building the WASM kernel:

```sh
make wasm
node tools/quotient-normalization-probe.mjs
```

The [probe](../../tools/quotient-normalization-probe.mjs) checks the source in
a fresh program for each case, obtains an instruction-derived expression
handle, and calls the ordinary full normalizer. It fixes the query budget
at 10,000,000 steps and the deadline at 30 seconds. It does not modify the
kernel or retry with larger budgets. Read each JSON outcome: controlled
resource stops are recorded without making the diagnostic process fail.
An optional positive integer argument selects another fixed step budget
within the normal query ceiling.
The deadline stays at 30 seconds even with a larger step argument; a slower
machine can therefore report a deadline before reaching its step budget.

Measured on main `89f73ea1` with this fixture and probe:

| Case | Outcome | Query steps | Newly allocated nodes |
| --- | --- | ---: | ---: |
| `to_unit` | Full normal form | 5,117 | 1,156 |
| `to_prop` | Fixed budget exhausted | 10,000,000 | 2,028,800 |

The bounded failure establishes disproportionate work on this small open
function; it does not prove divergence or that no larger budget can finish.
The runtime's usual query ceiling is larger; this fixture's outcome with the
default growing budgets and no diagnostic deadline has not been measured.
The concrete wide rational
contract has separately failed with K336, the native reduction recursion
limit. These are different observations.

## Relation to rationals

On the binary-rationals branch at `117a06cb` (based on main `34fb0818`),
the concrete contract that reached K336 is:

```cubist
import binary_rationals;
use binary_rationals;
evaluate bq_inv(-340282366920938463463374607431768211455/18446744073709551615)
  expecting _;
```

`expecting _` still requests a full normal form. It does not skip the
certificate. The proof that the inverse's denominator is nonzero reaches
`bint_decide` → `difference_decide` → `quotient_effective` → `related_to`,
which descends into `Prop(U0)`.
Although the inverse input is closed, the negative equality decision returns
a function binding an assumed equality `same`. Full normalization enters
that function's body; `same @ i` remains open, exposing the generic quotient
eliminator and its generated clauses. This is why normalization of an open
quotient function is relevant to the closed inverse.

Independently checked component probes isolate the cost: the numerator and
denominator normalize; the nonzero proof already exhausts a fixed ten-million
step budget for `bq_inv(-2/3)`. For the wide input, a separate trace shows
mixed closed/open BNat law proofs entering unary conversion and nested UNat
addition. The proof as written can require enormous unary syntax. Changing
that proof algorithm is distinct from fixing generic quotient normalization.
The corresponding small full-value contract on the same branch is
`evaluate bq_inv(-2/3) expecting _;`. The component probes and partial graphs
below were measured on `117a06cb`, before #287's implicit-inference fix;
they have not been repeated on top of #287.

## Partial reductions

A later [counted rewrite trace](quotient-normalization-trace.md) records exact
checkpoints at 1, 2, 5, 10, 20 and 50 rule applications on main `89f73ea1`,
including a comparison with the expected path, sigma and universe rules.
Unlike the historical work-budget snapshots below, these are contraction
counts with reduction-cache shortcuts disabled.

Temporary, reverted instrumentation recorded active normalizer frames and
completed sibling results at fixed work budgets. Reconnecting those frames
gave the following diagnostic partial graphs on `117a06cb` (the binary
rational branch based on main `34fb0818`):

| Query | Steps | Reachable partial nodes | Partial depth |
| --- | ---: | ---: | ---: |
| Trivial quotient to Prop, setness parameter | 10,000 | 885 | 63 |
| Same | 100,000 | 4,043 | 94 |
| Same | 1,000,000 | 23,351 | 155 |
| Nonzero proof from `bq_inv(-2/3)` | 10,000 | 1,073 | 73 |
| Same | 100,000 | 3,644 | 148 |
| Same | 1,000,000 | 27,208 | 434 |

These historical measurements used separate equivalent source probes, not
the two-function fixture above. They are partial states, not final normal
forms or new judgements. At one million steps the Prop graph contains 11,480
composition nodes and 8,786 boundary-system nodes. Growth occurs in the
generated quotient squash clause's Glue equivalence witnesses, their types,
and nested composition bases and boundaries. The small inverse reaches the
same machinery, including long composition chains inside a pair's type.

Native alpha comparisons confirm thousands of duplicate composition nodes;
an exact face/body-handle survey also finds duplicate boundary pieces.
Alpha equality ignores some annotations, so those counts alone do not
justify interning arbitrary typed terms. Four narrow experiments—stable
local binder names, Pi composition binder reuse, normalizing bodies before
annotations with an early eta attempt, and skipping identical boundary
pieces—still exhausted ten million steps on the generic Prop examples.
They were reverted; none completed within that diagnostic budget. This
establishes concrete growth mechanisms, but does not establish the eventual
normal-form size, behavior under default limits, or unavoidable growth.
The temporary trace patch and raw partial graphs are local investigation
artifacts, not retained in this repository; the bounded probe above is the
committed, reproducible experiment.

The [elaborator audit](elaborator-path-family-normalization.md) already fixed
false dependence for directly generated constant-motive matches. Generic
`descend` is compiled with a genuinely dependent motive before specialization;
that earlier fix does not remove its justified transports.

## What counts as fixing it

Computing numerator/denominator projections, exposing a pair with a suspended
proof, or checking `evaluate nonempty P by proof` does not complete the
full-normalization contract. Keep the generic reproduction's source unchanged
through the structural work. Its completion gate is full normalization within
the probe's fixed 10,000,000-step budget, without increasing the arena/memory
limit, with no retries, resource failure or host overflow. A depth guard may
be replaced only after the bounded traversal replacements specified by
EVAL4. The step unit here is the current kernel's query work; if a new
evaluator accounts differently, re-baseline both cases (including the Unit
control) and publish comparable work/memory bounds before claiming this gate.
Record the 30-second deadline outcome separately because it
depends on the machine. Report the completed normal-form size, depth, steps
and retained memory. Check the result using the existing trusted rules on
tractable differential cases before replacing a trusted reducer.

A smaller, checked elaboration of the generated squash clause can count as
a fix: the source fixture stays the same, while its generated term may
change. The earlier audit proposed a direct square filler or a direct match
in `descend`; those remain unvalidated candidates. They must preserve the
dependent eliminator's computation and handle generic callers, with the
same full-normalization checks. A caller-specific helper avoiding the
fixture does not close this gate. Changes to universe composition rules,
proof irrelevance or transport regularity are outside this plan.

The required end-to-end gates remain full small and wide rational inverses,
all NUM2 contracts, and the explicit default `Z`/`Q` migration gates. The
roadmap separates source proof algorithm changes, lazy execution, cubical
reduction, and full typed readback so that success at one cannot close the
others.
