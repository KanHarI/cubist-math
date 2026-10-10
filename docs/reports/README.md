# Reports and historical evidence

Reports describe their named revisions. Their measurements, review outcomes
and contemporary recommendations are evidence, not current instructions.
The [work plan](../roadmaps/work-plan.md) owns scheduling. Raw review inputs
belong in the relevant PR discussion; inventories summarize their findings
with attribution.

## Frontend generation evidence

The [gap inventory](frontend-generation-gaps.md#current-status-and-fixing-evidence)
owns current finding status, fixes and distinguishing regressions. The
[shared follow-up checklist](pr-188-todo.md) links to outstanding work.
The [review at `00d4ecce`](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6095711362)
lives on PR #188.

The FG reports retain their original revision-specific evidence. Every raw
snapshot below is cited by a report; none is a live input to a tool or test.
Keep these cited baselines for their build/source digests, limits and sampled
measurements. New metrics are generated on demand by
[frontend-generation-metrics.mjs](../../tools/frontend-generation-metrics.mjs);
CI's mutation reports go under `build/`.

| Report | Cited evidence retained |
| --- | --- |
| [FG1: publication](frontend-generation-fg1.md) | [FG0](frontend-generation-metrics/fg0.json) and [FG1](frontend-generation-metrics/fg1.json), the before/after publication baseline |
| [FG2: dependencies](frontend-generation-fg2.md) | FG1 and [FG2](frontend-generation-metrics/fg2.json), notation/dependency change measurements |
| [FG3: universes](frontend-generation-fg3.md) | FG2 and [FG3](frontend-generation-metrics/fg3.json), generated-universe costs |
| [FG4: evidence](frontend-generation-fg4.md) | [FG4](frontend-generation-metrics/fg4.json), context/evidence measurements |
| [FG5: provenance](frontend-generation-fg5.md) | [FG5](frontend-generation-metrics/fg5.json), public-interface measurements |
| [FG6: preservation gate](frontend-generation-fg6.md) | [FG6](frontend-generation-metrics/fg6.json) and [mutation report](frontend-generation-mutations.json), including exact patches, digests, logs and reduced counterexample |

## Dated progress snapshots

These remain useful historical reports; they are not unfinished roadmaps
subject to the completed-scope archival rule. Dates distinguish the source
and validation state. Their original recommendations are not a second work
queue, and retired-source links are pinned to the report's revision.

| Snapshot | Purpose retained |
| --- | --- |
| [2026-09-29, morning](2026-09-29-daily.md) | `c2a8306`: native/JavaScript validation, corpus count and integration evidence before the H1 release |
| [2026-09-29, night](2026-09-29-night.md) | `16cc11f`: the subsequent acceptance-matrix coverage and semantic/engineering release obligations, compared with the morning snapshot |
| [2026-10-07](2026-10-07-daily.md) | `08ba80d`/`ae94f49`: measured checking-speed comparisons, the website publishing incident and then-open stack with explicit verification limits |
