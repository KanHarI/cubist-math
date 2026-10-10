# Historical plans, specifications and evidence

This directory separates completed work, superseded implementation sequences
and dated evidence from current scheduling. Archiving an implementation
sequence does not complete its unfinished proposals: their active owners are
listed below. Specifications and acceptance contracts remain useful, and
moving a record does not remove its regression tests.

Reconciled on 2026-10-10 against main `cb525f07`.

| Document | Why historical | Current contract or follow-up |
| --- | --- | --- |
| [G0 universe specification](g0-universe-specification.md) | K1.1–K1.4 and L1.1 completed on 2026-09-27; all 43 former templates check generically | Its rules remain normative; [E1/E2](../language-enhancement-proposals.md) and K2.5's resizing remedies are separate work |
| [H1 history](h1-history.md) | Release chronology, review rounds, former experimental marker and retired representation contract | [H1 specification](../h1-signature-specification.md) |
| [H1 review evidence](h1-review-evidence.md) | Mathematical release approvals completed on 2026-10-02 | Active [model](../h1-model.md), [canonicity](../h1-canonicity.md) and [critical-pair arguments](../h1-critical-pairs.md) |
| [H1 release evidence](h1-release-evidence.md) | Pinned validation of the released revision, repeated on 2026-10-03 | Later changes require their own validation; the [acceptance matrix](../h1-signature-specification.md#1010-coverage-of-the-acceptance-cases) remains checked |
| [H1 differential evidence](h1-differential-evidence.md) | Gate, oracle and replay tooling retired on 2026-10-02; the uncompleted replay cases were retired, not silently passed | Current source/native regressions and [source-defined type API](../h1-program-types.md) |
| [2026-09-28 work-plan audit](audits/2026-09-28-audit.md) | Findings and measurements against `02a57ef`, before subsequent fixes/releases | [Work plan](../work-plan.md); dated findings are not current defect status |
| [Work-plan history through 2026-10-05](work-plan-history.md) | Superseded revision notes and first-action list retained from main's former schedule | Current [first actions](../work-plan.md#first-actions) and [decisions](../work-plan.md#open-decisions) |
| [Proof-ergonomics implementation sequence](proof-ergonomics-implementation-plan.md) | Original PR order mostly delivered, with other work withdrawn or transferred | [Active remaining contracts](../proof-ergonomics-roadmap.md#remaining-implementation-contracts), HoTT and theory packages; linked lowering/measurement contracts remain applicable |

The active directory retains documents with unfinished implementation or
current normative/API content: kernel stage-6 work, theory capabilities,
notation tooling, HoTT automation, runtime evaluation, and the H1
specification and mathematical arguments. The truncation ledger still owns
unfinished migrations; the source-defined Nat/W/pushout record describes the
current API. Paused mathematical developments are unfinished, not completed
history.

The integrated frontend roadmap has evidence/performance follow-ups, so it
remains active. See
[branch work](../work-plan.md#branch-work).
