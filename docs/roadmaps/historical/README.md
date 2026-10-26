# Historical plans, specifications and evidence

This directory separates completed work, superseded implementation sequences
and dated evidence from current scheduling. Archiving an implementation
sequence does not complete its unfinished proposals: their active owners are
listed below. Specifications and acceptance contracts remain useful, and
moving a record does not remove its regression tests.

Index reconciled on 2026-10-26 against main `7230825e`. Dated records below
retain their original revisions, measurements and review decisions.

| Document | Why historical | Current contract or follow-up |
| --- | --- | --- |
| [G0 universe specification](g0-universe-specification.md) | K1.1–K1.4 and L1.1 completed on 2026-09-27; all 43 former templates check generically | Its rules remain normative; [E1/E2](../kernel/language-enhancement-proposals.md) and K2.5's resizing remedies are separate work |
| [H1 history](h1-history.md) | Release chronology, review rounds, former experimental marker and retired representation contract | [H1 specification](../hott/h1-signature-specification.md) |
| [H1 review evidence](h1-review-evidence.md) | Mathematical release approvals completed on 2026-10-02 | Active [model](../hott/h1-model.md), [canonicity](../hott/h1-canonicity.md) and [critical-pair arguments](../hott/h1-critical-pairs.md) |
| [H1 release evidence](h1-release-evidence.md) | Pinned validation of the released revision, repeated on 2026-10-03 | Later changes require their own validation; the [acceptance matrix](../hott/h1-signature-specification.md#1010-coverage-of-the-acceptance-cases) remains checked |
| [H1 differential evidence](h1-differential-evidence.md) | Gate, oracle and replay tooling retired on 2026-10-02; the uncompleted replay cases were retired, not silently passed | Current source/native regressions and [source-defined type API](h1-program-types.md) |
| [2026-09-28 work-plan audit](audits/2026-09-28-audit.md) | Findings and measurements against `02a57ef`, before subsequent fixes/releases | [Work plan](../work-plan.md); dated findings are not current defect status |
| [Work-plan history through 2026-10-05](work-plan-history.md) | Superseded revision notes and first-action list retained from main's former schedule | Current [first actions](../work-plan.md#first-actions) and [decisions](../work-plan.md#open-decisions) |
| [Proof-ergonomics implementation sequence](proof-ergonomics-implementation-plan.md) | Original PR order mostly delivered, with other work withdrawn or transferred | [Active remaining contracts](../high-level-abstractions/proof-ergonomics-roadmap.md#remaining-implementation-contracts), HoTT and theory packages; linked lowering/measurement contracts remain applicable |
| [Capture and bindings](capture-bindings.md) | CB0–CB7 and both cleanups are complete and merged | [Frontend contract index](../frontend/README.md); keep binding, replay, preservation and resource contracts |
| CB checkpoints: [CB1](capture-bindings-cb1.md), [CB2](capture-bindings-cb2.md), [CB3](capture-bindings-cb3.md), [CB4](capture-bindings-cb4.md), [CB5](capture-bindings-cb5.md), [CB6](capture-bindings-cb6.md), [CB7](capture-bindings-cb7.md) | Completed implementation boundaries and revision-pinned reviews/measurements | CB7's resource allowances and RSS exception remain acceptance limits; checkpoint TODO counts are historical |
| [Frontend generation](frontend-generation.md) | FG implementation sequence delivered or replaced by CB0–CB7 | [Shared contracts](frontend-generation.md#shared-contracts) and [semantic preservation gate](frontend-generation.md#fg6-make-preservation-tests-and-measurements-a-release-gate) still govern extensions |
| [Scopes and captured syntax](syntax-hygiene.md) | Earlier nominal approach superseded by retained binding identities | [Binding design](capture-bindings.md), indexed under [frontend](../frontend/README.md) |
| [Refactoring and source-level tests](refactoring-and-testing.md) | Agreed RC scope and final cleanup merged in #243–#263 | [Publication contract](refactoring-and-testing.md#publication-ownership), [source-test guide](../../guides/regression-contracts.md); the remote mutation gate passed after #264 ([verification record](refactoring-and-testing.md#verification-record)) |
| [Induction hypothesis syntax](induction-hypothesis-syntax.md) | Syntax change and migration delivered in #228 | Recorded binding contract and [language reference](../../../web/reference/induction.html); eventual removal of the compatibility spelling needs a separate decision |
| [Evaluation demand marks](evaluation-demand-marks.md), with its [acceptance report](evaluation-demand-marks/report.md) | DM0–DM6 completed in #304–#306; archived on 2026-10-26 | Its decisions remain EVAL5's observation contract, documented in the language reference. `constructs.json` beside it is still the construct corpus of `tests/evaluation-demand-marks.test.mjs`, and `probe-sources.mjs` is shared with the [debugging plan](../runtime/rational-normalization-debug-plan.md)'s probe; open EVAL5 work is in the [runtime roadmap](../runtime/runtime-evaluation-roadmap.md#eval5-demand-only-the-result-being-observed) |
| [Folded normal forms](folded-normal-forms.md) | Decision D1 of the debugging plan; FN1/FN2 completed in #309/#310; archived on 2026-10-26 | `!!` folded and `!!!` full remain the contract, documented in the language and kernel references; the full-normal-form targets stay in the [debugging plan](../runtime/rational-normalization-debug-plan.md) |
| [Kernel instructions history](kernel-instructions-history.md) | Stages 4–5, I1.2a and I1.2b completed by 2026-10-02; split out on 2026-10-26 | [Kernel instructions](../kernel/kernel-instructions.md): the trust boundary, instructions, driver and stage-6 work |
| [Source-defined Nat, W and pushouts](h1-program-types.md) | Source migrations and primitive retirement are complete | Recorded source APIs, current [H1 specification](../hott/h1-signature-specification.md) and [language reference](../../../web/reference/induction.html) |

The subject folders retain unfinished work and normative specifications:
kernel stage-6 work, theory capabilities, notation tooling, HoTT automation,
runtime evaluation, and H1's specification and mathematical arguments. K2.5's
[truncation migrations and ledger](../hott/h1-truncation-migration.md) remain
unfinished. Paused mathematical developments remain under
[mathematics/](../mathematics/); they are not completed history.

A completed implementation plan can still contain a continuing contract.
The [frontend index](../frontend/README.md) links those sections explicitly;
archival status does not retire their rules, tests or measured acceptance limits.
The [work plan](../work-plan.md) remains the scheduling authority, including
follow-ups transferred out of completed implementation sequences.
