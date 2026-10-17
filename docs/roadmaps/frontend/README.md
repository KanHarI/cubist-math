# Frontend contracts

CB0–CB7, their cleanups, the FG work they replace, and the agreed RC refactoring
and source-test scope are complete. Their exhausted plans and dated evidence
live in [historical/](../historical/README.md). This index keeps the contracts
needed for future frontend changes discoverable without a second specification.

| Boundary | Continuing contract and evidence |
| --- | --- |
| Binding identities, scopes and substitution | [Binding design](../historical/capture-bindings.md#shared-representation), [resolution](../historical/capture-bindings.md#resolution-and-scoping) and [retained interfaces](../historical/capture-bindings-cb2.md) |
| Deferred scopes and checked evidence | [CB3](../historical/capture-bindings-cb3.md) |
| Generation, universes and declaration admission | [Shared generation contracts](../historical/frontend-generation.md#shared-contracts), [artifact builder](../historical/capture-bindings-cb4.md) and [semantic preservation gate](../historical/frontend-generation.md#fg6-make-preservation-tests-and-measurements-a-release-gate) |
| Diagnostics, generated views and contextual REPLs | [CB5](../historical/capture-bindings-cb5.md), [CB6](../historical/capture-bindings-cb6.md) and the [REPL contract](../historical/capture-bindings.md#contextual-repl-at-arbitrary-nesting-depth) |
| Publication ownership and source tests | [Publication lifecycle](../historical/refactoring-and-testing.md#publication-ownership) and the [regression-contract guide](../../guides/regression-contracts.md) |
| Release and resource limits | [CB7 evidence](../historical/capture-bindings-cb7.md), including its recorded allowances and RSS exception |

The [work plan](../work-plan.md#first-actions) owns new implementation and the
unresolved remote mutation-check follow-up. Checked initial/free capabilities
and their universal proofs remain [L2.6 work](../high-level-abstractions/core-theories.md#initial-and-free-models-l26);
completion of the frontend migration does not establish those proofs.
