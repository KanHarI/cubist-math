# HoTT automation implementation checkpoint

Date: 2026-09-25. This is the implementation handoff for the
[HoTT and cubical automation roadmap](../roadmaps/hott-automation-roadmap.md).
A7, the baseline and regressions, is complete. Every other milestone is still
planned. No kernel rule, elaborator rule or tactic changed; three library
proofs now hold by conversion.

## Regression fixtures

`tests/hott-automation.test.mjs` checks four fixtures in
[docs/examples/hott-automation](../examples/hott-automation/README.md). It pins
each fixture's declaration list, so a law cannot silently leave it.

| Fixture | Declarations | Expected outcome |
| --- | --- | --- |
| `conversion-laws.cubist` | 25 | All check with no assumptions. This decides the C1/C2 classification and detects changes to kernel computation. |
| `cubical-probes.cubist` | 10 | All check: the roadmap's evidence constructions, `trans` as one composition, `sym(sym(p))` by `refl(p)`, an arbitrary witness for a convertible rule, a `U1` rule applied at a `U0` carrier with explicit arguments, and E1's ordered transport fillers. |
| `canonicity.cubist` | 8 | Invariant 10: each closed assumption-free result is stated with its canonical value and proved by `rfl` alone. The test rejects any other proof. Winding numbers compute through univalence and the circle. |
| `rejected-probes.cubist.rejected` | 15 | Two helper declarations check. Seven probes must stay rejected. Six are rejected until a named milestone lands. |

The seven permanent rejections are four laws that do not hold by conversion,
the sequential composition of two congruences equated to the simultaneous
line, an arbitrary loop equated to `refl`, and E1's independent filler. The
milestone-gated probes are:

| Probe | Current reason | Expected to change with |
| --- | --- | --- |
| `rejected_sym_pathp` | "Unbound cubical dimension: d0" | E0 or A1a: check, or give a normal diagnostic |
| `rejected_rule_constant`, `rejected_rule_ap` | Rule parameter not determined by the matched side | A1 folded signatures |
| `under_succ` | Unresolved equality goal | A2 |
| `use_ru`, `use_ru_at_u0` | Unresolved equality goal | A1, including mixed-universe matching |

When a milestone makes a gated probe check, the test fails and says to move
that probe into a checked fixture.

## Measurement baseline

[measure.mjs](../examples/hott-automation/measure.mjs) writes
[baseline.json](../examples/hott-automation/baseline.json) for the 15
declarations that A7 names. The proof-ergonomics baseline is unchanged. Each
row records tokens, lines and source hashes, the public type as currently
inferred, assumptions, and a fresh and a reused observation. An observation
records elapsed time, native checking steps, the closing check's steps,
steps spent in universe specialization, native queries, budget retries,
rewrite work and the final-check arena snapshot.

The fresh session checks the import graph once in a new kernel. The reused
session checks each selected module again, under a new name, in the same
kernel. Three templates (`adjoint_triangle`, `equiv_from_inverse` and
`group_hom_ext_at`) are measured through `U0` specializations, with the
inclusive cost of each first specialization and the declaration that
triggered it. `foldedType` stays null until A1.

Observations from this run (revision `7d9893b` plus these changes, Node
v22.22.0 on an Apple M3 Pro, one observation, 40 modules, 457 checked
declarations):

- The same 15 declarations used 16,486 native checking steps in the fresh
  session and 30,915 in the reused one. Step counts depend on session state,
  so A4 must define cache and session accounting before counting steps as fuel.
- Closing checks were 456 of the 16,486 steps. They reuse judgements cached
  during elaboration, so elaboration queries dominate. The kernel's own
  re-check during definition is not reported to JavaScript.
- 1,779 native queries needed no step-budget retry at the default budget.
- First specializations cost 8,989 steps (`adjoint_triangle`), 10,607
  (`equiv_from_inverse`, including its nested `adjoint_triangle`) and 2,900
  (`group_hom_ext_at`). The first two were triggered by `binary_nat_equiv`.
- The recorded signatures of `right_unit`, `transport_constant` and
  `transport_ap` are raw `path`/`comp` terms. `quotient_rec_beta` is the only
  selected declaration with assumptions (three truncation assumptions).

## Conversion audit

27 corpus declarations use derived path induction. For each, the native
checker compared the two sides of its checked statement by conversion:

| Result | Declarations |
| --- | --- |
| Holds by conversion; proof replaced by `rfl` | `homotopy_paths.path_map_constant`, `homotopy_paths.path_map_identity`, `field_products.field_pair_path_decode` |
| Needs its proof | 18, including `circle.decode_encode`, `group_total_laws_path` and `identity_system_retraction` |
| Not an equality statement | 5 |
| Template, not audited | `paths.based_induction` |

The three replacements state their former inferred types explicitly. Native
conversion confirms that each public type, and the types of their consumers
(`null_homotopy_kills_loops`, `contractible_loops_are_null` and
`field_product_is_set`), are unchanged. All six remain assumption-free.

Per invariant 9, the witnesses changed: each lemma was derived path induction
and is now a constant path. Its consumers were rechecked, as were the four
modules that import `homotopy_paths` or `field_products`. Fresh-session native
checking steps fell as follows:

| Declaration | Before | After |
| --- | --- | --- |
| `path_map_constant` | 325 | 199 |
| `path_map_identity` | 205 | 107 |
| `field_pair_path_decode` | 624 | 468 |
| `null_homotopy_kills_loops` | 1,447 | 1,440 |
| `contractible_loops_are_null` | 335 | 321 |
| `field_product_is_set` | 2,914 | 2,631 |

`field_pair_path_refl` was the base case of the replaced induction and is now
unused. It was kept, since removing a public declaration is a separate
decision.

## Verification

```sh
node tools/build-cubical-runtime.mjs
npm test -- tests/hott-automation.test.mjs
npm test -- homotopy_paths field_products field_asymptotics circle_degree complex_numbers identity_systems
node docs/examples/hott-automation/measure.mjs
node tools/format-mathscript.mjs --check docs/examples/hott-automation/*.cubist docs/examples/hott-automation/rejected-probes.cubist.rejected
npm test
```

All of these passed on 2026-09-25. The full suite passed 360 tests, and the
canonical corpus still checks 3,761 declarations and 43 templates with no
failed or blocked declarations.

## Next unfinished item

A5, the goal and proof-construction layer, together with the elaborator items
the roadmap adds to it: one name supply, result values instead of message
matching, one computation of link sites and an explicit elaboration context.
A4's deterministic fuel can proceed alongside it, using the session
dependence recorded above. Library-first items B0, E0 and D0a need no new
tooling and can start now. The kernel roadmap's G1 design comparison is
independent.
