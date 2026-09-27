# HoTT automation examples

These accompany the [HoTT and cubical automation roadmap](../../roadmaps/hott-automation-roadmap.md).
[conversion-laws.cubist](conversion-laws.cubist) records the evidence for its
library-first milestones. Every declaration checks by conversion or by one
existing lemma:

| Declarations | Roadmap item |
| --- | --- |
| `bridge_rec`, `bridge_ind` and their `_beta` laws | B0 (superseded by H1, whose generated eliminators behave this way): suspension eliminators with PathP bridges compute on meridians |
| `bridge_code`, `bridge_code_meridian`, `bridge_code_upper`, `bridge_code_lower` | B0 (superseded by H1): the circle's cover through the bridge recursion |
| `cong_constant_line`, `cong_identity_line`, `cong_compose_line`, `cong_refl_line`, `cong_sym_line`, `sym_sym_line` | C1 conversion entries |
| `transport_path_right`, `transport_arrow` | C1 entries moved from the C2 transport rules |
| `happly_funext`, `sigma_projection_eta`, `naturality_square` | A7's conversion fixture; E2 starts from the naturality square |
| `closed_constant_transport` | Constant transport computes on closed values (G4, now for all declared data types) |
| `PropLevel`, `prop_level_zero`, `prop_level_one` | D0a: numeric h-levels agree with `IsProp` and `IsSet` |
| `reverse_dependent_path`, `dependent_congruence` | E0: dependent path operations |

A7 made these probes regression tests in `tests/hott-automation.test.mjs`,
together with three further fixtures:

| File | Contents |
| --- | --- |
| [cubical-probes.cubist](cubical-probes.cubist) | Accepted constructions from the roadmap's evidence and review probes, the mixed-universe control and E1's ordered fillers; all check |
| [canonicity.cubist](canonicity.cubist) | Invariant 10: closed assumption-free results, each proved by `rfl` against its canonical value, including winding numbers of loops in the circle |
| [rejected-probes.cubist.rejected](rejected-probes.cubist.rejected) | Laws that must stay rejected and simplifier probes rejected until a named milestone; the `.rejected` suffix keeps it out of globs of checked sources |

[measure.mjs](measure.mjs) records the A7 baseline in
[baseline.json](baseline.json). The
[implementation checkpoint](../../tactical/hott-automation-handoff.md) records
its results and the expected outcome of each rejected probe.

## Checks

```sh
npm test -- tests/hott-automation.test.mjs
npm test -- docs/examples/hott-automation/conversion-laws.cubist docs/examples/hott-automation/cubical-probes.cubist docs/examples/hott-automation/canonicity.cubist
node tools/format-mathscript.mjs --check docs/examples/hott-automation/*.cubist docs/examples/hott-automation/rejected-probes.cubist.rejected
```

On 2026-09-24, `conversion-laws.cubist` checked 25 declarations in 89,080
native checking steps, with no axioms. On 2026-09-25 the test file passed, the
three checked fixtures checked 43 declarations with no axioms, and the
formatter reported no changes.

## Rejected laws

[rejected-probes.cubist.rejected](rejected-probes.cubist.rejected) contains
the laws that conversion does not establish, the review probes that must stay
rejected, and the simplifier probes waiting for A1, A2 or E0. The test file
checks each rejection and its reason. When a milestone makes a waiting probe
check, the test fails and names the probe to move into a checked fixture.
