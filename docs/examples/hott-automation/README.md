# HoTT automation examples

These accompany the [HoTT and cubical automation roadmap](../../roadmaps/hott-automation-roadmap.md).
[conversion-laws.cubist](conversion-laws.cubist) records the evidence for its
library-first milestones. Every declaration checks by conversion or by one
existing lemma:

| Declarations | Roadmap item |
| --- | --- |
| `bridge_rec`, `bridge_ind` and their `_beta` laws | B0: suspension eliminators with PathP bridges compute on meridians |
| `bridge_code`, `bridge_code_meridian`, `bridge_code_upper`, `bridge_code_lower` | B0: the circle's cover through the bridge recursion |
| `cong_constant_line`, `cong_identity_line`, `cong_compose_line`, `cong_refl_line`, `cong_sym_line`, `sym_sym_line` | C1 conversion entries |
| `transport_path_right`, `transport_arrow` | C1 entries moved from the C2 transport rules |
| `happly_funext`, `sigma_projection_eta`, `naturality_square` | A7's conversion fixture; E2 starts from the naturality square |
| `closed_constant_transport` | Constant transport computes on closed values (G4) |
| `PropLevel`, `prop_level_zero`, `prop_level_one` | D0a: numeric h-levels agree with `IsProp` and `IsSet` |
| `reverse_dependent_path`, `dependent_congruence` | E0: dependent path operations |

A7 promotes these probes, and the rejected laws below, to regression tests.

## Checks

```sh
npm test -- docs/examples/hott-automation/conversion-laws.cubist
node tools/format-mathscript.mjs --check docs/examples/hott-automation/conversion-laws.cubist
```

On 2026-09-24 the first command checked 25 declarations in 89,080 native
checking steps, with no axioms. The second reported no formatting changes.

## Rejected laws

Conversion does not establish the first four statements below, and
elaboration rejects the last three declarations. Saved as a `.cubist` file and
checked with `node cli/repl.mjs check FILE`, every declaration is rejected:

- the first four with "Type mismatch." at `rfl`;
- `rejected_sym_pathp` with "Unbound cubical dimension: d0"; the file's
  `reverse_dependent_path` is the working construction;
- the last two with "A simplification rule parameter is not determined by the
  matched side; supply arguments." The inferred left sides of these lemmas
  omit `A`, `x` and `y`.

```text
import paths;

def rejected_right_unit(A : U1, x y : A, p : x = y) : trans(p, refl(y)) = p {
  rfl;
}

def rejected_cong_trans(A B : U1, f : A -> B, x y z : A, p : x = y, q : y = z) :
  cong(f, trans(p, q)) = trans(cong(f, p), cong(f, q)) {
  rfl;
}

def rejected_transport_left(A : U1, a x y : A, p : x = y, q : x = a) :
  transport(fun (t : A) => t = a, x, y, p, q) = trans(sym(p), q) {
  rfl;
}

def rejected_constant_refl(A B : U0, x : A, v : B) :
  transport(fun (t : A) => B, x, x, refl(x), v) = v {
  rfl;
}

def rejected_sym_pathp(A : U0, B : A -> U0, x y : A, p : x = y, u : B(x), v : B(y),
  q : PathP(fun (i : Interval) => B(p @ i), u, v)) :
  PathP(fun (i : Interval) => B(p @ flip(i)), v, u) {
  exact sym(q);
}

def rejected_rule_constant(A B : U1, x y : A, p : x = y, v : B) :
  transport(fun (t : A) => B, x, y, p, v) = v {
  simp only [transport_constant];
}

def rejected_rule_ap(A : U1, C : A -> U0, x y : A, p : x = y, v : C(x)) :
  transport(C, x, y, p, v) = transport(C, x, y, p, v) {
  simp only [transport_ap];
}
```
