import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { checkProgram } from "./check-program.mjs";

test("nondependent quotient descent preserves class and relation computation", async t => {
  const { result } = await checkProgram(t, `
import quotients;
computable def relation_computes(
  U, V < UU0, A : U, R : A -> A -> U, B : V, set_ : IsSet(V, B), f : A -> B,
  respects : Respects(U, V, A, R, B, f), a, b : A, r : R(a, b)
) :
  typed(f(a) = f(b), path i => descend(
    U, V, A, R, B, set_, f, respects, class_path(U, A, R, a, b, r) @ i
  )) = respects(a, b, r) := refl(respects(a, b, r));
computable def class_computes(
  U, V < UU0, A : U, R : A -> A -> U, B : V, set_ : IsSet(V, B), f : A -> B,
  respects : Respects(U, V, A, R, B, f), a : A
) : descend(U, V, A, R, B, set_, f, respects, class(a)) = f(a) := refl(f(a));
`);
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
});

test("the unchanged generic quotient functions fully normalize within the fixed gate", async t => {
  const source = await readFile(new URL("./fixtures/generic-prop-normalization.cubist", import.meta.url), "utf8");
  for (const name of ["to_unit", "to_prop"]) {
    const { program, result } = await checkProgram(t, source, { options: { collectReferences: false } });
    assert.equal(result.complete, true, JSON.stringify(result.gaps));
    const checked = program.checker.checkSyntax({ tag: "DefRef", name: `main__${name}` }, null, new Map(), new Map());
    const k = program.kernel, steps = 10000000n;
    k.stepBudget = steps; k.maxQuerySteps = steps; k.setStepBudget(steps); k.setDeadline(30000);
    const normal = k.normalize(checked.expression);
    assert.ok(normal > 0);
    assert.notEqual(k.node(normal).kind, "DefRef");
  }
});
