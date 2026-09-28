// The instruction driver against the term checker's conversion, on
// generated problems where eta and computation meet
// (tools/differential-driver.mjs): whatever the reference accepts the driver
// derives, and whatever it refuses the driver refuses. Fixed seeds here; the
// tool runs as many as asked.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { describe, disagreement, problem, verdicts } from "../tools/differential-driver.mjs";

test("the driver agrees with the term checker on generated eta problems", async t => {
  const program = new CubicalProgram(await createCubical(), async () => { throw new Error("No modules."); });
  t.after(() => program.dispose());
  await program.check("def unit_point : Unit := tt;\n", "differential");
  const found = [];
  for (let seed = 1; seed <= 500; seed++) {
    const p = problem(seed), reason = disagreement(p, verdicts(program, p));
    if (reason) found.push(`${reason}: ${describe(p)}`);
  }
  assert.deepEqual(found, []);
});

test("the generator is deterministic and poses every kind of problem", () => {
  assert.equal(describe(problem(7)), describe(problem(7)));
  const kinds = new Set(Array.from({ length: 100 }, (_, seed) => problem(seed + 1)).map(p => `${p.name}${p.equal ? "" : " different"}`));
  for (const name of ["nat", "sigma", "glueNat", "glueSigma", "glueNested", "face"]) {
    assert.ok(kinds.has(name), `an equal ${name} problem`);
    assert.ok(kinds.has(`${name} different`), `a different ${name} problem`);
  }
});
