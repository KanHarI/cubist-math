// The instruction driver against the term checker's conversion, on
// generated problems where eta and computation meet
// (tools/differential-driver.mjs): whatever the reference accepts the driver
// derives, and whatever it refuses the driver refuses. Fixed seeds here; the
// tool runs as many as asked.
import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
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

test("the tool checks what it is asked, or stops", () => {
  const tool = args => spawnSync(process.execPath, ["tools/differential-driver.mjs", ...args],
    { cwd: fileURLToPath(new URL("../", import.meta.url)), encoding: "utf8" });
  const run = tool(["--seeds=3", "--from=5"]);
  assert.equal(run.status, 0, run.stderr);
  assert.match(run.stdout, /^3 problems from seed 5: 0 disagreements\.$/m);
  for (const args of [["--from=oops"], ["--seeds=Infinity"], ["--seeds=0"], ["--seeds=2.5"], ["--seeds=-1"], ["--seed=2000"],
    ["--from=4294967295", "--seeds=2"], ["2000"], [""]]) {
    const refused = tool(args);
    assert.equal(refused.status, 2, args.join(" "));
    assert.match(refused.stderr, /Usage: node tools\/differential-driver\.mjs/, args.join(" "));
    assert.equal(refused.stdout, "", args.join(" "));
  }
});
