import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { assertStage } from "./known-defect.mjs";
import { ciSeeds, caseLimit, configuration, generate, minimize } from "./fixtures/frontend-invariants.mjs";

const count = Number(process.env.CUBIST_GENERATION_CASES ?? ciSeeds.length);
assert.ok(Number.isSafeInteger(count) && count >= 1 && count <= caseLimit, "1..64 bounded cases");
const module = await create(), library = sourceReader();
const baseline = JSON.parse(await readFile(new URL("./fixtures/frontend-invariants-baseline.json", import.meta.url), "utf8"));

async function verify(config) {
  const spec = generate(config);
  const program = new CubicalProgram(module, (name, importer) => spec.fixtures[name] ?? library(name, importer));
  try {
    const result = await program.check(spec.source, "main");
    assert.deepEqual(result.gaps.filter(gap => gap.module !== "main"), [], "generated imports must check");
    const output = name => {
      const found = result.outputs.find(item => item.name === name);
      assert.ok(found, `${name} must have an output`);
      return found;
    };
    const observed = {
      gaps: result.gaps.map(gap => [gap.module, gap.name, gap.code]),
      accepted: spec.accepted.map(name => [name, output(name).verified]),
      assumes: result.outputs.filter(item => item.verified && item.axioms?.length).map(item => item.name),
    };
    const desired = { gaps: spec.expectedGaps.map(name => ["main", name, "E606"]),
      accepted: spec.accepted.map(name => [name, true]), assumes: [] };
    const record = [...program.checker.theories.values()].find(item => item.name === spec.model);
    for (const name of ["M", "c", "op"])
      assert.ok(record?.fields.some(field => field.name === spec.names[name]), `field correspondence ${name}`);
    for (const suffix of ["Hom", "Hom.id", "Hom.compose", "Iso", "Iso.id"])
      assert.ok(Object.values(program.symbols).some(item => item.name === `${spec.model}.${suffix}` && item.verified), `artifact ${suffix}`);
    const advice = lint(spec.source).filter(warning => ["W705", "W706"].includes(warning.code));
    assert.equal(advice.length, 1);
    assert.equal(advice[0].declaration, "ordinary");
    const rewritten = await program.check(spec.source.replace("forall unused : Unit. Unit", "Unit -> Unit"), "main");
    assert.deepEqual(rewritten.gaps.map(gap => [gap.module, gap.name, gap.code]), observed.gaps);
    const interfaces = result => result.outputs.filter(item => item.verified).map(item => [item.name, item.type, item.axioms]);
    assert.deepEqual(interfaces(rewritten), interfaces(result), "safe lint rewrite preserves checked interfaces and assumptions");
    const work = program.kernel.work();
    assert.ok(work.queries < 50000 && work.instructions < 500000, "bounded checker work; checker limits unchanged");
    assert.equal(work.deadlines, 0);
    return { observed, desired };
  } finally { program.dispose(); }
}

// Exercise imports, inheritance, renaming, helper depth, grouped/dependent
// parameters, caller notation and initial/free clients on the current stage.
// Recursive/path combinations remain in the generator and in G4/G8/G12's
// individual witnesses; enabling them here requires their CB2/CB3 fixes.
for (let seed = 0; seed < count; seed++) for (const capture of [false, true]) {
  test(`CB0 preservation: ${capture ? "capture target" : "active control"}, seed ${seed}`, { timeout: 30000 }, async t => {
    const config = { ...configuration(seed), binder: `local_${seed}`, recursive: false, paths: false, capture };
    const known = capture ? baseline.cases[String(seed % ciSeeds.length)] : undefined;
    let stage;
    try {
      stage = await verify(config);
      assert.deepEqual(stage.observed, known?.observed ?? stage.desired, "stage observation changed");
    } catch (error) {
      const reduced = await minimize(config, async candidate => {
        try {
          const next = await verify(candidate);
          assert.deepEqual(next.observed, known?.observed ?? next.desired, "stage observation changed");
          return false;
        } catch (failure) { return failure.code === error.code && failure.message === error.message; }
      });
      const directory = new URL("../build/frontend-generation-failures/", import.meta.url);
      await mkdir(directory, { recursive: true });
      const file = `seed-${seed}-${capture ? "capture" : "control"}.json`;
      await writeFile(new URL(file, directory), JSON.stringify({ seed, error: error.message, ...reduced, ...generate(reduced.config) }, null, 2) + "\n");
      error.message = `seed ${seed}; reduced witness in build/frontend-generation-failures/${file}: ${error.message}`;
      throw error;
    }
    assertStage(t, { ...stage, known, id: `preservation-${seed}-${capture}` });
  });
}
