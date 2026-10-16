import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { isDeepStrictEqual } from "node:util";
import { observeModule } from "./module-observation.mjs";
import { ciSeeds, caseLimit, configuration, generate, minimize, observationDifferences } from "./fixtures/frontend-invariants.mjs";

const count = Number(process.env.CUBIST_GENERATION_CASES ?? ciSeeds.length);
assert.ok(Number.isSafeInteger(count) && count >= 1 && count <= caseLimit, "1..64 bounded cases");
const module = await create(), library = sourceReader();

async function verify(config) {
  const spec = generate(config);
  const program = new CubicalProgram(module, (name, importer) => spec.fixtures[name] ?? library(name, importer));
  try {
    const result = await program.check(spec.source, "main");
    const {clients, ...local} = observeModule(result, {clients:spec.accepted});
    const observed = {...local, accepted:clients};
    const desired = { gaps: spec.expectedGaps.map(name => ["main", name, "E606"]),
      accepted: Object.fromEntries(spec.accepted.map(name => [name, true])), assumes: [] };
    const record = [...program.checker.theories.values()].find(item => item.name === spec.model);
    desired.fields = ["M", "c", "op"].map(name => spec.names[name]);
    observed.fields = desired.fields.filter(name => record?.fields.some(field => field.name === name));
    const artifacts = ["Hom", "Hom.id", "Hom.compose", "Iso", "Iso.id"];
    desired.artifacts = Object.fromEntries(artifacts.map(name => [name, true]));
    observed.artifacts = Object.fromEntries(artifacts.map(suffix => [suffix,
      Object.values(program.symbols).some(item => item.name === `${spec.model}.${suffix}` && item.verified)]));
    const advice = lint(spec.source).filter(warning => ["W705", "W706"].includes(warning.code));
    assert.equal(advice.length, 1);
    assert.equal(advice[0].declaration, "ordinary");
    const rewritten = await program.check(spec.source.replace("forall unused : Unit. Unit", "Unit -> Unit"), "main");
    assert.deepEqual(observeModule(rewritten).gaps, observed.gaps);
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
// CB3's recursive/path behavior participates in every combination as well
// as G4/G8/G12's individual witnesses.
for (let seed = 0; seed < count; seed++) for (const capture of [false, true]) {
  test(`CB0 preservation: ${capture ? "capture target" : "uncolliding parameter"}, seed ${seed}`, { timeout: 30000 }, async () => {
    const config = { ...configuration(seed), capture };
    const { observed, desired } = await verify(config);
    const differences = observationDifferences(observed, desired);
    if (differences.length) {
      const reduced = await minimize(config, async candidate => {
        // Each candidate has its own desired result. Infrastructure errors
        // are non-reproductions; retain the original semantic difference.
        const next = await verify(candidate);
        return isDeepStrictEqual(observationDifferences(next.observed, next.desired), differences);
      });
      const directory = new URL("../build/frontend-generation-failures/", import.meta.url);
      await mkdir(directory, { recursive: true });
      const file = `seed-${seed}-${capture ? "capture" : "control"}.json`;
      await writeFile(new URL(file, directory), JSON.stringify({ seed, differences, ...reduced, ...generate(reduced.config) }, null, 2) + "\n");
    }
    assert.deepEqual(observed, desired, `preservation-${seed}-${capture}`);
  });
}
