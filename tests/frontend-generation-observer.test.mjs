import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cases, observe } from "./frontend-generation-cases.mjs";

const module = await createCubical();

// None of these imports is used by the main module: its declarations still
// check, so declaration comments alone cannot expose the imported failure.
for (const { kind, source, failedModule } of [
  { kind: "missing module", source: null, failedModule: "fg0_dependency" },
  { kind: "missing transitive module", source: "import fg0_missing_leaf;\ndef unused : Unit := tt;\n", failedModule: "fg0_missing_leaf" },
  { kind: "refused declaration", source: "def wrong : Unit := Unit;\n", failedModule: "fg0_dependency" },
  { kind: "failed directive", source: "evaluate fg0_unknown;\n", failedModule: "fg0_dependency" },
]) test(`case observations reject an imported ${kind} before classifying defects`, async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-generation-imports-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  if (source !== null) await writeFile(join(directory, "fg0_dependency.cubist"), source);
  // A control and two cases, none with a local refusal.
  for (const id of ["control-recursion", "G5", "G9"]) {
    const c = cases.find(c => c.id === id);
    const candidate = { ...c, path: join(directory, `${c.name}.cubist`),
      source: c.source.replace("\n", "\nimport fg0_dependency;\n") };
    await assert.rejects(() => observe(t, candidate, module), error => {
      assert.equal(error.code, "ERR_TEST_PRECONDITION");
      assert.ok(error.cause.actual.some(gap => gap.module === failedModule), "retain the failed module and its diagnostic");
      return true;
    }, id);
  }
});

test("one reported local error cannot account for two checker failures", async t => {
  const c = cases.find(c => c.id === "G6"), check = CubicalProgram.prototype.check;
  t.mock.method(CubicalProgram.prototype, "check", async function (...args) {
    const result = await check.apply(this, args);
    result.gaps.push({ ...result.gaps[0] });
    return result;
  });
  await assert.rejects(() => observe(t, c, module), error => {
    assert.equal(error.code, "ERR_TEST_PRECONDITION");
    assert.equal(error.cause.actual.length, 1);
    assert.equal(error.cause.actual[0].module, c.name);
    return true;
  });
});
