import test from "node:test";
import assert from "node:assert/strict";
import { readdir, readFile } from "node:fs/promises";
import { captureRefusals, captureObservationFiles } from "./fixtures/capture-refusals.mjs";
import { bindingCases } from "./fixtures/capture-bindings.mjs";

test("capture-only refusals belong to known observations and have migration witnesses", async () => {
  const root = new URL("../", import.meta.url);
  const codes = new Set(captureRefusals.map(item => item.code));
  const fixtureBaseline = JSON.parse(await readFile(new URL("./fixtures/frontend-generation-baseline.json", import.meta.url), "utf8"));
  const bindingBaseline = JSON.parse(await readFile(new URL("./fixtures/capture-bindings-baseline.json", import.meta.url), "utf8"));
  for (const {code,phase,witnesses} of captureRefusals) for (const id of witnesses) {
    const record = bindingBaseline.cases[id] ?? fixtureBaseline.cases[id];
    assert.ok(record, `${code}: ${id} must have a known observation`);
    assert.ok(record.phase.split("/").some(part => phase.split("/").includes(part)), `${id}: migration owner`);
    assert.ok(JSON.stringify(record.observed).includes(code), `${id}: record observes its capture refusal`);
    assert.ok(bindingCases.some(c => c.id === id) || (await readdir(new URL("./fixtures/frontend-generation/", import.meta.url)))
      .some(file => file === `${id.toLowerCase()}.cubist`), `${id}: witness exists`);
  }
  for (const c of bindingCases) for (const gap of c.desired.gaps)
    assert.ok(!codes.has(gap[2]), `${c.id}: capture refusal cannot be desired`);
  const forbidden = new RegExp(`\\b(${[...codes].join("|")})\\b`);
  async function scan(directory) {
    for (const entry of await readdir(new URL(directory,root), {withFileTypes:true})) {
      const path = `${directory}/${entry.name}`;
      if (entry.isDirectory()) await scan(path);
      else if (/\.(mjs|cubist)$/.test(path) && !captureObservationFiles.includes(path))
        assert.ok(!forbidden.test(await readFile(new URL(path,root), "utf8")), `${path}: capture refusal outside a known observation`);
    }
  }
  await scan("tests"); await scan("cubist-tests");
});
