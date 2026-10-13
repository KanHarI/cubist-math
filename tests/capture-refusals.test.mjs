import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readdir, readFile } from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { captureRefusals, captureControls, captureObservationFiles } from "./fixtures/capture-refusals.mjs";
import { bindingCases } from "./fixtures/capture-bindings.mjs";
import { cases } from "./frontend-generation-cases.mjs";
import { editedFixture } from "./fixture-edits.mjs";
import { checkProgram } from "./check-program.mjs";
import { observeModule } from "./module-observation.mjs";

const module = await create(), library = sourceReader();
// G10's ordinary fixture observer checks comment placement. Its migration
// controls use the same semantic client view as the binding witnesses.
const witnessCases = [...bindingCases, {...cases.find(c => c.id === "G10"),
  clients:["T","intended","captured"],
  desired:{gaps:[["main","captured","E606"]],clients:{T:true,intended:true,captured:false},assumes:[]},
}];

test("capture-only refusals belong to known observations and have migration witnesses", async () => {
  const root = new URL("../", import.meta.url);
  const codes = new Set(captureRefusals.map(item => item.code));
  const fixtureBaseline = JSON.parse(await readFile(new URL("./fixtures/frontend-generation-baseline.json", import.meta.url), "utf8"));
  const bindingBaseline = JSON.parse(await readFile(new URL("./fixtures/capture-bindings-baseline.json", import.meta.url), "utf8"));
  assert.deepEqual(Object.keys(captureControls).sort(), captureRefusals.flatMap(item => item.witnesses).sort());
  for (const {code,phase,witnesses} of captureRefusals) for (const id of witnesses) {
    const record = bindingBaseline.cases[id] ?? fixtureBaseline.cases[id];
    assert.ok(record, `${code}: ${id} must have a known observation`);
    assert.ok(record.phase.split("/").some(part => phase.split("/").includes(part)), `${id}: migration owner`);
    assert.ok(JSON.stringify(record.observed).includes(code), `${id}: record observes its capture refusal`);
    const witness = witnessCases.find(c => c.id === id), control = captureControls[id];
    assert.ok(witness, `${id}: witness exists`);
    assert.equal(witness.desired.clients[control.positive], true, `${id}: intended client`);
    assert.ok(control.intended?.length, `${id}: an intended source control is required`);
    if (control.negative) {
      assert.equal(witness.desired.clients[control.negative], false, `${id}: captured client`);
      assert.ok(control.captured?.length, `${id}: a captured source control is required`);
      assert.equal(control.noCaptured, undefined);
    } else {
      assert.ok(control.noCaptured?.length, `${id}: explain why the captured reading is ill-typed`);
      assert.equal(control.captured, undefined);
      assert.ok(!witness.clients.includes("captured"), `${id}: no vacuous negative client`);
    }
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

for (const [id, control] of Object.entries(captureControls)) for (const reading of ["intended","captured"]) {
  if (!control[reading]) continue;
  test(`CB0 migration control: ${id}, ${reading} reading`, async t => {
    const c = witnessCases.find(c => c.id === id), sources = {...c.fixtures,main:c.source};
    for (const {module:name,...edit} of control[reading]) {
      sources[name] = editedFixture(sources[name],edit,`${id}/${name}`);
    }
    const {result} = await checkProgram(t,sources.main,{module,
      reader:(name,importer) => sources[name] ?? library(name,importer)});
    const desired = structuredClone(c.desired);
    if (reading === "captured") {
      desired.clients[control.positive] = false;
      desired.clients[control.negative] = true;
      desired.gaps = desired.gaps.map(gap => gap[1] === control.negative ? ["main",control.positive,"E606"] : gap);
    }
    assert.deepEqual(observeModule(result,{clients:c.clients}),desired,
      `${id}: ${reading} source must distinguish the clients and preserve the other contracts`);
  });
}
