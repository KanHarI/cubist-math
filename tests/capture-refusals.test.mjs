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
import { fixtureClientContract, validateMigrationWitness, assertCapturedRefusal } from "./migration-witnesses.mjs";

const module = await create(), library = sourceReader();
// G10's ordinary fixture observer checks comment placement. Its migration
// controls use the same semantic client view as the binding witnesses.
const fixtureWitnesses = cases.filter(c => captureControls[c.id]);
const witnessCases = [...bindingCases, ...fixtureWitnesses.map(c => ({...c,...fixtureClientContract(c.source)}))];
const captureCodes = new Set(captureRefusals.map(item => item.code));
function checkedReading(t,c,edits,name = "main") {
  const sources = {...c.fixtures,main:c.source};
  for (const {module:owner,...edit} of edits)
    sources[owner] = editedFixture(sources[owner],edit,`${c.id}/${owner}`);
  return checkProgram(t,sources[name],{module,name,
    reader:(name,importer) => sources[name] ?? library(name,importer)});
}

test("retired capture-only refusals retain distinguishing migration witnesses", async () => {
  const root = new URL("../", import.meta.url);
  const codes = new Set(captureRefusals.map(item => item.code));
  assert.deepEqual(Object.keys(captureControls).sort(), captureRefusals.flatMap(item => item.witnesses).sort());
  for (const {witnesses} of captureRefusals) for (const id of witnesses) {
    const witness = witnessCases.find(c => c.id === id), control = captureControls[id];
    assert.ok(witness, `${id}: witness exists`);
    validateMigrationWitness(witness,control,codes);
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
  test(`CB0 migration control: ${id}, ${reading} reading`, async t => {
    const c = witnessCases.find(c => c.id === id);
    const captured = control.captured, edits = reading === "intended" ? control.intended : captured.edits;
    const refusal = reading === "captured" && captured.kind === "refused";
    const name = refusal ? captured.module : "main";
    const {result} = await checkedReading(t,c,edits,name);
    if (refusal) {
      const intended = await checkedReading(t,c,control.intended,name);
      const view = result => observeModule(result,{name,clients:[captured.name]});
      assertCapturedRefusal(view(intended.result),view(result),captured,captureCodes);
      return;
    }
    const desired = structuredClone(c.desired);
    if (reading === "captured") {
      desired.clients[control.positive] = false;
      desired.clients[captured.negative] = true;
      desired.gaps = desired.gaps.map(gap => gap[1] === captured.negative ? ["main",control.positive,gap[2]] : gap);
    }
    assert.deepEqual(observeModule(result,{clients:c.clients}),desired,
      `${id}: ${reading} source must distinguish the clients and preserve the other contracts`);
  });
}

test("migration contracts reject reversed source comments and undeclared negative clients", () => {
  const codes = new Set(captureRefusals.map(item => item.code)), c = cases.find(c => c.id === "G10");
  const reversed = c.source.replace("// Error: E606\n", "").replace("def intended", "// Error: E606\ndef intended");
  assert.throws(() => validateMigrationWitness({...c,...fixtureClientContract(reversed)},captureControls.G10,codes),
    /intended client/);
  const ordinary = bindingCases.find(c => c.id === "initial-pattern-model"), withNegative = structuredClone(ordinary);
  withNegative.clients.push("wrong");
  withNegative.desired.clients.wrong = false;
  withNegative.desired.gaps.push(["main","wrong","E606"]);
  assert.throws(() => validateMigrationWitness(withNegative,captureControls[ordinary.id],codes),
    /every refused client/);
});

test("an independently unsupported declaration cannot prove an ill-typed captured reading", async t => {
  const c = bindingCases.find(c => c.id === "initial-pattern-model");
  const {result} = await checkedReading(t,c,captureControls[c.id].intended);
  const observed = observeModule(result,{clients:["k"]});
  assert.throws(() => assertCapturedRefusal(observed,observed,{module:"main",name:"k",code:"E856"},captureCodes),
    /intended reading must accept/);
});
