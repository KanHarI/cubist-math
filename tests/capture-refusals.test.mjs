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
import { fixtureClientContract, validateMigrationWitness } from "./migration-witnesses.mjs";

const module = await create(), library = sourceReader();
// G10's ordinary fixture observer checks comment placement. Its migration
// controls use the same semantic client view as the binding witnesses.
const fixtureWitnesses = cases.filter(c => captureControls[c.id]);
const witnessCases = [...bindingCases, ...fixtureWitnesses.map(c => ({...c,...fixtureClientContract(c.source)}))];

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
    const c = witnessCases.find(c => c.id === id), sources = {...c.fixtures,main:c.source};
    const captured = control.captured, edits = reading === "intended" ? control.intended : captured.edits;
    for (const {module:name,...edit} of edits) {
      sources[name] = editedFixture(sources[name],edit,`${id}/${name}`);
    }
    const refusal = reading === "captured" && captured.kind === "refused";
    const name = refusal ? captured.module : "main";
    const {result} = await checkProgram(t,sources[name],{module,name,
      reader:(name,importer) => sources[name] ?? library(name,importer)});
    if (refusal) {
      const observed = observeModule(result,{name,clients:[captured.name]});
      assert.equal(observed.clients[captured.name],false,`${id}: the explicit captured declaration must be refused`);
      assert.deepEqual(observed.gaps.filter(gap => gap[1] === captured.name),[[name,captured.name,captured.code]]);
      assert.deepEqual(observed.assumes,[]);
      assert.ok(observed.gaps.every(gap => !captureRefusals.some(item => item.code === gap[2])),
        `${id}: ill-typedness must be independent of capture workarounds`);
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
