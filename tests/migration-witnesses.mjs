import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { stated } from "../web/cubist/stated-comments.mjs";
import { precondition } from "./known-defect.mjs";

// A fixture's comments are its contract, including for migration controls.
// Never keep a second manually written client verdict beside that source.
export function fixtureClientContract(source, moduleName = "main") {
  const declarations = parse(source).declarations.map(d => ({name:d.name.text,
    line:source.slice(0,d.start).split("\n").length - 1}));
  const errors = stated(source).filter(item => item.label === "Error");
  precondition(() => {
    assert.equal(new Set(declarations.map(d => d.name)).size, declarations.length,
      "migration clients need distinct declaration names");
    for (const error of errors) {
      assert.equal(declarations.filter(d => d.line === error.line).length, 1,
        "each migration error comment must identify one declaration");
      assert.match(error.text, /^E\d+(?::|$)/, "a refused client needs a diagnostic code");
    }
  });
  return {clients:declarations.map(d => d.name), desired:{
    gaps:errors.map(error => [moduleName,declarations.find(d => d.line === error.line).name,error.text.match(/^E\d+/)[0]]),
    clients:Object.fromEntries(declarations.map(d => [d.name,!errors.some(error => error.line === d.line)])),
    assumes:[],
  }};
}

export function validateMigrationWitness(witness, control, captureCodes) {
  const {id,clients,desired} = witness, captured = control.captured;
  assert.deepEqual([...clients].sort(),Object.keys(desired.clients).sort(),`${id}: every client has one verdict`);
  assert.equal(desired.clients[control.positive],true,`${id}: intended client`);
  assert.ok(control.intended?.length,`${id}: an intended source control is required`);
  assert.ok(captured?.edits?.length,`${id}: an explicit captured source control is required`);
  assert.ok(["clients","refused"].includes(captured.kind),`${id}: captured reading has a checked outcome`);
  const ordinary = control.ordinaryRefusals ?? {};
  const refused = Object.entries(desired.clients).filter(([,accepted]) => !accepted).map(([name]) => name);
  assert.deepEqual(refused.sort(),[...Object.keys(ordinary),...(captured.kind === "clients" ? [captured.negative] : [])].sort(),
    `${id}: every refused client is a distinguishing negative or an ordinary refusal`);
  for (const [name,code] of Object.entries(ordinary)) {
    assert.ok(!captureCodes.has(code),`${id}: ordinary refusal cannot be a capture workaround`);
    assert.deepEqual(desired.gaps.filter(gap => gap[1] === name),[["main",name,code]],`${id}: ordinary refusal ${name}`);
  }
  if (captured.kind === "clients") {
    assert.equal(desired.clients[captured.negative],false,`${id}: captured client`);
    assert.equal(desired.gaps.filter(gap => gap[1] === captured.negative).length,1,`${id}: negative diagnostic`);
  } else {
    assert.ok(captured.reason?.length,`${id}: explain the ill-typed reading`);
    assert.match(captured.code,/^E\d+$/,`${id}: ordinary captured-reading refusal`);
    assert.ok(!captureCodes.has(captured.code),`${id}: a capture workaround cannot prove ill-typedness`);
    assert.ok(captured.module === "main" || typeof witness.fixtures?.[captured.module] === "string",`${id}: refusal module`);
    assert.equal(typeof captured.name,"string",`${id}: refused declaration`);
  }
}
