import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { validateLedger } from "../tools/migration-ledger.mjs";
import { execFileSync } from "node:child_process";
import { moduleReader } from "../web/module-resolution.mjs";
import { checkProgram, checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/truncation_*.cubist, whose comments state
// each refusal (tests/cubist-tests.test.mjs); here, their assumptions.
async function check(t,name) {
  const {program,result}=await checkTestModule(t,name,{module});
  const get=name=>[...result.outputs,...result.imports].find(output=>output.name===name);
  const assumptions=output=>output.axioms.map(name=>result.assumptionLabels[name] ?? name).sort();
  return {program,result,get,assumptions};
}

test("G2: small_mere_eliminate uses the declared eliminator into U1 without assumptions",async t=>{
  const {result,get,assumptions}=await check(t,"truncation_small_mere");
  assert.ok(result.complete,JSON.stringify(result.gaps));
  assert.deepEqual(assumptions(get("replay")),[]);
  assert.deepEqual(get("replay").extensions,[]);
});

test("G5: the rebuilt CauchySame relation and EventualClose stay in U0 without assumptions",async t=>{
  const {result,get,assumptions}=await check(t,"truncation_cauchy_same");
  assert.ok(result.complete,JSON.stringify(result.gaps));
  for(const name of ["EventualClose","CauchySame","relation"]) {
    assert.ok(get(name)?.verified,name); assert.deepEqual(assumptions(get(name)),[],name);
  }
});

test("G6: resizing a proposition uses only LEM; a StrictlyAbove witness cannot use set evidence",async t=>{
  const {get,assumptions}=await check(t,"truncation_resize");
  assert.ok(get("resized")?.verified,get("resized")?.reason);
  assert.deepEqual(assumptions(get("resized")),["LEM"]);
  assert.equal(get("rejected").verified,false);
  assert.match(get("rejected").reason,/mismatch/i);
});

test("G7: no_maximal_strict_successor applies double negation at U1 and retains LEM",async t=>{
  const {get,assumptions}=await check(t,"truncation_strict_successor");
  assert.ok(get("replay")?.verified,get("replay")?.reason);
  assert.deepEqual(assumptions(get("replay")),["LEM"]);
});

// K2.5 step 1 retired the Zorn and classical comparisons, whose pins it
// invalidated, and step 5 the field-logic and Cauchy comparisons, whose
// baselines use the removed legacy builtins; each records the last revision
// at which it passed, and its pinned changes.
test("G4: the checked migration ledger records its retired comparisons and defers the H2 tower declarations",async()=>{
  const ledger=JSON.parse(await readFile(new URL("../docs/roadmaps/hott/h1-truncation-ledger.json",import.meta.url),"utf8"));
  assert.equal(validateLedger(ledger).size,0);
  assert.deepEqual(ledger.retired.map(record=>[record.comparison,record.lastPassing,record.changes.length]),
    [["zorn_chain_complete","21f55b55",1],["classical_axioms","21f55b55",4],["field_logic","7896d18a",1],["cauchy_quotient","7896d18a",11]]);
  assert.deepEqual(ledger.deferred,["tower_induction_large","tower_relative_induction"]);
  assert.throws(()=>validateLedger({...ledger,changes:[...ledger.changes,ledger.retired[0].changes[0]]}),
    /belongs to the retired zorn_chain_complete comparison/);
  // The retired changes remove only the legacy truncation assumptions, the
  // policy they were pinned under; an active change removes none.
  const [record]=ledger.retired;
  assert.throws(()=>validateLedger({...ledger,retired:[{...record,changes:[{...record.changes[0],assumptionsRemoved:["LEM"]}]}]}),
    /which remove only the legacy truncation assumptions/);
  assert.throws(()=>validateLedger({...ledger,changes:[{...ledger.retired[2].changes[0],module:"field_logic_again"}]}),
    /may not remove or replace an assumption/);
});

test("G4: the CLI refuses a baseline other than the pinned one, a retired comparison and a new module without a baseline",()=>{
  const args=["tools/verify-proof-migration.mjs","--base","f4d1961","--no-dependents",
    "--edited-file","library/h1_classical.cubist"];
  const ledger=["--ledger","docs/roadmaps/hott/h1-truncation-ledger.json"];
  assert.throws(()=>execFileSync(process.execPath,[...args.slice(0,2),"cc6b50f",...args.slice(3),...ledger,"classical_axioms"],{stdio:"pipe"}),
    error=>error.status===1 && /Ledger baseline is f4d1961.*different revision/.test(String(error.stderr)));
  assert.throws(()=>execFileSync(process.execPath,[...args,...ledger,"classical_axioms"],{stdio:"pipe"}),
    error=>error.status===1 && /The ledger retired its classical_axioms comparison, which last passed at 21f55b55/.test(String(error.stderr)));
  assert.throws(()=>execFileSync(process.execPath,[...args,"migration_no_baseline_fixture"],{stdio:"pipe"}),
    error=>error.status===1 && /No baseline for compared module migration_no_baseline_fixture/.test(String(error.stderr)));
});

test("archive module names check from the CLI and the verifier, with no marker",()=>{
  const module = execFileSync(process.execPath,["cli/repl.mjs","check","cauchy_quotient"],{encoding:"utf8"});
  assert.doesNotMatch(module,/kernel extension|under review|does not check|failed/i);
  const migration = execFileSync(process.execPath,["tools/verify-proof-migration.mjs","--no-dependents","cauchy_ordered"],{encoding:"utf8"});
  assert.match(migration,/0 failures/);
});

// The verifier reads its baseline as a historical source, and compares an
// axiom by its assumed statement: the library's axioms and every declaration
// that uses them verify against their committed sources (#317's review,
// findings 3 and 4).
test("the library's axiom modules verify unchanged against their committed baseline",()=>{
  const report=execFileSync(process.execPath,["tools/verify-proof-migration.mjs","--no-dependents","--edited-root","library",
    "classical_axioms","h1_classical","universe_automorphisms"],{encoding:"utf8"});
  assert.match(report,/ok {3}classical_axioms: 7 identical/);
  assert.match(report,/ok {3}universe_automorphisms: 23 identical/);
  assert.match(report,/3 modules \(0 dependents\), 0 failures/);
});

test("the CLI refuses the field-logic and Cauchy comparisons, retired with the legacy builtins",()=>{
  const cases = [
    ["cauchy_quotient","cubist-tests/h1_cauchy_quotient.cubist",null],
    ["field_logic","docs/examples/h1/migrations/field_logic.cubist","FieldProp,small_mere_eliminate"],
  ];
  for (const [module,file,scope] of cases) {
    const args=["tools/verify-proof-migration.mjs","--no-dependents","--edited-file",file,
      "--ledger","docs/roadmaps/hott/h1-truncation-ledger.json",...(scope ? ["--declarations",scope] : []),module];
    assert.throws(()=>execFileSync(process.execPath,args,{stdio:"pipe"}),
      error=>error.status===1 && new RegExp(`The ledger retired its ${module} comparison, which last passed at 7896d18a`).test(String(error.stderr)));
  }
});

// K2.5 step 5 removed the legacy builtins: their names are unknown
// everywhere, an archive module's as a library module's.
test("the legacy builtins' names are unknown in an archive module and in a library module",async t=>{
  const source="def truncated := Truncate(U0, Unit);\n";
  for(const place of ["archive","library"]) {
    const reader=moduleReader(()=>null);
    reader.place("legacy",place);
    const {get}=await checkProgram(t,source,{module,name:"legacy",reader});
    assert.equal(get("truncated").code,"E343",place);
    assert.match(get("truncated").reason,/^Untranslated name: Truncate\b/,place);
  }
});

test("the archive's excluded middle is the library's, and a program that uses both lists it once",async t=>{
  const {get,assumptions}=await check(t,"truncation_rebuilt_classical");
  for(const name of ["old","rebuilt","both"])assert.ok(get(name).verified,get(name).reason);
  for(const name of ["old","rebuilt","both"])assert.deepEqual(assumptions(get(name)),["LEM"],name);
  assert.equal(get("rejected").verified,false);
  assert.match(get("rejected").reason,/^Expected a universe/);
});
