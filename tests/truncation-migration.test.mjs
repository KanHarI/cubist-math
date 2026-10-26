import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { validateLedger } from "../tools/migration-ledger.mjs";
import { execFileSync } from "node:child_process";
import { checkTestModule } from "./check-program.mjs";

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
// invalidated; each records the last revision at which it passed.
test("G4: the checked migration ledger has exact pins, records its retired comparisons and defers the H2 tower declarations",async()=>{
  const ledger=JSON.parse(await readFile(new URL("../docs/roadmaps/hott/h1-truncation-ledger.json",import.meta.url),"utf8"));
  assert.equal(validateLedger(ledger).size,12);
  assert.deepEqual(ledger.retired.map(record=>[record.comparison,record.lastPassing,record.changes.length]),
    [["zorn_chain_complete","21f55b55",1],["classical_axioms","21f55b55",4]]);
  assert.deepEqual(ledger.deferred,["tower_induction_large","tower_relative_induction"]);
  assert.throws(()=>validateLedger({...ledger,changes:[...ledger.changes,ledger.retired[0].changes[0]]}),
    /belongs to the retired zorn_chain_complete comparison/);
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

test("both remaining documented ledger comparisons verify their pinned changes and local public dependencies",()=>{
  const cases = [
    ["cauchy_quotient","cubist-tests/h1_cauchy_quotient.cubist",null,11],
    ["field_logic","docs/examples/h1/migrations/field_logic.cubist","FieldProp,small_mere_eliminate",1],
  ];
  for (const [module,file,scope,count] of cases) {
    const args=["tools/verify-proof-migration.mjs","--no-dependents","--edited-file",file,
      "--ledger","docs/roadmaps/hott/h1-truncation-ledger.json",...(scope ? ["--declarations",scope] : []),module];
    const report=execFileSync(process.execPath,args,{encoding:"utf8"});
    assert.match(report,new RegExp(`${count} exact ledger changes`)); assert.match(report,/0 failures/);
  }
});

test("the library's excluded middle coexists with the archive's legacy builtin, and a program that uses both lists both",async t=>{
  const {get,assumptions}=await check(t,"truncation_rebuilt_classical");
  for(const name of ["old","rebuilt","both"])assert.ok(get(name).verified,get(name).reason);
  assert.deepEqual(assumptions(get("old")),["LEM[Truncate]","Truncate","TruncateElim"]);
  assert.deepEqual(assumptions(get("rebuilt")),["LEM"]);
  assert.deepEqual(assumptions(get("both")),["LEM","LEM[Truncate]","Truncate","TruncateElim"]);
  assert.equal(get("rejected").verified,false);
  assert.match(get("rejected").reason,/^Expected a universe/);
});
