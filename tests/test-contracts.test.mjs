import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {observeTestCases} from "../web/cubist/test-pragmas.mjs";
import {Translator} from "../web/translator/translate.mjs";

const module=await createCubical();
const checked=async(t,source,options={})=>{
  const {program,result}=await checkProgram(t,source,{module,options:{testMode:true,...options}});
  return {program,result,report:observeTestCases(program,result)};
};

test("ordinary program and raw translator entry reject test metadata",async t=>{
  const source="# test(untrusted) # expect_error(E606) def x : Unit := tt;";
  await assert.rejects(checkProgram(t,source,{module}),/explicit test mode/);
  const {program}=await checkProgram(t,"",{module});
  assert.throws(()=>new Translator({checker:program.checker}).translate(source),/explicit test mode/);
});

test("one expected refusal cannot hide a second failure, a cascade or a missing target",async t=>{
  const source="# test(refusal) # expect_error(E606) def x : Void := tt; # test(client) # expect_error(E340) def y := x;";
  const {program,result,report}=await checked(t,source);
  assert.deepEqual(report.cases[0].failures,[]);
  assert.ok(report.cases[1].failures.length,"dependent failures are not an expected mathematical refusal");
  result.gaps.push({...result.gaps[0]});
  assert.ok(observeTestCases(program,result).cases[0].failures.length,"every failure is counted");
  result.gaps=[];delete program.symbols.main__x;
  assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>/not observed/.test(message)));
});

test("warnings match their target and multiplicity",async t=>{
  const {report}=await checked(t,`# test(warning) # expect_warning(W705)
def redundant : (forall x : Unit. Unit) := fun (x : Unit) => tt;
# test(clean) def good : Unit := tt;`);
  assert.deepEqual(report.failures,[]);
  assert.deepEqual(report.cases.map(entry=>entry.failures),[[],[]]);
});

test("exact assumptions include type dependencies and exclude bound hypotheses",async t=>{
  const {report}=await checked(t,`# test(bound) # expect_axioms([])
def local(A : U0, assumption : A) : A := assumption;
# test(type_dependencies) # expect_axioms([Truncate])
def identity(A : U0, value : Truncate(U0,A)) : Truncate(U0,A) := value;
# test(transitive) # expect_axioms([Truncate])
def alias := identity;`);
  assert.deepEqual(report.prerequisites,[]);
  assert.deepEqual(report.failures,[]);
  assert.deepEqual(report.cases.map(entry=>entry.failures),[[],[],[]]);
});

test("an assumption expectation checks every generated member separately",async t=>{
  const {program,result,report}=await checked(t,`import hlevels;
# test(family) # expect_axioms([])
theory T(U < UU0) { M : set U; c : M; }`);
  assert.deepEqual(report.cases[0].failures,[]);
  program.symbols.main__T.axioms=["injected_assumption"];
  assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>message.startsWith("T:")));
});

test("resource exhaustion cannot satisfy an expected refusal",async t=>{
  const {report}=await checked(t,"# test(resource) # expect_error(E606) def x : Unit := tt;",{declarationFuel:{queries:0}});
  assert.ok(report.prerequisites.length);
  assert.deepEqual(report.expectedErrors,[]);
});

for(const [label,sources] of [
  ["missing import",{}],
  ["missing transitive import",{dependency:"import absent; def x := tt;"}],
  ["refused imported declaration",{dependency:"def wrong : Void := tt;"}],
  ["failed imported directive",{dependency:"evaluate tt expecting Unit;"}],
])test(`test contracts retain an unused ${label} failure`,async t=>{
  const source="import dependency; # test(local) def x : Unit := tt;";
  const {program,result}=await checkProgram(t,source,{module,reader:async name=>sources[name]??null,options:{testMode:true}});
  const report=observeTestCases(program,result);
  assert.deepEqual(report.cases[0].failures,[]);
  assert.ok(report.prerequisites.length);
});

test("rebuilt assumptions resolve exact signature identities",async t=>{
  const {report}=await checked(t,`import h1_truncation;
# test(rebuilt) # expect_axioms([LEM[h1_truncation.Trunc]])
def excluded := LEM(Trunc,U0);`);
  assert.deepEqual(report.prerequisites,[]);
  assert.deepEqual(report.failures,[]);
  assert.deepEqual(report.cases[0].failures,[]);
});

test("an imported expected refusal cannot make a dependency successful",async t=>{
  const {program,result}=await checkProgram(t,"import dependency; # test(root) def x := tt;",{module,
    reader:async()=>"# test(imported) # expect_error(E606) def wrong : Void := tt;",options:{testMode:true}});
  const report=observeTestCases(program,result);
  assert.ok(report.prerequisites.length);
  assert.deepEqual(report.expectedErrors,[]);
});


test("directive contracts observe successful evaluations and exactly owned refusals",async t=>{
  const {report}=await checked(t,`# test(evaluate_ok) evaluate tt expecting tt;
# test(evaluate_bad) # expect_error(E325) evaluate tt expecting Unit;
# test(print_ok) print(typeof(tt));`);
  assert.deepEqual(report.prerequisites,[]);
  assert.deepEqual(report.failures,[]);
  assert.deepEqual(report.cases.map(entry=>entry.failures),[[],[],[]]);
});

test("an imported positive contract is a prerequisite of selected local cases",async t=>{
  const {program,result}=await checkProgram(t,"import dependency; # test(root) def x := tt;",{module,
    reader:async()=>"# test(imported) # expect_axioms([]) def x := Truncate(U0,Unit);",options:{testMode:true}});
  assert.ok(observeTestCases(program,result).prerequisites.some(message=>message.startsWith("imported:")));
});
