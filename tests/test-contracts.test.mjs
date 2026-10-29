import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram,legacyArchiveReader} from "./check-program.mjs";
import {observeTestCases} from "../web/cubist/test-pragmas.mjs";
import {Translator} from "../web/translator/translate.mjs";

const module=await createCubical();
const checked=async(t,source,options={},reader=undefined)=>{
  const {program,result}=await checkProgram(t,source,{module,...(reader?{reader}:{}),options:{testMode:true,...options}});
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
  const {report}=await checked(t,`import classical_axioms;
# test(bound) # expect_axioms([])
def local(A : U0, assumption : A) : A := assumption;
# test(type_dependencies) # expect_axioms([LEM])
def identity(value : LEM(U0) = LEM(U0)) : LEM(U0) = LEM(U0) := value;
# test(transitive) # expect_axioms([LEM])
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

// The legacy builtins are an archive module's, as legacy uses them.
test("assumption expectations name axioms and legacy builtins by their labels",async t=>{
  for(const [source,reader] of [[`import classical_axioms;
# test(library) # expect_axioms([LEM])
def excluded := LEM(U0);
def Pointed := axiom UNat;
# test(qualified) # expect_axioms([Choice, main::Pointed])
def both : AxiomOfChoice(U0) and UNat := (Choice(U0), Pointed);`],[`import legacy;
# test(legacy) # expect_axioms([LEM[Truncate], Truncate, TruncateElim])
def excluded := legacy::double_negation;`,legacyArchiveReader()]]) {
    const {report}=await checked(t,`import unat;\n${source}`,{},reader);
    assert.deepEqual(report.prerequisites,[]);
    assert.deepEqual(report.failures,[]);
    assert.deepEqual(report.cases.map(entry=>entry.failures),report.cases.map(()=>[]));
  }
  const {report}=await checked(t,`import classical_axioms;
# test(legacy) # expect_axioms([LEM[Truncate]])
def excluded := LEM(U0);`);
  // An import of classical_axioms shadows the legacy builtin.
  assert.deepEqual(report.cases[0].failures,["Unknown checked assumption LEM[Truncate].",
    "excluded: expected assumptions [LEM[Truncate]], observed [LEM]."]);
});

test("an imported expected refusal cannot make a dependency successful",async t=>{
  const {program,result}=await checkProgram(t,"import dependency; # test(root) def x := tt;",{module,
    reader:async()=>"# test(imported) # expect_error(E606) def wrong : Void := tt;",options:{testMode:true}});
  const report=observeTestCases(program,result);
  assert.ok(report.prerequisites.length);
  assert.deepEqual(report.expectedErrors,[]);
  assert.deepEqual(report.cases.find(entry=>entry.id==="imported").failures,[]);
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
    reader:async()=>"# test(imported) # expect_axioms([]) def x := axiom Unit;",options:{testMode:true}});
  assert.ok(observeTestCases(program,result).prerequisites.some(message=>message.startsWith("imported:")));
});


test("unannotated declarations must have an observed output, including unused dependencies",async t=>{
  const {program,result}=await checkProgram(t,"import dependency; # test(root) def root := tt; def tail := tt;",{module,
    reader:async()=>"def imported := tt;",options:{testMode:true}});
  delete program.symbols.main__tail;
  delete program.symbols.dependency__imported;
  const report=observeTestCases(program,result);
  assert.ok(report.failures.some(message=>message.includes("main.tail")));
  assert.ok(report.prerequisites.some(message=>message.includes("dependency.imported")));
});


test("case ownership takes precedence over an error span in earlier retained source",async t=>{
  const {program,result}=await checked(t,"# test(first) # expect_error(E606) def first : Void := tt; # test(second) # expect_error(E606) def second : Void := tt;");
  result.gaps[1].start=result.gaps[0].start;
  const report=observeTestCases(program,result);
  assert.deepEqual(report.cases.map(entry=>entry.failures),[[],[]]);
  assert.deepEqual(report.expectedErrors.map(error=>error.name),["first","second"]);
});

for(const target of ["def second : Void := tt;","evaluate tt expecting Unit;"])
  test(`an unannotated target cannot supply another case's refusal: ${target}`,async t=>{
    const source=`# test(first) # expect_error(E606) def first : Unit := tt; ${target}`;
    const {program,result}=await checked(t,source);
    result.gaps[0].start=source.indexOf("def first");
    const report=observeTestCases(program,result);
    assert.ok(report.cases[0].failures.length,"the successful first declaration did not refuse");
    assert.equal(report.failures.length,1,"the unannotated refusal remains a global failure");
    assert.deepEqual(report.expectedErrors,[]);
  });

for(const failure of ["deadline","budget","fuel","resource"])
  test(`resource dependency cascades remain prerequisites: ${failure}`,async t=>{
    const {program,result}=await checked(t,"def first : Void := tt; # test(uses) def uses := first; def unannotated := first;");
    program.symbols.main__first.failure=failure;
    const report=observeTestCases(program,result);
    assert.equal(report.prerequisites.length,3);
    assert.deepEqual(report.failures,[]);
    assert.deepEqual(report.cases[0].failures,[]);
    assert.deepEqual(report.expectedErrors,[]);
  });

test("a duplicate's observation never borrows the original declaration's failure state",async t=>{
  const {program,result}=await checked(t,"def x := tt; # test(duplicate) # expect_error(E872) def x := tt;");
  for(const state of [{failure:"fuel"},{failure:null,blockedBy:"main__missing"}]) {
    Object.assign(program.symbols.main__x,state);
    const report=observeTestCases(program,result);
    assert.deepEqual(report.prerequisites,[]);
    assert.deepEqual(report.cases[0].failures,[]);
    assert.deepEqual(report.expectedErrors.map(error=>error.caseId),["duplicate"]);
  }
});

test("owned expected errors remain observations when an unused import fails",async t=>{
  const {program,result}=await checkProgram(t,"import absent; # test(refusal) # expect_error(E606) def bad : Void := tt;",{module,
    reader:async()=>null,options:{testMode:true}});
  const report=observeTestCases(program,result);
  assert.ok(report.prerequisites.length,"the experiment still fails its preconditions");
  assert.deepEqual(report.cases[0].failures,[]);
  assert.deepEqual(report.expectedErrors.map(error=>error.name),["bad"]);
});

test("incremental entries cannot inherit fixture test mode",async t=>{
  const {program}=await checked(t,"# test(base) def base := tt;");
  await assert.rejects(program.checkEntry("# test(query) def query := tt;","scratch"),/Test pragmas require explicit test mode/);
  assert.ok(!program.modules.has("scratch"));
});


test("an imported unannotated warning is a prerequisite, not a local semantic failure",async t=>{
  const {program,result}=await checkProgram(t,"import dependency; # test(root) def x := tt;",{module,
    reader:async()=>"# test(imported) def good := tt; def unused : forall x : Unit. Unit := fun (x : Unit) => tt;",options:{testMode:true}});
  const report=observeTestCases(program,result);
  assert.ok(report.prerequisites.some(message=>message.includes("W705")));
  assert.deepEqual(report.failures,[]);
});
