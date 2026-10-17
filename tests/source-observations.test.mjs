import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {formatCubist} from "../web/cubist/formatter.mjs";
import {observeTestCases} from "../web/cubist/test-pragmas.mjs";
import {reported,stated} from "../tools/inline-errors.mjs";

const module=await createCubical();
const check=(t,source)=>checkProgram(t,source,{module,options:{testMode:true}});

// Keep presentation goldens independent of the semantic code/range contracts.
for(const file of ["wildcard_refusal","recursive_refusal"])
  test(`migrated refusal retains its diagnostic message: ${file}`,async t=>{
    const source=await readFile(new URL(`./fixtures/contracts/${file}.cubist`,import.meta.url),"utf8");
    const {result}=await check(t,source);
    assert.deepEqual(result.gaps.filter(gap=>gap.module!=="main"),[]);
    assert.deepEqual(reported(source,result,"main"),stated(source));
    assert.deepEqual(result.outputs.filter(output=>output.verified&&output.axioms?.length).map(output=>output.name),[]);
  });

test("error anchors preserve token boundaries and target attachment through formatting",async t=>{
  // A top-level mismatch covers the written assignment, including its terminator.
  const source="# test(anchor) # expect_error(E606) # expect_error_at(:= tt;) # expect_searches(0) def bad:Void:=tt;";
  const formatted=formatCubist(source,{printWidth:40});
  assert.equal(formatCubist(formatted,{printWidth:40}),formatted);
  const {program,result}=await check(t,formatted);
  assert.deepEqual(observeTestCases(program,result).cases[0].failures,[]);
  const end=result.gaps[0].end;
  result.gaps[0].end=result.gaps[0].start;
  assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>message.includes("cover exactly")),
    "the published gap range remains observable independently of the structured site");
  result.gaps[0].end=end;
  result.gaps[0].diagnostic.primary.module="different_source";
  assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>message.includes("cover exactly")));
});

for(const [anchor,body,count] of [["missing","tt",0],["tt","typed(tt = tt,refl(tt))",3]])
  test(`source anchors reject ${count} matching occurrences`,async t=>{
    const {program,result}=await check(t,`# test(anchor) # expect_error(E606) # expect_error_at(${anchor}) def bad : Void := ${body};`);
    assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>message.endsWith(`found ${count}.`)));
  });

test("an absent work counter cannot satisfy an exact zero expectation",async t=>{
  const {program,result}=await check(t,"# test(work) # expect_searches(0) def identity(x : Unit) : Unit := x;");
  assert.deepEqual(observeTestCases(program,result).cases[0].failures,[]);
  delete program.symbols.main__identity.searchFuel;
  assert.ok(observeTestCases(program,result).cases[0].failures.some(message=>message.includes("no counter")));
});

for(const [pragma,target] of [
  ["expect_error_at()","def bad : Void := tt;"],
  ["expect_error_at((tt])","def bad : Void := tt;"],
  ["expect_error_at(tt)","def good := tt;"],
  ["expect_searches(-1)","def good := tt;"],
  ["expect_searches(1.5)","def good := tt;"],
  ["expect_searches(9007199254740992)","def good := tt;"],
  ["expect_searches(0)","inductive T { point; }"],
])test(`refuse unsupported source/work contract ${pragma}`,()=>{
  assert.throws(()=>parse(`# test(invalid) # ${pragma} ${target}`),/Invalid test pragma/);
});
