import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile,readdir} from "node:fs/promises";
import {fileURLToPath} from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {sourceTestCases,selectTestCases} from "../web/cubist/test-pragmas.mjs";
import {moduleOfFile,sourceReader} from "../tools/module-sources.mjs";
import {checkedSource} from "../tools/checked-source.mjs";
import {precondition} from "./module-observation.mjs";

const directory=new URL("./fixtures/contracts/",import.meta.url),module=await createCubical();
const fixtures=[];
for(const file of (await readdir(directory,{recursive:true})).filter(file=>file.endsWith(".cubist")).sort()) {
  const path=fileURLToPath(new URL(file,directory)),source=await readFile(path,"utf8"),name=moduleOfFile(file);
  const cases=sourceTestCases(parse(source));
  assert.ok(cases.length,`${file} declares no test cases`);
  fixtures.push({path,source,name,cases,checked:null});
}
const cases=fixtures.flatMap(fixture=>fixture.cases.map(entry=>({...entry,fixture})));
assert.equal(new Set(cases.map(entry=>entry.id)).size,cases.length,"test case IDs are unique across fixtures");
const selected=process.env.CUBIST_TEST_CASES===undefined?null:JSON.parse(process.env.CUBIST_TEST_CASES);
for(const {id,fixture} of selectTestCases(cases,selected))test(id,async()=>{
  const {source,name,path}=fixture;
  fixture.checked??=checkedSource(source,name,{module,reader:sourceReader({path}),options:{testMode:true}});
  const {contracts}=await fixture.checked;
  precondition(()=>assert.deepEqual(contracts.prerequisites,[],`${id}: imported and resource failures`));
  assert.deepEqual(contracts.failures,[],`${id}: unexpected diagnostics outside annotated cases`);
  const observed=contracts.cases.find(entry=>entry.id===id);
  assert.ok(observed,`${id}: target was not observed`);
  assert.deepEqual(observed.failures,[],id);
});
