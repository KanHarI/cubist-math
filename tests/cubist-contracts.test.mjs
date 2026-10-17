import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile,readdir} from "node:fs/promises";
import {fileURLToPath} from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {sourceTestCases} from "../web/cubist/test-pragmas.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {checkedSource} from "../tools/checked-source.mjs";
import {precondition} from "./module-observation.mjs";

const directory=new URL("./fixtures/contracts/",import.meta.url),module=await createCubical();
const ids=new Set();
for(const file of (await readdir(directory)).filter(file=>file.endsWith(".cubist")).sort()) {
  const path=fileURLToPath(new URL(file,directory)),source=await readFile(path,"utf8"),name=file.slice(0,-7);
  const cases=sourceTestCases(parse(source));
  assert.ok(cases.length,`${file} declares no test cases`);
  let checked;
  for(const {id} of cases) {
    assert.ok(!ids.has(id),`Duplicate test case ${id}`);ids.add(id);
    test(id,async()=>{
      checked??=checkedSource(source,name,{module,reader:sourceReader({path}),options:{testMode:true}});
      const {contracts}=await checked;
      precondition(()=>assert.deepEqual(contracts.prerequisites,[],`${id}: imported and resource failures`));
      assert.deepEqual(contracts.failures,[],`${id}: unexpected diagnostics outside annotated cases`);
      const observed=contracts.cases.find(entry=>entry.id===id);
      assert.ok(observed,`${id}: target was not observed`);
      assert.deepEqual(observed.failures,[],id);
    });
  }
}
