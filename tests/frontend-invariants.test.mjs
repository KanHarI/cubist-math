import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {mkdir,writeFile} from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {ciSeeds,caseLimit,configuration,generate,minimize} from "./fixtures/frontend-invariants.mjs";

const count=Number(process.env.CUBIST_GENERATION_CASES??ciSeeds.length);
assert.ok(Number.isSafeInteger(count)&&count>=1&&count<=caseLimit,"1..64 bounded cases");
const module=await create(),library=sourceReader();
async function verify(config) {
  const spec=generate(config);
  const program=new CubicalProgram(module,(name,importer)=>spec.fixtures[name]??library(name,importer));
  try {
    const result=await program.check(spec.source,"main");
    assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),spec.expectedGaps.map(name=>[name,"E606"]),"diagnostic contract");
    for(const name of spec.accepted) {
      const output=result.outputs.find(o=>o.name===name);
      assert.equal(output?.verified,true,`${name} must check`);assert.deepEqual(output.axioms,[],name);
    }
    const records=[...program.checker.theories.values()];
    const record=records.find(r=>r.name===spec.model);
    assert.equal(record.support.hom.status,"conditional");
    for(const name of ["M","c","op"])
      assert.ok(record.fields.some(field=>field.name===spec.names[name]),`field correspondence ${name}`);
    if(config.inherited) {
      const parent=records.find(r=>r.name==="T");
      for(const name of ["M","c","op"])
        assert.equal(record.dependencies.fields.find(f=>f.name===spec.names[name]).originIdentity,parent.fields.find(f=>f.name===name).identity);
    }
    for(const suffix of ["Hom","Hom.id","Hom.compose","Iso","Iso.id"])
      assert.ok(Object.values(program.symbols).some(o=>o.name===`${spec.model}.${suffix}`&&o.verified),`artifact ${suffix}`);
    const location=spec.parent.indexOf(spec.labelScope),binder=location+spec.labelScope.indexOf("c : M");
    for(const match of spec.labelScope.matchAll(/\bc\b/g)) {
      const at=location+match.index;
      const info=program.localSymbols[`${config.imported?"fixture":"main"}__local_${at}`];
      assert.equal(info?.name,"c");assert.equal(info.definitionStart,binder);
      assert.equal(program.inspect(info.binding).expressionText,"c");
    }
    if(config.paths) {
      const gap=result.gaps.find(g=>g.name==="mismatch"),at=spec.source.lastIndexOf("right_");
      assert.equal(gap.start,at);assert.equal(gap.end,at+6);
      assert.equal(result.outputs.find(o=>o.name==="mismatch").searchFuel.searches,0);
    }
    const advice=lint(spec.source).filter(w=>["W705","W706"].includes(w.code));
    // Only advice about the independent ordinary type is applied.
    assert.equal(advice.length,1);assert.equal(advice[0].declaration,"ordinary");
    const rewritten=await program.check(spec.source.replace("forall unused : Unit. Unit","Unit -> Unit"),"main");
    assert.deepEqual(rewritten.gaps.map(g=>[g.name,g.code]),result.gaps.map(g=>[g.name,g.code]));
    assert.deepEqual(rewritten.outputs.filter(o=>o.verified).map(o=>[o.name,o.type,o.axioms]),result.outputs.filter(o=>o.verified).map(o=>[o.name,o.type,o.axioms]));
    // Additional ceilings are audit guards, never larger checker limits.
    const work=program.kernel.work();
    assert.ok(work.queries<50000&&work.instructions<500000,"bounded checker work");
    assert.equal(work.deadlines,0);
    return {queries:work.queries,instructions:work.instructions};
  }finally {program.dispose();}
}
for(let seed=0;seed<count;seed++)test(`FG6: preservation under composed transformations, seed ${seed}`,{timeout:30000},async()=>{
  const config=configuration(seed);
  try {await verify(config);}catch(error) {
    const shrunk=await minimize(config,async next=>{
      try {await verify(next);return false;}catch(candidate){return candidate.code===error.code&&candidate.message===error.message;}
    });
    const directory=new URL("../build/frontend-generation-failures/",import.meta.url);
    await mkdir(directory,{recursive:true});
    await writeFile(new URL(`seed-${seed}.json`,directory),JSON.stringify({seed,error:error.message,...shrunk,...generate(shrunk.config)},null,2)+"\n");
    error.message=`seed ${seed}; reduced case in build/frontend-generation-failures/seed-${seed}.json: ${error.message}`;
    throw error;
  }
});
