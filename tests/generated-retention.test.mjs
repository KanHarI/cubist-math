import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {snapshotSyntax,visitSyntax} from "../web/translator/syntax-graph.mjs";

const module=await create();
const options={collectGeneration:true};
const source=`import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M; }
initial N : T(U0);
free F(A : U0) : T(U0) on A;`;

test("CB5: generated retention is optional inert syntax and leaves checking unchanged",async t=>{
  const baseline=await checkProgram(t,source,{module});
  const {program,result}=await checkProgram(t,source,{module,options});
  assert.deepEqual(result.gaps,[]);
  for(const key of ["publications","instructionCount","outputs","directiveFuel"])
    assert.deepEqual(result[key],baseline.result[key],key);
  assert.equal(baseline.program.generation.size,0);
  const retained=program.generation.get("main");
  const declarations=retained.flatMap(group=>group.declarations);
  for(const name of ["T","T.Hom.compose","T.Iso.inverse","N","N.fold_map","F","F.gen"])
    assert.ok(declarations.some(d=>d.name.text===name||d.constructors?.some(c=>c.name.text===name)),name);
  assert.ok(snapshotSyntax(retained).nodes.length>0,"no live checker, environment or theory objects");
  for(const declaration of declarations) {
    assert.equal(declaration.bindings.format,"cubist-bindings-1");
    assert.equal(program.compilationBindings.declaration(`main__${declaration.name.text}`).binding.id,declaration.name.bindingId);
    let references=0;
    visitSyntax(declaration,node=>{
      if(node?.kind==="bindingReference") {
        references++;
        assert.ok(node.origin);
        assert.ok(!Object.hasOwn(node,"value"),"references retain data, not elaborated values");
      }
    });
    assert.ok(references>0,declaration.name.text);
  }
});

test("CB5: failed and blocked families retain artifacts without publishing definitions",async t=>{
  const {program,result}=await checkProgram(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; law bad : c = tt; }`,{module,options});
  assert.ok(result.gaps.length>0);
  const groups=program.generation.get("main"),publications=program.publications.get("main");
  for(const [id,state] of [["T:base","failed"],["T:hom","blocked"],["T:iso","blocked"]]) {
    assert.equal(publications.find(p=>p.id===id).state,state);
    const group=groups.find(g=>g.id===id);
    assert.ok(group.declarations.length);
    for(const d of group.declarations) {
      assert.equal(program.kernel.definitions.has(`main__${d.name.text}`),false);
      assert.ok(d.bindings);
    }
  }
});

test("CB5: imported artifacts retain producer origins and disappear on recheck",async t=>{
  const fixture="theory Parent(U < UU0) { M : U; }";
  const {program}=await checkProgram(t,"import fixture; theory Child(U < UU0) extends Parent {}",{
    module,options,reader:name=>name==="fixture"?fixture:Promise.reject(Error(name)),
  });
  const parent=program.generation.get("fixture").flatMap(g=>g.declarations).find(d=>d.name.text==="Parent");
  const child=program.generation.get("main").flatMap(g=>g.declarations).find(d=>d.name.text==="Child");
  assert.equal(parent.name.origin.module,"fixture");
  assert.equal(child.name.origin.module,"main");
  assert.notEqual(parent.name.bindingId,child.name.bindingId);
  await program.check("def replacement : Unit := tt;","main");
  assert.equal(program.generation.has("fixture"),false);
  assert.deepEqual(program.generation.get("main"),[]);
});
