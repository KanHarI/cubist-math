import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";

const module=await create();
const tree=(await readFile(new URL("../library/universe_smallness.cubist",import.meta.url),"utf8"))
  .split("// No small family")[0].replace("import contractible_maps;","");

test("an inspected induction hypothesis opens its exact introduction or later use context",async t=>{
  for(const imported of [false,true])await t.test(imported?"imported":"local",async t=>{
    const source=imported?"import fixture; def outside : Unit := tt;":tree,owner=imported?"fixture":"main";
    const reader=async()=>tree;
    const off=await checkProgram(t,source,{module,reader});
    const on=await checkProgram(t,source,{module,reader,options:{collectScopes:true}});
    assert.deepEqual(on.result.gaps,[]);
    assert.deepEqual(on.result.outputs,off.result.outputs);
    assert.deepEqual(on.result.links,off.result.links);
    assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
    const uses=[...on.program.views].filter(([,view])=>view.module===owner&&view.node.name==="ih"
      &&(view.node.isBinding||view.node.start===tree.indexOf("ih(m.1)")));
    assert.equal(uses.length,2);
    const scopes=[];
    for(const [binding,observed] of uses) {
      assert.deepEqual(off.program.inspect(binding).contextEntry,{module:owner,scope:null});
      const view=on.program.inspect(binding),entry=view.contextEntry;
      assert.equal(entry.module,owner);
      const point=on.program.scopePoints.get(entry.scope);
      assert.ok(point?.available,point?.reason);
      assert.equal(point.phase,observed.node.isBinding?"inspection":"expression");scopes.push(point.id);
      const before=on.program.kernel.work(),session=new ContextualSession(on.program,point.id);
      try {
        for(const [input,kind] of [["typeof ih","type"],["typeof children","type"],
          ["typeof m",observed.node.isBinding?"error":"type"],["outside","error"]]) {
          const [answer]=await session.run(input);
          assert.equal(answer.kind,kind,JSON.stringify(answer));
        }
        const [saved]=await session.run("let saved := ih");assert.equal(saved.kind,"defined");
        const [again]=await session.run("typeof saved");assert.equal(again.kind,"type");
      } finally {session.dispose();}
      assert.deepEqual(on.program.kernel.work(),before);
    }
    assert.equal(new Set(scopes).size,2,"the same hypothesis has different introduction and use contexts");
    if(imported)assert.equal(on.program.inspect(on.result.outputs.find(o=>o.name==="outside").binding).contextEntry,null);
  });
});

test("inspection preserves distinct refinements of one written lambda occurrence",async t=>{
  const source=`inductive Nat { zero; succ(n : Nat); }
def f(a, b : Nat) : Nat := match a, b {
  zero, zero => zero;
  _, _ => (fun (v : Nat) => v)(a);
};`;
  const {program,result}=await checkProgram(t,source,{module,options:{collectScopes:true}});
  assert.deepEqual(result.gaps,[]);
  const uses=[...program.views].filter(([,view])=>view.node.name==="v"&&!view.node.isBinding
    &&view.node.start===source.lastIndexOf("v)(a)"));
  assert.ok(uses.length>=2);
  const scopes=new Set(),answers=new Set();
  for(const [binding] of uses) {
    const entry=program.inspect(binding).contextEntry;scopes.add(entry.scope);
    const session=new ContextualSession(program,entry.scope);
    try {answers.add((await session.run("typed(a = zero, refl(a))"))[0].kind);}
    finally {session.dispose();}
  }
  assert.equal(scopes.size,uses.length,"each elaborated occurrence keeps its own context");
  assert.deepEqual([...answers].sort(),["error","value"]);
});
