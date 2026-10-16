import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {bindingUses,bindingSyntaxView} from "../web/cubist/binding-syntax.mjs";

const module=await create();
test("ordinary source and imported inheritance retain their exact ordered interfaces",async t=>{
  const library=sourceReader(),parent=`import hlevels; import nat;
theory P(U < UU0, n : Nat) {
  M : set U; op(p : n = n) : M; def n : Nat := zero;
}`;
  const {program,result}=await checkProgram(t,`import parent;
theory C(U < UU0, n : Nat) extends P {}
initial N : C(U0, succ(zero));
def good : N := N.op(refl(succ(zero)));
def wrong : N := N.op(refl(zero));`,{module,reader:(name,from)=>name==="parent"?parent:library(name,from)});
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["wrong","E606"]]);
  for(const [name,source] of [["parent__P","parent"],["main__C","main"]]) {
    const record=program.checker.theories.get(name);
    assert.equal(record.origin.module,source);
    assert.equal(record.bindingSyntax.format,"cubist-bindings-1");
    const operation=record.fields.find(f=>f.label==="op"),helper=record.derived.find(f=>f.label==="n");
    const ids=bindingUses(bindingSyntaxView(record.bindingSyntax,operation.type)).map(use=>use.id);
    assert.ok(ids.includes(record.params[0].id));
    assert.ok(!ids.includes(helper.id));
    assert.equal(record.homSupport.status,"conditional");
  }
  assert.ok(result.links.every(link=>link.end<=result.source.length));
  assert.ok(result.outputs.find(o=>o.name==="N.fold").verified);
});
