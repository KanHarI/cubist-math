import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {BindingTable,LexicalContext,SlotOutcomes,bindingResolution,reservedResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,substituteBindingSyntax,sameBindingSyntax,cloneBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {DependencyAnalysis} from "../web/cubist/dependencies.mjs";

function setup() {
  const source={revision:"source",module:"main"},table=new BindingTable("compilation");
  let context=new LexicalContext(["Unit","tt"].map(label=>[label,reservedResolution(label)])),serial=0;
  const allocate=(label,role="helper")=>table.allocate(["interface"],{role,label,origin:sourceOrigin({...source,start:0,end:1})});
  const bind=record=>{context=context.bind(record.label,bindingResolution(record.id));};
  const resolve=text=>resolveBindingSyntax(parse(text,true),{table,source,owner:["syntax",String(serial++)],context});
  return {table,allocate,bind,resolve};
}

test("dependency analysis cannot retarget an earlier header occurrence to a later helper",()=>{
  const {allocate,bind,resolve}=setup();
  const header=allocate("n","parameter");bind(header);
  const earlier=resolve("n = n"),missing=resolve("late");
  const helper=allocate("n"),late=allocate("late");bind(helper);bind(late);
  const analysis=new DependencyAnalysis([{id:header.id,kind:"parameter",label:"n"},
    {id:helper.id,kind:"derived",label:"n",syntax:resolve("tt")},
    {id:late.id,kind:"derived",label:"late",syntax:resolve("tt")}]);
  assert.deepEqual(analysis.dependencies(earlier).map(use=>[use.id,use.category]),[[header.id,"parameter"]]);
  assert.equal(analysis.references(missing)[0].kind,"missing");
  assert.equal(analysis.references(missing)[0].label,"late");
  assert.equal(analysis.first(missing,["helper"]),null);
});

test("complete expansion dependencies retain bare recursive references and their paths",()=>{
  const {allocate,bind,resolve}=setup();
  const recursive=allocate("loop"),wrapper=allocate("wrapper");bind(recursive);bind(wrapper);
  const analysis=new DependencyAnalysis([
    {id:recursive.id,kind:"derived",recursive:true,label:"loop",syntax:resolve("fun (x : Unit) => loop(x)")},
    {id:wrapper.id,kind:"derived",label:"wrapper",syntax:resolve("loop(tt)")},
  ]);
  const hidden=analysis.first(resolve("wrapper = wrapper"),["recursive-helper"]);
  assert.equal(hidden.id,recursive.id);assert.deepEqual(hidden.via,[wrapper.id]);
  assert.equal(analysis.first(resolve("loop"),["recursive-helper"]).id,recursive.id);
  assert.deepEqual(analysis.validateHelpers(),{pending:[]});
});

test("helper cycle validation distinguishes structural recursion from inlining cycles",()=>{
  const {allocate,bind,resolve}=setup(),a=allocate("a"),b=allocate("b");bind(a);bind(b);
  const entries=[{id:a.id,kind:"derived",label:"a",syntax:resolve("b")},
    {id:b.id,kind:"derived",label:"b",syntax:resolve("a")}];
  assert.throws(()=>new DependencyAnalysis(entries).validateHelpers(),/Cycle among nonrecursive helpers: a -> b -> a/);
  assert.deepEqual(new DependencyAnalysis([{...entries[0],recursive:true},entries[1]]).validateHelpers(),{pending:[]});
});

test("pending alternatives and inserted arguments remain explicit until the slot decision",()=>{
  const {table,allocate,bind,resolve}=setup(),outer=allocate("x","parameter"),helper=allocate("helper");
  bind(outer);bind(helper);
  const syntax=resolve("match tt { x => x; }"),slot=syntax.tree.clauses[0].constructor.bindingId;
  const copied=substituteBindingSyntax(syntax,new Map([[outer.id,resolve("helper")]]),table,["substitution"]);
  const analysis=new DependencyAnalysis([{id:helper.id,kind:"derived",label:"helper",syntax:resolve("tt")}]);
  const pending=analysis.references(copied);
  assert.ok(pending.some(use=>use.kind==="deferred"&&use.substitutions.length===1));
  assert.equal(analysis.first(copied,["helper"]),null,"an unselected fallback is conditional");
  const constructor={outcomes:new SlotOutcomes().decide(slot,"constructor")};
  const variable={outcomes:new SlotOutcomes().decide(slot,"variable")};
  assert.equal(analysis.first(copied,["helper"],constructor).id,helper.id);
  assert.equal(analysis.first(copied,["helper"],variable),null);
  assert.equal(sameBindingSyntax(copied,cloneBindingSyntax(copied,table,["clone"]).syntax),true);
  assert.equal(sameBindingSyntax(syntax,resolve("match tt { y => y; }")),false,"pending constructor spelling is semantic");
  const deferredHelper=new DependencyAnalysis([{id:helper.id,kind:"derived",label:"helper",syntax:copied}]);
  assert.ok(deferredHelper.validateHelpers().pending.length>0,"unresolved roles cannot certify expansion readiness");
});
