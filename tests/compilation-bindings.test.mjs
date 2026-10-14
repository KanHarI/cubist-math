import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";

const module=await create();

test("declaration identities and source ownership do not depend on scope collection",async t=>{
  const dep="inductive Two : set U0 { left_; right_; } def saved : Two := left_;";
  const source="import dep; def saved : Two := right_; def kept : Two := saved; def saved : Two := left_;";
  const declarations=[];
  for(const collectScopes of [false,true]) {
    const program=new CubicalProgram(module,async()=>dep,{collectScopes,scopeRevision:"same-inputs"});
    t.after(()=>program.dispose());
    const result=await program.check(source,"main");
    assert.equal(result.gaps.length,1);assert.equal(result.gaps[0].duplicate,true);
    const registry=program.compilationBindings;
    const imported=registry.declaration("dep__saved").binding,local=registry.declaration("main__saved").binding;
    assert.notEqual(imported.id,local.id);
    assert.equal(imported.origin.module,"dep");
    assert.equal(local.origin.start,source.indexOf("saved"));
    assert.equal(registry.ofValue(program.modules.get("main").get("saved")).id,local.id);
    const constructor=registry.ofValue(program.modules.get("dep").get("right_"));
    assert.equal(constructor.origin.module,"dep");assert.equal(constructor.label,"right_");
    const squash=registry.ofValue(program.modules.get("dep").get("Two.squash"));
    assert.equal(squash.label,"Two.squash");
    assert.equal(squash,registry.declaration("dep__Two:constructor:2").binding);
    assert.notEqual(squash.id,registry.declaration("dep__Two").binding.id);
    declarations.push(registry.table.snapshot().bindings.filter(binding=>binding.role==="declaration"));
    if(collectScopes)assert.equal(program.scopeRecorder.table,registry.table);
  }
  assert.deepEqual(declarations[0],declarations[1]);
});

test("a declaration reservation never supplies the value of a refused declaration",async t=>{
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  const result=await program.check("def bad : Unit := Unit; def client : Unit := bad; def good : Unit := tt;","main");
  assert.deepEqual(result.gaps.map(gap=>gap.name),["bad","client"]);
  assert.ok(program.compilationBindings.declaration("main__bad"));
  assert.equal(program.modules.get("main").get("bad").tag,"Untranslated");
  assert.equal(program.kernel.definitions.has("main__bad"),false);
  assert.equal(program.kernel.definitions.has("main__client"),false);
  assert.equal(program.kernel.definitions.has("main__good"),true);
});

test("failed constructors keep distinct declared identities and the common failure root",async t=>{
  for(const collectScopes of [false,true]) {
    const program=new CubicalProgram(module,async()=>"",{collectScopes});t.after(()=>program.dispose());
    const result=await program.check("inductive T : set U0 { c; d(x : Missing); } def client : Unit := c;","main");
    assert.deepEqual(result.gaps.map(gap=>gap.name),["T","client"]);
    const registry=program.compilationBindings,env=program.modules.get("main");
    const identities=["T","c","d","T.squash"].map(name=>{
      const value=env.get(name),binding=registry.ofValue(value);
      assert.equal(value.tag,"Untranslated");
      assert.equal(binding.label,name);
      assert.equal(binding,registry.declaration(`main__${name}`).binding);
      assert.equal(value.blockedBy,"main__T");
      return binding.id;
    });
    assert.equal(new Set(identities).size,4);
    assert.equal(env.get("client").blockedBy,"main__T");
  }
});

test("edited source replaces its compilation identities while cached REPL extensions preserve them",async t=>{
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check("def saved : Unit := tt;","main")).gaps,[]);
  const before=program.compilationBindings,original=before.declaration("main__saved").binding;
  assert.deepEqual((await program.check("import main; def next_ : Unit := saved;","entry",()=>{},{reuseModules:true})).gaps,[]);
  assert.equal(program.compilationBindings,before);
  assert.equal(program.compilationBindings.declaration("main__saved").binding,original);
  assert.deepEqual((await program.check("def saved : Unit := (fun (x : Unit) => x)(tt);","main")).gaps,[]);
  assert.notEqual(program.compilationBindings,before);
  assert.notEqual(program.compilationBindings.declaration("main__saved").binding.id,original.id);
  assert.throws(()=>program.compilationBindings.table.get(original.id),/Unknown binding identity/);
});
