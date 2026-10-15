import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {sourceBindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {resolveBindingSyntax,cloneBindingSyntax,sameBindingSyntax,bindingUses} from "../web/cubist/binding-syntax.mjs";
import {sourceOrigin} from "../web/cubist/bindings.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";

const wasm=await create();
const base=`import nat; import hlevels;
inductive Two { choice; other; }
def original(n : Nat) : add(n, zero) = n := nat_add_zero(n);
def zero_if(n : Nat, h : n = zero) : add(n, zero) = zero {
  calc { add(n, zero) = n by original(n); _ = zero by h; }
}
simp_rule original;
simp_set saved := [original];`;

test("retained proof references survive cloning, source-set expansion and destination shadowing",async t=>{
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  assert.deepEqual((await program.check(base,"base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table;
  const source=`
def from_set(n : Nat) : add(n, zero) = n { simp only [saved]; }
def shadow_set(n : Nat, saved : Unit) : add(n, zero) = n { simp only [saved]; }
def excluded(n : Nat) : add(n, zero) = n { simp without [saved]; }
def absent_set(n : Nat) : add(n, zero) = n { simp only [absent]; }
def local_copy(n : Nat, h : add(n, zero) = n) : n = n { simp only [h] at h as h; exact h; }
def premise(n : Nat, h : n = zero) : add(n, zero) = zero { simp only [zero_if] with [h]; }
def wrong_premise(n : Nat, h : n = succ(zero)) : add(n, zero) = zero { simp only [zero_if] with [h]; }
def supplied(n : Nat, h : add(n, zero) = n) : n = n { simpa only [original] using h; }
def slots(n : Nat, other : add(n, zero) = n, b : Two) : add(n, zero) = n {
  match b { choice => { exact other; } other => { simp only [other] with [other]; } }
}
def unfolded(n : Nat) : Nat := with unfolding [original] { n };
def universe_hint(U < UU0, A : U, x : A) : A := with unfolding [original] { x };
def local_hint(original : Nat) : Nat := with unfolding [original] { original };
def absent_hint : Nat := with unfolding [later] { zero };
`;
  const inputs=sourceBindingInputs(registry,program.modules.get("base"),{
    reserved:reservedReferences(source),simpRegistry:program.simpRegistries.get("base")});
  const records=parse(source).declarations.map((declaration,index)=>{
    const owner=["proofs",String(index)],origin=sourceOrigin({revision:registry.revision,module:"proofs",
      start:declaration.name.start,end:declaration.name.end});
    const binding=table.allocate(owner,{role:"declaration",label:declaration.name.text,origin});
    const syntax=resolveBindingSyntax(declaration,{...inputs,table,owner,source:{revision:registry.revision,module:"proofs"}});
    assert.doesNotThrow(()=>snapshotSyntax(syntax));
    const copied=cloneBindingSyntax(JSON.parse(JSON.stringify(syntax)),table,[...owner,"copy"]).syntax;
    assert.equal(sameBindingSyntax(syntax,copied),true);
    return {binding,syntax:copied};
  });
  const captured=inputs.simpSets.get("saved").rules[0].id;
  assert.ok(bindingUses(records[0].syntax).some(use=>use.id===captured));
  const checker=Object.create(program.checker);checker.bindingName=label=>`proofs__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"proofs",compilationBindings:registry,
    simpRegistry:program.simpRegistries.get("base")});
  const destination=parse(`simp_set saved := []; simp_set absent := [original];
    def original : Unit := tt; def later : Nat := zero; def h : Unit := tt;`);
  const result=translator.translateSyntax({items:[...destination.items,...records.map(({binding,syntax})=>bindingDeclaration(binding,syntax))]},
    source,new Map([...program.modules.get("base"),...inputs.env]));
  const failures=result.declarations.filter(d=>d.status!=="checked-native-cubical");
  assert.deepEqual(failures.map(d=>d.name),["excluded","absent_set","wrong_premise","local_hint","absent_hint"],JSON.stringify(failures.map(d=>[d.name,d.reason])));
  assert.match(failures[1].reason,/Untranslated name: absent/);
  assert.match(failures[3].reason,/No checked definition to unfold: original/);
  assert.match(failures[4].reason,/Untranslated name: later/);
  assert.ok(failures.every(d=>!d.reason.includes("\u0000id")));

  // Naming the original theorem in the destination does not replace a
  // missing checked receipt for the retained set's member.
  const env=new Map([...program.modules.get("base"),...inputs.env]);
  env.delete(inputs.adapter.key(captured));
  const refusal=translator.translateSyntax({declarations:[bindingDeclaration(records[0].binding,records[0].syntax)]},source,env);
  assert.equal(refusal.declarations[0].status,"not-translated");
  assert.match(refusal.declarations[0].reason,/Untranslated/);
});

test("imported inherited proof bodies keep their source simplification set",async t=>{
  const read=sourceReader(),parent=base+`
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) {
  M : set U;
  def equation(n : Nat, x : Edge) : Nat := match x {
    lo => add(n, zero); hi => n;
  } obligations by { simp only [saved]; };
  def copy(n : Nat, h : add(n, zero) = n, x : Edge) : Nat := match x {
    lo => add(n, zero); hi => n;
  } obligations by { simp only [h] at h as h2; simpa only [h] using h2; };
  def unfolded(n : Nat) : Nat := with unfolding [original] { n };
}`;
  const program=new CubicalProgram(wasm,name=>name==="parent"?parent:read(name));t.after(()=>program.dispose());
  const source=`import hlevels; import parent;
simp_set saved := [];
def original : Unit := tt;
theory Child(U < UU0) extends p : Parent {}
def intended(S : Child(U0), n : Nat) : S.equation(n, hi) = n { rfl; }
def copied(S : Child(U0), n : Nat) : S.copy(n, nat_add_zero(n), hi) = n { rfl; }
def wrong(S : Child(U0), n : Nat) : S.equation(n, hi) = succ(n) { rfl; }`;
  const result=await program.check(source,"child");
  assert.deepEqual(result.gaps.map(g=>g.name),["wrong"],JSON.stringify(result.gaps));
  assert.ok(result.outputs.find(d=>d.name==="intended").verified);
});

test("ambiguous source sets fail at consumption without aborting the generated queue",async t=>{
  const read=sourceReader(),rules="import nat; simp_set conflict := [nat_add_zero];";
  const program=new CubicalProgram(wasm,name=>["a","b"].includes(name)?rules:read(name));t.after(()=>program.dispose());
  const source=`import a; import b; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Broken(U < UU0) {
  M : set U;
  def equation(n : Nat, x : Edge) : Nat := match x {
    lo => add(n, zero); hi => n;
  } obligations by { simp only [conflict]; };
}
def independent : Unit := tt;`;
  const result=await program.check(source,"main");
  assert.deepEqual(result.gaps.map(g=>g.name),["Broken.equation"],JSON.stringify(result.gaps));
  assert.match(result.gaps[0].reason,/Simplification set conflict is ambiguous: a, b/);
  assert.ok(result.outputs.find(d=>d.name==="independent").verified);
});

test("substituted proof fields keep their written diagnostic labels and source-owned sites",async t=>{
  const read=sourceReader();
  const prelude=base+"\ninductive Edge { lo; hi; edge : lo = hi; }";
  const fields="theory Parent(U < UU0) { M : set U; fz : zero = zero; fr(n : Nat) : add(n, zero) = n; }";
  const helpers=`
  def field_witness(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { simp only [zero_if] with [fz]; };
  def copy(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { simp only [saved] at fr as h2; simpa only [saved] using h2; };
  def shadow(n : Nat, fr : add(n, zero) = n, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { simp only [saved] at fr as h2; simpa only [saved] using h2; };`;
  for(const imported of [false,true]) {
    const program=new CubicalProgram(wasm,name=>name==="parent"?prelude+fields:read(name));t.after(()=>program.dispose());
    const source=(imported?"import parent;":prelude+fields)+`\ntheory Child(U < UU0) extends p : Parent {${helpers}\n}`;
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["Child.field_witness","E331"],["Child.copy","E454"]],JSON.stringify(result.gaps));
    for(const [index,label,marker] of [[0,"fz","with [fz]"],[1,"fr","at fr as"]]) {
      const gap=result.gaps[index],start=source.indexOf(marker)+(index===0?6:3);
      assert.match(gap.reason,new RegExp(`local(?: hypothesis)?: ${label}\\.`));
      assert.deepEqual([gap.start,gap.end],[start,start+label.length]);
    }
    assert.ok(result.outputs.find(d=>d.name==="Child.shadow").verified);
  }
  // A helper inherited from another module keeps its source binding label.
  // Imported statement spans are the existing CB5 ownership gap.
  const parent=prelude+fields+`\ntheory Middle(U < UU0) extends p : Parent {${helpers}\n}`;
  const program=new CubicalProgram(wasm,name=>name==="middle"?parent:read(name));t.after(()=>program.dispose());
  const source="import middle; theory Child(U < UU0) extends p : Middle {}";
  const result=await program.check(source,"main");
  const gaps=result.gaps.filter(g=>g.module==="main");
  assert.deepEqual(gaps.map(g=>g.name),["Child.field_witness","Child.copy"],JSON.stringify(result.gaps));
  for(const [index,label] of ["fz","fr"].entries()) {
    assert.match(gaps[index].reason,new RegExp(`local(?: hypothesis)?: ${label}\\.`));
  }
});
