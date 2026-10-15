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
  const renamed=prelude+fields.slice(0,-1)+helpers+`}
theory Child(U < UU0) extends Parent(fz := gz, fr := gr) {}
theory Grand(U < UU0) extends Child(gz := hz, gr := hr) {}`;
  const copy=new CubicalProgram(wasm,read);t.after(()=>copy.dispose());
  const inherited=await copy.check(renamed,"main");
  assert.equal(inherited.gaps.length,6,JSON.stringify(inherited.gaps));
  for(const gap of inherited.gaps) {
    const label=gap.code==="E331"?"fz":"fr";
    assert.match(gap.reason,new RegExp(`local(?: hypothesis)?: ${label}\\.`));
    assert.equal(renamed.slice(gap.start,gap.end),label);
  }
});

test("freeze edits preserve written field, helper and using references through inheritance",async t=>{
  const prelude="import nat; import hlevels; inductive Edge { lo; hi; edge : lo = hi; }";
  const helper="def lemma(n : Nat) : add(n, zero) = n := nat_add_zero(n);";
  const bodies=`
def by_field(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
  obligations by { simp [fe]; };
def by_helper(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
  obligations by { simp [lemma]; };
def by_using(x : Edge) : Nat := match x { lo => add(zero, zero); hi => zero; }
  obligations by { simpa [nat_add_zero] using fz; };`;
  const sources=[
    prelude+`def fe(n : Nat) : add(n, zero) = n := nat_add_zero(n);
def fz : zero = zero := refl(zero);`+helper+bodies,
    prelude+`theory Parent(U < UU0) { M : set U;
fe(n : Nat) : add(n, zero) = n; fz : zero = zero; ${helper}${bodies}}
theory Child(U < UU0) extends Parent(fe := renamed_fe, fz := renamed_fz) {}`,
  ];
  const run=async source=>{
    const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps,[]);
    assert.ok(result.outputs.filter(d=>/(^|\.)by_/.test(d.name)).every(d=>d.verified&&!d.axioms.length));
    return result;
  };
  for(const source of sources) {
    const result=await run(source);
    for(const [original,text,label] of [
      ["simp [fe];","simp only [fe];","fe"],
      ["simp [lemma];","simp only [lemma];","lemma"],
      ["simpa [nat_add_zero] using fz;","simpa only [nat_add_zero] using fz;","nat_add_zero"],
    ]) {
      const links=result.links.filter(link=>link.freeze?.original===original);
      assert.ok(links.length,original);
      for(const link of links) {
        assert.equal(link.freeze.text,text);
        assert.ok(link.description.endsWith(`using ${label}.`),link.description);
      }
      const edit=links[0].freeze;
      await run(source.slice(0,edit.start)+edit.text+source.slice(edit.end));
    }
  }
});

test("conditional rule failures name the written field in ordinary and inherited proofs",async t=>{
  const prelude="import nat; import hlevels; inductive Edge { lo; hi; edge : lo = hi; }";
  const proof=`def rejected(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
  obligations by { simp only [fc]; };`;
  for(const source of [
    prelude+"def fc(n : Nat, h : n = zero) : add(n, zero) = n := nat_add_zero(n);"+proof,
    prelude+`theory Parent(U < UU0) { M : set U; fc(n : Nat, h : n = zero) : add(n, zero) = n; ${proof}}
theory Child(U < UU0) extends Parent(fc := renamed_fc) {}`,
  ]) {
    const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
    const result=await program.check(source,"main");
    assert.equal(result.gaps.length,source.includes("theory Parent")?2:1,JSON.stringify(result.gaps));
    for(const gap of result.gaps) {
      assert.equal(gap.code,"E456");
      assert.match(gap.reason,/Rule fc has an unproved premise/);
      assert.equal(source.slice(gap.start,gap.end),"fc");
    }
  }
});

test("imported proof sites cannot offer edits or traced links in the client source",async t=>{
  const parent=`import nat; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : set U; fe(n : Nat) : add(n, zero) = n;
  def by_field(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { simp [fe]; };
  def calculated(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { calc { add(n, zero) = n by fe(n); } };
}`;
  const library=sourceReader(),reader=name=>name==="parent"?parent:library(name);
  const run=async source=>{
    const program=new CubicalProgram(wasm,reader);t.after(()=>program.dispose());
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps,[]);
    return result;
  };
  for(const padding of ["","// "+"x".repeat(parent.length)+"\n"]) {
    const source=`import parent;\n${padding}theory Child(U < UU0) extends Parent(fe := gfe) {}`;
    const result=await run(source);
    assert.ok(result.outputs.find(d=>d.name==="Child.by_field").verified);
    assert.ok(result.outputs.find(d=>d.name==="Child.calculated").verified);
    assert.equal(result.links.some(link=>link.freeze||["simplification witness","simplification step",
      "calculation witness","calculation step"].includes(link.role)),false);
    // Generated definition/match annotations still await CB5. They offer
    // no source edits; tactic witnesses and their traced steps must be owned.
    const local=source+"\ndef local_proof(n : Nat) : add(n, zero) = n { simp [nat_add_zero]; }";
    const checked=await run(local),edits=checked.links.filter(link=>link.freeze).map(link=>link.freeze);
    assert.equal(edits.length,1);
    const edit=edits[0];
    assert.equal(edit.start,local.indexOf("simp [nat_add_zero]"));
    assert.equal(edit.text,"simp only [nat_add_zero];");
    await run(local.slice(0,edit.start)+edit.text+local.slice(edit.end));
  }
});

test("an inherited proof cannot edit its parent's source using the child's later rules",async t=>{
  for(const explicit of [true,false]) {
    const source=`import nat; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : set U; fe(n : Nat) : add(n, zero) = n;
  def derived_proof(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { ${explicit?"simp [fe];":"simp;"} };
}
def extra(n : Nat) : add(n, zero) = n := nat_add_zero(n);
simp_rule extra;
theory Child(U < UU0) extends Parent {}`;
    const run=async source=>{
      const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
      return program.check(source,"main");
    };
    const result=await run(source);
    assert.deepEqual(result.gaps.map(g=>g.name),explicit?[]:["Parent.derived_proof"]);
    assert.ok(result.outputs.find(d=>d.name==="Child.derived_proof").verified);
    const links=result.links.filter(link=>link.role==="simplification witness");
    assert.equal(links.length,explicit?1:0);
    const edits=result.links.filter(link=>link.freeze).map(link=>link.freeze);
    assert.equal(edits.length,explicit?1:0);
    for(const edit of edits) {
      assert.equal(edit.text,"simp only [fe];");
      const checked=await run(source.slice(0,edit.start)+edit.text+source.slice(edit.end));
      assert.deepEqual(checked.gaps,[]);
    }
  }
});
