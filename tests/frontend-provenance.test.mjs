import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {checkProgram} from "./check-program.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {gaps} from "./frontend-generation-cases.mjs";

const module=await create();
const check=(t,source,fixtures={})=>{
  const library=sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
};
const clean=checked=>assert.deepEqual(checked.result.gaps,[]);

test("CB5: freshened law and derived parameters preserve every written link and hover",async t=>{
  const source=gaps.G9.source.replace("  law l", "  def derived(c : M) : M := k(c);\n  law l");
  for(const imported of [false,true]) {
    const checked=await check(t,imported?`import fixture;
theory Child(U < UU0) extends T {}
def inherited(S : Child(U0), x : S.M) : S.op(x,S.c) = S.op(x,x) := S.l(x);`:source,{fixture:source});
    clean(checked);
    for(const fragment of ["law l(c : M) : k(c) = op(c, c);","def derived(c : M) : M := k(c);"]) {
      const start=source.indexOf(fragment), binder=start+fragment.indexOf("c : M");
      for(const occurrence of fragment.matchAll(/\bc\b/g)) {
        const at=start+occurrence.index;
        const observations=imported
          ?[...checked.program.declarationReferences].filter(([name])=>name.startsWith("fixture__"))
            .flatMap(([,references])=>references.filter(reference=>reference.start===at)
              .map(reference=>checked.program.localSymbols[reference.binding]).filter(Boolean))
          :checked.result.links.filter(link=>link.start===at&&link.end===at+1);
        assert.ok(observations.length,`missing source observation at ${at}`);
        for(const link of observations) {
          assert.equal(link.name,"c");assert.equal(link.definitionStart,binder);
          const view=checked.program.inspect(link.binding);
          assert.equal(view.expressionText,"c");
          assert.doesNotMatch(view.typeText,/\bc1\b|\u0000|__theory/);
          assert.ok(view.context.some(entry=>entry.label==="c"));
          assert.ok(view.context.every(entry=>entry.label!=="c1"));
          assert.deepEqual(view.axioms,[]);
        }
      }
    }
  }
});

test("CB5: safe lint preserves named constructors, Hom/Iso and initial/free clients",async t=>{
  for(const quantifier of ["forall x : M. M","forall x, y : M. M"]) {
    const args=quantifier.includes(",")?"x, x":"x", names=quantifier.includes(",")?"x, y":"x";
    const source=`import hlevels;
theory T(U < UU0) { M : set U; op : ${quantifier}; law same : forall a : M. a = a; }
def identity(S : T(U0)) := T.Hom.id(S);
def iso(S : T(U0)) := T.Iso.id(S);
initial N : T(U0);
free W(A : U0) : T(U0) on A;
def generated(x : N) : N := N.op(${args});
def generator : W(Unit) := W.gen(tt);
def named(S : T(U0), a : S.M) : S.M := T.Hom.make(S,S,
  map := fun (x : S.M) => x, map_op := fun (${names} : S.M) => refl(S.op(${names}))).map(a);
def fold_computes(S : T(U0), a : S.M) : W.fold(S.M, S, fun (x : S.M) => x).map(W.gen(a)) = a { rfl; }
def ordinary : U0 := forall unused : Unit. Unit;`;
    const checked=await check(t,source);clean(checked);
    const advice=lint(source).filter(w=>["W705","W706"].includes(w.code));
    assert.equal(advice.length,1);assert.equal(advice[0].declaration,"ordinary");
    const rewritten=await check(t,source.replace("forall unused : Unit. Unit","Unit -> Unit"));clean(rewritten);
    for(const name of ["identity","iso","N.fold","generated","named","fold_computes"]) {
      assert.equal(checked.get(name).verified,true);assert.deepEqual(checked.get(name).axioms,[]);
      assert.equal(rewritten.get(name).type,checked.get(name).type);
    }
    assert.deepEqual(rewritten.result.outputs.map(o=>o.name),checked.result.outputs.map(o=>o.name));
  }
});

test("CB5: the original arrow rewrite loses generated capability despite equal function types",async t=>{
  const checked=await check(t,gaps.G5.source);clean(checked);
  const rewritten=await check(t,gaps.G5.source.replace("forall x, y : M. M","M -> M -> M"));
  assert.ok(rewritten.result.gaps.some(g=>g.name==="identity"));
  assert.ok(rewritten.result.gaps.some(g=>g.name==="N"));
  assert.deepEqual(lint(gaps.G5.source),[]);
});


test("CB5: inherited binding failures retain caller and authored source locations",async t=>{
  const fixture=`import hlevels; import unat;
notation consume { x + y := x; }
theory Parent(U < UU0) { M : set U; c : M; }
theory Child(U < UU0) extends p : Parent {
  def rejected : UNat := consume.(p.absent + zero);
}`;
  for(const imported of [false,true]) {
    const prefix=imported?"import fixture;\n":fixture+"\n";
    const source=prefix+"theory Grand(U < UU0) extends Child {}\ndef tail : Unit := tt;";
    const checked=await check(t,source,{fixture});
    const gap=checked.result.gaps.find(g=>g.name==="Grand.rejected");
    assert.equal(gap.code,"E829");assert.equal(source.slice(gap.start,gap.end),"Child");
    assert.equal(gap.diagnostic.kind,"binding");
    assert.equal(gap.diagnostic.parameters.member,"absent");
    assert.deepEqual(gap.diagnostic.primary,{module:"main",start:gap.start,end:gap.end});
    const authored=gap.diagnostic.related.find(site=>site.start===fixture.indexOf("p.absent"));
    assert.equal(authored.module,imported?"fixture":"main");
    assert.equal(fixture.slice(authored.start,authored.end),"p.absent");
    assert.equal(checked.get("tail").verified,true);
  }
});

test("CB5: inherited proof failures use caller spans and keep the exact written statement",async t=>{
  for(const statement of ["rfl;","exact refl(succ(zero));","simp only [unat_add_zero];","rw [unat_add_zero];"]) {
    const fixture=`import unat; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : set U;
  def bad(n : UNat, x : Edge) : UNat := match x { lo => add(n, zero); hi => succ(n); }
    obligations by { ${statement} };
}`;
    for(const padding of ["","// "+"x".repeat(fixture.length)+"\n"]) {
      const source="import fixture;\n"+padding+"theory Child(U < UU0) extends Parent {}";
      const checked=await check(t,source,{fixture});
      const gap=checked.result.gaps.find(g=>g.name==="Child.bad");
      assert.ok(gap);assert.equal(source.slice(gap.start,gap.end),"Parent");
      assert.equal(gap.diagnostic.primary.module,"main");
      const written=statement.startsWith("rw ")?"unat_add_zero":statement;
      const related=gap.diagnostic.related.find(site=>site.module==="fixture"&&fixture.slice(site.start,site.end)===written);
      assert.ok(related,JSON.stringify(gap));
    }
  }
});

test("CB5: rewrite descriptions and residual errors name the written substituted rule",async t=>{
  for(const fails of [false,true]) {
    const source=`import unat; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0, n : UNat) { M : set U; fe : add(n, zero) = n;
  def d(x : Edge) : UNat := match x { lo => add(n, zero); hi => ${fails?"succ(n)":"n"}; }
    obligations by { rw [fe]; };
}`;
    const checked=await check(t,source);
    if(fails) {
      const gap=checked.result.gaps.find(g=>g.name==="Parent.d");
      assert.equal(gap.code,"E452");assert.match(gap.reason,/fe/);
      assert.doesNotMatch(gap.reason,/using Parent|rule Parent/);
    } else {
      clean(checked);
      const links=checked.result.links.filter(link=>link.role==="rewrite witness");
      assert.equal(links.length,1);assert.equal(links[0].description,"Checked rewrite using fe.");
    }
  }
});

test("CB5: copied observations keep distinct checked views and cannot annotate the parent's source",async t=>{
  const source=gaps.G9.source+"\ntheory Child(U < UU0) extends T(M := N) {}";
  const checked=await check(t,source);clean(checked);
  const at=source.indexOf("law l(c")+"law l(".length;
  const observed=name=>(checked.program.declarationReferences.get(`main__${name}.l`)??[])
    .filter(reference=>reference.start===at&&checked.program.views.has(reference.binding));
  const parent=observed("T"),child=observed("Child");
  assert.ok(parent.length);assert.ok(child.length);
  assert.ok(child.every(copy=>parent.every(original=>original.binding!==copy.binding)));
  for(const reference of parent)assert.match(checked.program.inspect(reference.binding).typeText,/\.M\b/);
  for(const reference of child)assert.match(checked.program.inspect(reference.binding).typeText,/\.N\b/);
  assert.ok(checked.result.links.some(link=>parent.some(reference=>reference.binding===link.binding)));
  assert.ok(checked.result.links.every(link=>child.every(reference=>reference.binding!==link.binding)));
  const xUses=checked.result.links.filter(link=>link.name==="x"&&link.start>source.indexOf("def meaning"));
  assert.ok(xUses.length>=2);
  for(const link of xUses) {
    const view=checked.program.inspect(link.binding);
    assert.ok(checked.program.views.has(view.sourceBinding));
    assert.equal(checked.program.inspect(view.sourceBinding).expressionText,"x");
  }
});

test("CB5: imported generated observations keep their source module without foreign links",async t=>{
  const fixture=`import unat; import hlevels;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : set U;
  def d(n : UNat, x : Edge) : UNat := match x { lo => add(n, zero); hi => n; }
    obligations by { simp only [unat_add_zero]; };
}`;
  const source="import fixture; theory Child(U < UU0) extends Parent {}";
  const checked=await check(t,source,{fixture});clean(checked);
  assert.ok(checked.result.links.every(link=>0<=link.start&&link.end<=source.length),JSON.stringify(checked.result.links));
  const binder=fixture.indexOf("d(n")+2;
  const references=checked.program.declarationReferences.get("main__Child.d").filter(ref=>ref.start===binder);
  assert.ok(references.length);
  for(const reference of references) {
    const info=checked.program.localSymbols[reference.binding];
    assert.equal(info.sourceModule,"fixture");assert.equal(info.sourceName,"Parent");
    assert.equal(info.definitionStart,binder);assert.equal(info.origin.module,"fixture");
    assert.ok(checked.program.inspect(reference.binding));
  }
});


test("CB5: closing inferred checks have qualified sites and helper checks retain their value origin",async t=>{
  for(const field of ["law bad : c = tt;","d : c;"]) {
    const fixture=`import hlevels; theory Parent(U < UU0) { M : set U; c : M; ${field} }`;
    for(const imported of [false,true]) {
      const checked=await check(t,imported?"import fixture; def tail : Unit := tt;":fixture,{fixture});
      const gap=checked.result.gaps.find(gap=>gap.name==="Parent");
      assert.ok(gap?.diagnostic);assert.equal(gap.diagnostic.primary.module,imported?"fixture":"main");
      assert.equal(fixture.slice(gap.diagnostic.primary.start,gap.diagnostic.primary.end),"Parent");
    }
  }
  const fixture=`import hlevels; theory Parent(U < UU0) { M : set U; c : M; def bad : M := tt; }`;
  for(const imported of [false,true]) {
    const checked=await check(t,imported?"import fixture; theory Child(U < UU0) extends Parent {}":fixture,{fixture});
    const gap=checked.result.gaps.find(gap=>gap.name===(imported?"Child.bad":"Parent.bad"));
    const sites=[gap.diagnostic.primary,...gap.diagnostic.related];
    assert.ok(sites.some(site=>site.module===(imported?"fixture":"main")&&fixture.slice(site.start,site.end)==="tt"));
    if(imported)assert.equal(gap.diagnostic.primary.module,"main");
    else assert.equal(fixture.slice(gap.start,gap.end),"tt");
  }
});
