import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {mkdtemp, writeFile, rm} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join} from "node:path";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import create from "../web/dist/cubical.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {checkProgram} from "./check-program.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {gaps} from "./fixtures/frontend-generation.mjs";

const module=await create();
const check=(t,source,fixtures={})=>{
  const library=sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
};
const clean=checked=>assert.deepEqual(checked.result.gaps,[]);

test("FG5: freshened law and derived parameters preserve every written link and hover",async t=>{
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
          ?Object.values(checked.program.localSymbols).filter(info=>info.binding===`fixture__local_${at}`)
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

test("FG5: safe lint preserves named constructors, Hom/Iso and initial/free clients",async t=>{
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

test("FG5: the original arrow rewrite loses generated capability despite equal function types",async t=>{
  const checked=await check(t,gaps.G5.source);clean(checked);
  const rewritten=await check(t,gaps.G5.source.replace("forall x, y : M. M","M -> M -> M"));
  assert.ok(rewritten.result.gaps.some(g=>g.name==="identity"));
  assert.ok(rewritten.result.gaps.some(g=>g.name==="N"));
  assert.deepEqual(lint(gaps.G5.source),[]);
});

test("FG5: CLI keeps public labels and the focused refusal category",async t=>{
  const directory=await mkdtemp(join(tmpdir(),"cubist-provenance-"));
  t.after(()=>rm(directory,{recursive:true,force:true}));
  const cli=fileURLToPath(new URL("../cli/repl.mjs",import.meta.url));
  const file=join(directory,"capture.cubist");
  await writeFile(file,gaps.G10.source);
  const refused=spawnSync(process.execPath,[cli,"check",file],{encoding:"utf8",timeout:30000});
  assert.equal(refused.status,1,refused.stderr);
  assert.match(refused.stderr,/E871/);assert.match(refused.stderr,/field c: rename the enclosing pattern/);
  assert.doesNotMatch(refused.stderr,/\bc1\b|\u0000|__theory/);
  await writeFile(file,gaps.G9.source);
  const inspected=spawnSync(process.execPath,[cli],{encoding:"utf8",timeout:30000,
    input:`check ${file}\ninspect T.l\nquit\n`});
  assert.equal(inspected.status,0,inspected.stderr);assert.equal(inspected.stderr,"");
  assert.doesNotMatch(inspected.stdout,/\bc1\b|\u0000|__theory/);
  assert.match(inspected.stdout,/Assumptions: none/);
});
