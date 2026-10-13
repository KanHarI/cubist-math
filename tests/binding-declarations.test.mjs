import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {ScopePoints} from "../web/translator/scope-points.mjs";
import {recursionSite} from "../web/translator/match.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {BindingAdapter,LexicalContext,bindingResolution,reservedResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,lowerBindingSyntax,cloneBindingSyntax} from "../web/cubist/binding-syntax.mjs";

const module=await create();
const base="inductive Two { left_; right_; } inductive Nat { zero; succ(n : Nat); }";

// Exercise complete ordinary declarations through the real translator's
// admission path. This pilot prepares the explicitly migrated family only;
// the production module resolver moves with the retained families in CB2/3.
async function prepared(t,source,{clone=false,destination=new Map()}={}) {
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check(base,"base")).gaps,[]);
  const points=[],recorder=new ScopePoints("module-pilot",{onPoint:point=>points.push(point)}),table=recorder.table;
  const reserved=reservedReferences(source),adapter=new BindingAdapter(table,{reserved});
  let context=new LexicalContext(reserved.map(label=>[label,reservedResolution(label)]));
  const env=new Map(destination),constructors=[];
  for(const [label,value] of program.modules.get("base")) {
    if(!/^[A-Za-z_][A-Za-z0-9_]*$/.test(label))continue;
    const start=base.indexOf(label),record=table.allocate(["import"],{role:"declaration",label,
      origin:sourceOrigin({revision:"base-1",module:"base",start,end:start+label.length})});
    context=context.bind(label,bindingResolution(record.id));
    env.set(adapter.key(record.id),value);
    if(value.tag==="InductiveConstructor")constructors.push({id:record.id,label,nullary:!value.arity&&!value.dims});
  }
  const ast=parse(source),artifacts=[];
  assert.ok(ast.declarations.every(d=>d.kind==="def"));
  const declarations=ast.declarations.map((declaration,index)=>{
    const owner=["module","pilot","declaration",String(index)],label=declaration.name.text;
    const record=table.allocate([...owner,"header"],{role:"declaration",label,
      origin:sourceOrigin({revision:"pilot-1",module:"pilot",start:declaration.name.start,end:declaration.name.end})});
    const own=declaration.params.length?declaration.params:declaration.valueParameters??[];
    const at=recursionSite(declaration,own)?context.bind(label,bindingResolution(record.id)):context;
    let syntax=resolveBindingSyntax(declaration,{table,owner,context:at,constructors,source:{revision:"pilot-1",module:"pilot"}});
    if(clone)syntax=cloneBindingSyntax(syntax,table,[...owner,"clone"]).syntax;
    artifacts.push(syntax);
    context=context.bind(label,bindingResolution(record.id));
    const lowered=lowerBindingSyntax(syntax,adapter);
    return {...lowered,name:{...lowered.name,bindingId:record.id}};
  });
  const checker=Object.create(program.checker);
  checker.bindingName=label=>`pilot__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"pilot",scopePoints:recorder,
    onDeclarationStart:d=>recorder.declaration("pilot",d,checker.bindingName(d.name.text))});
  const result=translator.translateSyntax({...ast,items:declarations,declarations},source,env,{bindingAdapter:adapter});
  return {program,translator,result,points,table,artifacts,adapter};
}

test("complete ordinary modules preserve dependent telescopes, named labels, recursion and dimensions",async t=>{
  const source=`
def first{{U < UU0, A : U}}(x, y : A) : A := x;
def inferred{{U < UU0, A : U}}(x, y : A) := y;
def dependent{{U < UU0, A : U}}(x, y : A, p : x = y) : A := x;
def named : Two := first{{A := Two, U := U0}}(y := left_, x := right_);
def inferred_named : Two := inferred(x := left_, y := right_);
def dependent_named : Two := dependent(y := right_, p := refl(right_), x := right_);
def shadow(x : Two) : Two := (fun (x : Two) => x)(right_);
def line(p : tt = tt) : tt = tt := path i => p @ i;
def copy(n : Nat) : Nat := match n { zero => zero; succ(k) => succ(copy(k)); };
def computation : Nat := copy(succ(zero));
def count(n, m : Nat) : Nat := match n { zero => m; succ(k) => count(k, succ(m)); };
def varied : Nat := count(succ(zero), zero);
def keep{{U < UU0, A : U}}(n : Nat, x : A) : A := match n { zero => x; succ(k) => keep(k, x); };
def implicit_recursive : Two := keep(succ(zero), right_);
`;
  for(const clone of [false,true]) {
    const {program,translator,result,points,table,artifacts}=await prepared(t,source,{clone});
    assert.deepEqual(result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]),[]);
    const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
    const expected=source=>translator.term(parse(source,true),scope);
    for(const label of ["named","inferred_named","dependent_named","implicit_recursive"]) {
      assert.equal(scope.equal(result.env.get(label),expected("right_")),true,label);
      assert.equal(scope.equal(result.env.get(label),expected("left_")),false,label);
    }
    assert.equal(scope.equal(result.env.get("computation"),expected("succ(zero)")),true);
    assert.equal(scope.equal(result.env.get("computation"),expected("zero")),false);
    assert.equal(scope.equal(result.env.get("varied"),expected("succ(zero)")),true);
    const chosen=points.find(point=>point.origin.start===source.indexOf("first{{A"));
    assert.ok(chosen?.available,chosen?.reason);
    const id=chosen.lexical.find(([label])=>label==="first")[1].id;
    assert.equal(id,result.declarations[0].syntax.name.bindingId,"source and scope registry share the declaration identity");
    const parameters=artifacts[0].owned.map(id=>table.get(id));
    assert.deepEqual(parameters.map(p=>[p.label,p.role]),[["U","universe"],["A","parameter"],["x","parameter"],["y","parameter"]]);
    assert.ok(points.some(point=>point.available&&point.lexical.some(([label,id])=>label==="i"&&table.get(id.id).role==="dimension")));
    assert.deepEqual(JSON.parse(JSON.stringify(artifacts)),artifacts);
  }
});

test("prepared declaration failures never resolve through destination labels or publish usable IDs",async t=>{
  const source=`def absent : Unit := late; def client : Unit := absent; def late : Unit := tt; def independent : Unit := late;`;
  const {result,program,adapter}=await prepared(t,source,{destination:new Map([["late",{tag:"Point"}]])});
  assert.deepEqual(result.declarations.map(d=>[d.name,d.status==="checked-native-cubical"]),
    [["absent",false],["client",false],["late",true],["independent",true]]);
  assert.match(result.declarations[0].reason,/Untranslated name: late/);
  for(const declaration of result.declarations.slice(0,2)) {
    assert.equal(result.env.get(adapter.key(declaration.syntax.name.bindingId)).tag,"Untranslated");
    assert.equal(program.kernel.definitions.has(`pilot__${declaration.name}`),false);
  }
});

test("fresh identities do not conceal repeated public parameter labels",async t=>{
  const {result}=await prepared(t,"def duplicate(x, x : Unit) : Unit := x; def independent : Unit := tt;");
  assert.match(result.declarations[0].reason,/two parameters named x/);
  assert.equal(result.declarations[1].status,"checked-native-cubical");
});

test("identity-bearing recursive calls retain the structural restriction",async t=>{
  const {result}=await prepared(t,"def bad(n : Nat) : Nat := match n { zero => zero; succ(k) => bad(n); };");
  assert.match(result.declarations[0].reason,/only structural recursion/);
});
