import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {bindingResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,bindingSyntaxView,cloneBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {bindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";

const wasm=await create();
async function setup(t) {
  const program=new CubicalProgram(wasm,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check("inductive Two { left_; right_; }","base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base"),values=new Map();
  for(const [label,value] of env)if(/^[A-Za-z_][A-Za-z0-9_]*$/.test(label)) {
    const binding=registry.ofValue(value);if(binding)values.set(binding.id,value);
  }
  const inputs=bindingInputs(table,values,{reserved:reservedReferences("U0 UU0")});
  let serial=0;
  // Build an artifact from separately resolved source interfaces. This is
  // not an opt-in source inductive resolver: generated initial/free builders
  // will supply the same complete ID-bearing header/constructor structure.
  const prepare=text=>{
    const source={revision:"source",module:"source"},d=parse(text).declarations[0],owner=["artifact",String(serial++)];
    const allocate=token=>table.allocate([...owner,"declarations"],{role:"declaration",label:token.text,
      origin:sourceOrigin({...source,start:token.start,end:token.end})});
    const binding=allocate(d.name),constructors=d.constructors.map(c=>allocate(c.name));
    const options={table,source,owner:[...owner,"header"],context:inputs.context,constructors:inputs.constructors};
    const header=resolveBindingSyntax({kind:"def",name:d.name,params:d.params,type:null,value:null},options);
    let context=inputs.context;
    for(const p of header.tree.params)context=context.bind(p.name.text,bindingResolution(p.name.bindingId));
    const result=d.result?{...d.result,...(d.result.universe?{universe:resolveBindingSyntax(d.result.universe,
      {...options,owner:[...owner,"result"],context}).tree}:{})}:null;
    context=context.bind(d.name.text,bindingResolution(binding.id));
    const members=d.constructors.map((c,k)=>{
      const syntax=resolveBindingSyntax({kind:"def",name:c.name,params:c.params,type:c.type,value:null},
        {...options,owner:[...owner,"constructor",String(k)],context});
      context=context.bind(c.name.text,bindingResolution(constructors[k].id));
      return {...c,params:syntax.tree.params,type:syntax.tree.type,name:{...c.name,bindingId:constructors[k].id}};
    });
    const syntax=cloneBindingSyntax(bindingSyntaxView(header,{...d,name:{...d.name,bindingId:binding.id},
      params:header.tree.params,result,constructors:members}),table,[...owner,"clone"]).syntax;
    const declaration=bindingDeclaration(binding,syntax,{generated:{initial:d.name.text}});
    assert.doesNotThrow(()=>snapshotSyntax(declaration));
    return {binding,constructors,syntax,declaration};
  };
  const check=(artifacts,source,{before=""}={})=>{
    const checker=program.checker,definitionModule="pilot";
    const translator=new Translator({checker,definitionModule,normalize:false,moduleName:"pilot",compilationBindings:registry});
    const result=translator.translateSyntax({declarations:[...parse(before).declarations,...artifacts.map(a=>a.declaration),...parse(source).declarations]},source,env);
    return {result,translator};
  };
  return {program,inputs,prepare,check};
}
const failures=result=>result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]);

test("retained inductives elaborate exact self, earlier constructors and complete grouped interfaces",async t=>{
  const {program,prepare,check}=await setup(t);
  const artifact=prepare(`inductive Bag(A : U0) : set U0 {
    cell(Two, x : Two, p : Two = x, a : A);
    chain(rest : Bag(A));
    loop(a : A) : cell(left_, left_, refl(left_), a) = cell(left_, left_, refl(left_), a);
  }`);
  const {result,translator}=check([artifact],`
    def made : Bag(Unit) := cell(left_, left_, refl(left_), tt);
    def chained : Bag(Unit) := chain(made);
    def wrong : Bag(Unit) := cell(tt, tt, refl(tt), tt);
  `,{before:"def Two : U0 := Unit;"});
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  const value=result.env.get("Bag");
  assert.deepEqual(value.slots.map(slot=>slot.source),["A"]);
  assert.deepEqual(value.constructors[0].fields,["Two","x","p","a"]);
  assert.doesNotMatch(JSON.stringify(result.declarations[1].inductive),/\\u0000id/);
  assert.doesNotMatch(program.checker.displayText(result.declarations.find(d=>d.name==="made").term,[],{width:1000}),/id \[/);
  const scope=new Scope(translator.unit(),new Map(),result.env);
  assert.equal(scope.equal(result.env.get("chained"),translator.term(parse("chain(made)",true),scope)),true);
  assert.equal(scope.equal(result.env.get("chained"),result.env.get("made")),false);
});

test("retained inductive universe parameters and failed constructor aliases keep their public interfaces",async t=>{
  const {program,inputs,prepare,check}=await setup(t);
  const valid=prepare("inductive Box(U < UU0, A : U) : U { box_(x : A); }");
  const bad=prepare("inductive Broken : set U0 { first_; invalid_(f : Broken -> Unit); }");
  const {result}=check([valid,bad],"def value : Box(U0, Unit) := box_(tt);");
  assert.deepEqual(failures(result).map(([name])=>name),["Broken"],JSON.stringify(failures(result)));
  assert.deepEqual(result.env.get("Box").slots.map(slot=>slot.source),["U","A"]);
  for(const binding of [bad.binding,...bad.constructors]) {
    const actual=result.env.get(inputs.adapter.key(binding.id));
    assert.equal(actual,result.env.get(binding.label));
    assert.equal(actual.tag,"Untranslated");assert.equal(actual.blockedBy,"pilot__Broken");
  }
  assert.equal(program.kernel.signatures.has("pilot__Broken"),false);
});

test("retained inductive errors name public repeated parameters",async t=>{
  const {prepare,check}=await setup(t);
  for(const text of ["inductive Broken(A, A : U0) { point_; }","inductive Broken { point_(x, x : Unit); }"]) {
    const {result}=check([prepare(text)],"");
    assert.equal(failures(result).length,1);
    assert.match(failures(result)[0][1],/two (?:parameters named A|arguments named x)/);
    assert.doesNotMatch(failures(result)[0][1],/id \[/);
  }
});
