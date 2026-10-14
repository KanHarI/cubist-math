import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {BindingTable,BindingAdapter,LexicalContext,SlotOutcomes,sourceOrigin,bindingResolution,
  projectedResolution,UnknownNamespaceMember} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,cloneBindingSyntax,bindingUses,substituteBindingSyntax,lowerBindingSyntax,sameBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

test("pending openings retain whole qualified fallbacks and resolve independently in each branch",()=>{
  const table=new BindingTable("openings"),origin=sourceOrigin({revision:"source",module:"main",start:0,end:1});
  const make=(label,role="declaration")=>table.allocate(["owner"],{role,label,origin});
  const p=make("p"),px=make("p.x"),field=make("T.p"),activation=make("selection","activation");
  const before=new LexicalContext([["p",bindingResolution(p.id)],["p.x",bindingResolution(px.id)]]);
  const opened=before.open(activation.id),use=opened.qualified("p.x").value;
  assert.equal(use.enclosing.id,px.id,"retain the qualified declaration, not the unrelated receiver p");
  const adapter=new BindingAdapter(table),pending=new SlotOutcomes();
  assert.equal(adapter.lower(use,pending),null);
  const absent=pending.activate(activation.id,[]),present=pending.activate(activation.id,
    [["p",projectedResolution(field.id,activation.id)]]);
  assert.equal(adapter.lower(use,absent),adapter.key(px.id));
  assert.deepEqual(present.resolve(use),{tag:"member",receiver:projectedResolution(field.id,activation.id),fields:["x"]});
  assert.equal(pending.activation(activation.id),null);
  assert.deepEqual(new SlotOutcomes(JSON.parse(JSON.stringify(present.snapshot()))).resolve(use),present.resolve(use));
  assert.deepEqual(new LexicalContext(JSON.parse(JSON.stringify(opened.snapshot()))).qualified("p.x"),opened.qualified("p.x"));
  assert.equal(opened.bind("p",bindingResolution(p.id)).qualified("p.x").value.id,p.id,"a later local shadows the opening");
  const closed=before.namespace("p",[["x",bindingResolution(px.id)]],"Parent").open(activation.id);
  const missing=closed.qualified("p.missing").value;
  assert.equal(missing.tag,"opening","a pending opening may supply p before the saved namespace refusal");
  assert.throws(()=>adapter.lower(missing,absent),UnknownNamespaceMember);
  assert.equal(present.resolve(missing).tag,"member");
});

const wasm=await create();
async function setup(t) {
  const library=sourceReader();
  const program=new CubicalProgram(wasm,(name,importer)=>name==="two"?`import hlevels; inductive Two : set U0 { left_; right_; }`
    :name==="p"?`import two; theory p(U < UU0) { M : set U; x : M; missing : M; }
      def other : p(U0) := p.make(Two, _, right_, right_);`:library(name,importer));t.after(()=>program.dispose());
  assert.deepEqual((await program.check(`import hlevels; import p;
    theory Leaf(U < UU0) { M : set U; x : M; }
    def chosen : Leaf(U0) := Leaf.make(Two, _, left_);
    theory Box(U < UU0) { M : set U; p : Leaf(U); }
    def box : Box(U0) := Box.make(Two, _, chosen);
    def receiver(a : Unit) : Leaf(U0) := chosen;
    def outside : Two := right_;
  `,"base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base"),values=new Map(),lexical=[];
  for(const [label,value] of env)if(!label.startsWith("\u0000")) {
    const binding=registry.ofValue(value);
    if(binding){values.set(binding.id,value);lexical.push([label,bindingResolution(binding.id)]);}
  }
  const inputs=bindingInputs(table,values,{lexical,reserved:reservedReferences("U0 UU0 Unit tt refl")});
  const source={revision:"retained-opening",module:"source"};let serial=0;
  const retain=text=>{
    const d=parse(text).declarations[0],owner=["retained",String(serial++)];
    const binding=table.allocate(owner,{role:"declaration",label:d.name.text,
      origin:sourceOrigin({...source,start:d.name.start,end:d.name.end})});
    const syntax=resolveBindingSyntax(d,{table,source,owner,context:inputs.context,constructors:inputs.constructors});
    return {binding,syntax};
  };
  const check=(declarations,before="")=>{
    const checker=Object.create(program.checker);checker.bindingName=label=>`pilot__${label}`;
    checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
    const translator=new Translator({checker,normalize:false,moduleName:"pilot",compilationBindings:registry});
    const term=translator.term.bind(translator);let receivers=0;
    translator.term=(node,...args)=>{if(node.kind==="call"&&node.fn.spelling==="receiver")receivers++;return term(node,...args);};
    const result=translator.translateSyntax({declarations:[...parse(before).declarations,
      ...declarations.map(({binding,syntax})=>bindingDeclaration(binding,syntax))]},"",env);
    const scope=new Scope(translator.unit(),new Map(),result.env);
    return {result,receivers,equal:(name,expected)=>scope.equal(result.env.get(name),term(parse(expected,true),scope))};
  };
  return {table,retain,check,inputs};
}
const failures=result=>result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]);

test("retained model openings keep source receivers, local shadowing and qualified targets through the kernel",async t=>{
  const {retain,check}=await setup(t);
  const declarations=[
    "def opened(x : Two) : Two := chosen.(x);",
    "def local : Two := chosen.((fun (x : Two) => x)(right_));",
    "def fallback : Two := chosen.(outside);",
    "def absentQualified : Two := chosen.(p.x(other));",
    "def hiddenQualified : Two := box.(p.x);",
    "def chained : Two := box.(p.(x));",
    "def called : Two { use receiver(tt); exact x; }",
    "def beforeAfter(x : Two) : Two { let saved := x; use chosen; let x := saved; exact x; }",
    "def blockChained : Two { use box; use p; exact x; }",
    "def missing : Two := chosen.(destination_only);",
    "def missingMember : Two := box.(p.missing(other));",
    "def failed : Two := tt.(outside);",
  ].map(retain);
  assert.doesNotThrow(()=>snapshotSyntax(declarations));
  const original=JSON.stringify(declarations);
  const {result,equal,receivers}=check(declarations,`
    def chosen : Unit := tt;
    def outside : Two := left_;
    def p : Unit := tt;
    def destination_only : Two := left_;
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["missing","missingMember","failed"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/Untranslated name: destination_only/);
  assert.match(failures(result)[1][1],/has no field missing/);
  assert.equal(equal("opened","fun (x : Two) => left_"),true);
  assert.equal(equal("opened","fun (x : Two) => x"),false);
  assert.equal(equal("beforeAfter","fun (x : Two) => x"),true);
  assert.equal(equal("beforeAfter","fun (x : Two) => left_"),false);
  for(const name of ["local","fallback","absentQualified"]) {
    assert.equal(equal(name,"right_"),true,name);assert.equal(equal(name,"left_"),false,name);
  }
  for(const name of ["hiddenQualified","chained","called","blockChained"]) {
    assert.equal(equal(name,"left_"),true,name);assert.equal(equal(name,"right_"),false,name);
  }
  assert.equal(receivers,1,"the source call is elaborated once for the activation");
  assert.equal(JSON.stringify(declarations),original);
});

test("activation ownership and saved alternatives survive cloning and conditional substitution",async t=>{
  const {retain,table,inputs,check}=await setup(t);
  const original=retain("def source_ : Two := chosen.(outside);");
  const copied=cloneBindingSyntax(original.syntax,table,["copy"]);
  assert.equal(sameBindingSyntax(original.syntax,copied.syntax),true);
  assert.ok(copied.syntax.owned.every(id=>!original.syntax.owned.includes(id)));
  const uses=bindingUses(original.syntax,{conditional:true});
  assert.ok(uses.some(use=>use.kind==="deferred-activation"));
  assert.ok(uses.some(use=>use.kind==="deferred-opening"));
  const outside=inputs.context.lookup("outside").id;
  assert.ok(uses.some(use=>use.id===outside&&use.conditions?.[0].outcome==="absent"));
  const replacement=resolveBindingSyntax(parse("left_",true),{table,owner:["argument"],context:inputs.context,
    source:{revision:"caller",module:"caller"}});
  const syntax=substituteBindingSyntax(copied.syntax,new Map([[outside,replacement]]),table,["substitution"]);
  const {result,equal}=check([{binding:original.binding,syntax}]);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("source_","left_"),true);assert.equal(equal("source_","right_"),false);
  assert.doesNotThrow(()=>lowerBindingSyntax(syntax,inputs.adapter));
  assert.doesNotThrow(()=>snapshotSyntax(syntax));
});
