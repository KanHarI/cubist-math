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
import {activateSourceItem,withSourceCaptures} from "../web/translator/retained-source-context.mjs";
import {retainTheorySource} from "../web/cubist/retained-theories.mjs";
import {retainedTheoryArtifacts} from "../web/cubist/retained-theory-artifacts.mjs";

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
  const slot=make("p","pattern"),pattern=before.defer("p",slot.id).qualified("p.x");
  assert.equal(new SlotOutcomes().decide(slot.id,"constructor").resolve(pattern.value).id,px.id,
    "a constructor decision restores the whole qualified declaration");
  assert.deepEqual(new SlotOutcomes().decide(slot.id,"variable").resolve(pattern.value),
    {tag:"member",receiver:bindingResolution(slot.id),fields:["x"]});
  const unknown=before.namespace("p",[["x",bindingResolution(px.id)]],"Parent").defer("p",slot.id).qualified("p.unknown").value;
  assert.equal(new SlotOutcomes().decide(slot.id,"variable").resolve(unknown).tag,"member");
  assert.throws(()=>adapter.lower(unknown,new SlotOutcomes().decide(slot.id,"constructor")),UnknownNamespaceMember);
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
  return {table,retain,check,inputs,program,env,source};
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

test("file-level activations retain closed source receivers through theory generation and inheritance",async t=>{
  const {table,inputs,program,env,source}=await setup(t);
  const registry=program.compilationBindings,checker=Object.create(program.checker);
  checker.bindingName=label=>`files__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"files",compilationBindings:registry});
  const term=translator.term.bind(translator);let receivers=0;
  translator.term=(node,...args)=>{if(node.kind==="call"&&node.fn.spelling==="receiver")receivers++;return term(node,...args);};
  const text=`use receiver(tt);
    theory T(U < UU0) { M : set U; c : M; def picked : Two := x; def local(x : Two) : Two := x; }`;
  const item=parse(text).declarations[0],unit=translator.unit({source:text});
  const prepared=activateSourceItem(translator,new Scope(unit,new Map(),env),item,inputs,{owner:["file","T"],source});
  assert.equal(receivers,1);
  const record=retainTheorySource(prepared.item,{table,source,owner:["file","T"],context:prepared.context,
    constructors:prepared.constructors});
  const parent=retainedTheoryArtifacts(record,{table,owner:["file","generated","T"]});
  const childRecord=retainTheorySource(parse("theory C(U < UU0) extends p : T {}").declarations[0],
    {table,source,owner:["file","C"],context:inputs.context,constructors:inputs.constructors},
    {lookup:name=>name==="T"?parent.record:null});
  const child=retainedTheoryArtifacts(childRecord,{table,owner:["file","generated","C"]});
  const declarations=[...parent.artifacts,...child.artifacts].map(({binding,syntax,...annotations})=>bindingDeclaration(binding,syntax,annotations));
  assert.doesNotThrow(()=>snapshotSyntax({captures:prepared.captures,activations:prepared.activations,record:child.record}));
  const held=JSON.stringify({captures:prepared.captures,activations:prepared.activations});
  const result=translator.translateSyntax({declarations:[...parse(`def receiver(a : Unit) : Unit := tt;
    def x : Two := right_;`).declarations,...declarations,...parse(`
    def instance_ : C(U0) := C.make(Two, _, left_);
    def chosen_value : Two := instance_.picked;
    def local_value : Two := instance_.local(right_);
  `).declarations]},"",withSourceCaptures(env,prepared,inputs.adapter));
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  const scope=new Scope(translator.unit(),new Map(),result.env);
  assert.equal(scope.equal(result.env.get("chosen_value"),term(parse("left_",true),scope)),true);
  assert.equal(scope.equal(result.env.get("chosen_value"),term(parse("right_",true),scope)),false);
  assert.equal(scope.equal(result.env.get("local_value"),term(parse("right_",true),scope)),true);
  assert.equal(receivers,1,"generation and inheritance never reactivate the source recipe");
  assert.equal(JSON.stringify({captures:prepared.captures,activations:prepared.activations}),held);
});

test("source activation is ordered, required per consumer and outside declaration parameters",async t=>{
  const {table,inputs,program,env,source}=await setup(t);
  const translator=new Translator({checker:program.checker,normalize:false,compilationBindings:program.compilationBindings});
  let index=0;
  const prepare=(text,changed={})=>{
    const item=parse(text).declarations[0];
    return activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),changed.env??env),item,
      {...inputs,...changed},{owner:["ordered",String(index++)],source});
  };
  const prepared=prepare("use box; use p; def value(x : Two) : Two := x;");
  assert.equal(prepared.activations.length,2);
  const final=prepared.context.lookup("x");
  assert.equal(final.tag,"projected");assert.equal(final.receiver,prepared.activations[1].capture.id);
  assert.equal(prepared.context.qualified("p.x").value.receiver,prepared.activations[0].capture.id);
  const retained=resolveBindingSyntax(prepared.item,{table,source,owner:["ordered","def"],context:prepared.context,
    constructors:prepared.constructors});
  assert.equal(retained.tree.body[0].value.resolution.id,retained.tree.params[0].name.bindingId);
  const qualified=prepare("use chosen; def value : Two := p.x(other);");
  assert.equal(qualified.context.qualified("p.x").value.id,inputs.context.qualified("p.x").value.id);
  assert.throws(()=>prepare("use tt; theory Refused(U < UU0) { k : Two; }"),/use selects a model/);
  assert.throws(()=>prepare("use chosen; use absent; theory Refused(U < UU0) { k : Two; }"),/Untranslated name: absent/);
  const shadow=table.allocate(["ordered","shadow"],{role:"declaration",label:"chosen",origin:sourceOrigin({...source,start:0,end:1})});
  const shadowed=new Map(env).set("chosen",{tag:"Point"}).set(inputs.adapter.key(shadow.id),{tag:"Point"});
  assert.throws(()=>prepare("use chosen; theory Later(U < UU0) { k : Two; }",
    {env:shadowed,context:inputs.context.bind("chosen",bindingResolution(shadow.id))}),/use selects a model/,
    "a new source item activates the recipe in its own current source context");
  const item={kind:"simp_rule",uses:[parse("missing",true)],start:0,end:7};
  const unused=activateSourceItem(translator,new Scope(translator.unit(),new Map(),env),item,inputs,
    {owner:["ordered","registration"],source});
  assert.equal(unused.context,inputs.context);assert.deepEqual(unused.captures,[]);assert.deepEqual(unused.activations,[]);
});

test("parent namespace selections preserve fields, lexical binders and model shadowing through generation",async t=>{
  const {table,inputs,program,env,source}=await setup(t);
  const records=new Map();
  const build=(text,owner)=>{
    const record=retainTheorySource(parse(text).declarations[0],{table,source,owner,context:inputs.context,
      constructors:inputs.constructors},{lookup:name=>records.get(name)});
    const built=retainedTheoryArtifacts(record,{table,owner:[...owner,"generated"]});
    records.set(record.name,built.record);return built;
  };
  const parent=build("theory Parent(U < UU0) { x : Two; y : Two; }",["namespace","parent"]);
  const child=build(`theory Child(U < UU0) extends chosen : Parent {
    def picked : Two := chosen.(x);
    def qualified : Two := chosen.x;
    def local(x : Two) : Two := chosen.(x);
    def from_model(chosen : Leaf(U0)) : chosen.M := chosen.(x);
    def nested : Two := chosen.((fun (x : Two) => x)(left_));
    def fallback : Two := chosen.(outside);
  }`,["namespace","child"]);
  const picked=child.record.derived.find(field=>field.label==="picked");
  const uses=bindingUses(picked.syntax);
  assert.ok(uses.every(use=>!["deferred-activation","deferred-opening"].includes(use.kind)));
  assert.ok(uses.some(use=>use.id===child.record.fields.find(field=>field.label==="x").id));
  assert.ok(uses.every(use=>use.id!==child.record.fields.find(field=>field.label==="y").id),"unused namespace members are not dependencies");
  const absent=build("theory Absent(U < UU0) extends absent_ : Parent { def picked : Two := absent_.(x); }",["namespace","absent"]);
  const sorts=build("theory Sorts(U < UU0) { M : set U; }",["namespace","sorts"]);
  const domains=build("theory Domains(U < UU0) extends chosen : Sorts { N : set U; f(a : chosen.(M)) : N; }",["namespace","domains"]);
  assert.equal(domains.record.fields.find(f=>f.label==="f").syntax.tree.params[0].type.resolution.id,
    domains.record.fields.find(f=>f.label==="M").id);
  const patterns=build(`theory Patterns(U < UU0) extends left_ : Parent {
    def selected_(b : Two) : Two := match b { left_ => left_.(x); right_ => left_.(y); };
    def qualified_(b : Two) : Two := match b { left_ => left_.x; right_ => left_.y; };
  }`,["namespace","patterns"]);
  const checker=Object.create(program.checker);checker.bindingName=label=>`namespace__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"namespace",compilationBindings:program.compilationBindings});
  const declarations=[parent,child,absent,sorts,domains,patterns].flatMap(built=>built.artifacts)
    .map(({binding,syntax,...annotations})=>bindingDeclaration(binding,syntax,annotations));
  const result=translator.translateSyntax({declarations:[...declarations,...parse(`
    def instance_ : Child(U0) := Child.make(right_, left_);
    def parent_value : Two := instance_.picked;
    def qualified_value : Two := instance_.qualified;
    def local_value : Two := instance_.local(left_);
    def model_value : Two := instance_.from_model(chosen);
    def nested_value : Two := instance_.nested;
    def fallback_value : Two := instance_.fallback;
    def absent_model : Absent(U0) := Absent.make(right_, left_);
    def absent_value : Two := absent_model.picked;
    def parent_domain : Domains(U0) := Domains.make(M := Unit, N := Two, f := fun (a : Unit) => left_);
    def wrong_domain : Domains(U0) := Domains.make(M := Unit, N := Two, f := fun (a : Two) => a);
    def matched : Patterns(U0) := Patterns.make(right_, left_);
    def first_selection : Two := matched.selected_(left_);
    def second_selection : Two := matched.selected_(right_);
    def first_qualified : Two := matched.qualified_(left_);
  `).declarations]},"",env);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong_domain"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/Type mismatch/);
  const scope=new Scope(translator.unit(),new Map(),result.env);
  for(const [label,value] of [["parent_value","right_"],["qualified_value","right_"],["local_value","left_"],
    ["model_value","left_"],["nested_value","left_"],["fallback_value","right_"],["absent_value","right_"],
    ["first_selection","right_"],["second_selection","left_"],["first_qualified","right_"]]) {
    assert.equal(scope.equal(result.env.get(label),translator.term(parse(value,true),scope)),true,label);
    assert.equal(scope.equal(result.env.get(label),translator.term(parse(value==="right_"?"left_":"right_",true),scope)),false,label);
  }
});

test("deferred namespace selectors retain member substitutions and pattern-local alternatives",async t=>{
  const {table,inputs,program,env,source}=await setup(t);
  const origin=sourceOrigin({...source,start:0,end:1});
  const field=table.allocate(["namespace","deferred"],{role:"field",label:"x",origin});
  const p=table.allocate(["namespace","deferred"],{role:"pattern",label:"p",origin});
  const x=table.allocate(["namespace","deferred"],{role:"pattern",label:"x",origin});
  const context=inputs.context.namespace("p",[["x",bindingResolution(field.id)]],"Parent").defer("p",p.id).defer("x",x.id);
  const resolve=(text,at=context)=>resolveBindingSyntax(parse(text,true),{table,source,owner:["namespace","expression"],
    context:at,constructors:inputs.constructors});
  assert.ok(bindingUses(resolve("_.(x)",inputs.context)).some(use=>use.kind==="hole"),"an ordinary receiver hole stays a hole");
  const syntax=resolve("p.(x)"),cloned=cloneBindingSyntax(syntax,table,["namespace","copy"]).syntax;
  assert.equal(sameBindingSyntax(syntax,cloned),true);
  assert.deepEqual(new LexicalContext(JSON.parse(JSON.stringify(context.snapshot()))).selector("p"),context.selector("p"));
  const replacement=resolve("right_",inputs.context);
  const substituted=substituteBindingSyntax(cloned,new Map([[field.id,replacement]]),table,["namespace","substitution"]);
  const qualified=substituteBindingSyntax(resolve("p.x"),new Map([[field.id,replacement]]),table,["namespace","qualified"]);
  const translator=new Translator({checker:program.checker,normalize:false,compilationBindings:program.compilationBindings});
  const values=new Map(env).set(inputs.adapter.key(p.id),env.get("chosen")).set(inputs.adapter.key(x.id),env.get("left_"));
  for(const [pRole,xRole,expected] of [["constructor","constructor","right_"],["constructor","variable","left_"],
    ["variable","constructor","left_"],["variable","variable","left_"]]) {
    const outcomes=new SlotOutcomes().decide(p.id,pRole).decide(x.id,xRole);
    const scope=new Scope(translator.unit({bindingAdapter:inputs.adapter}),new Map(),values,new Map(),outcomes);
    const value=translator.term(lowerBindingSyntax(substituted,inputs.adapter,outcomes),scope);
    assert.equal(scope.equal(value,translator.term(parse(expected,true),scope)),true,`${pRole}/${xRole}`);
    assert.equal(scope.equal(value,translator.term(parse(expected==="right_"?"left_":"right_",true),scope)),false,`${pRole}/${xRole}`);
    const member=translator.term(lowerBindingSyntax(qualified,inputs.adapter,outcomes),scope);
    assert.equal(scope.equal(member,translator.term(parse(pRole==="constructor"?"right_":"left_",true),scope)),true,
      "qualified references restore the namespace field after a constructor decision");
  }
  assert.doesNotThrow(()=>snapshotSyntax(substituted));
});

test("source activation occurrences share receiver meaning without merging their source histories",async t=>{
  const {table,inputs,program,env,source}=await setup(t);
  const translator=new Translator({checker:program.checker,normalize:false,compilationBindings:program.compilationBindings});
  const records=new Map();let index=0,capturedEnv=env;
  const prepare=(text,changed={})=>activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),changed.env??env),
    parse(text).declarations[0],{...inputs,...changed},{owner:["capture-equality",String(index++)],source});
  const build=text=>{
    const prepared=prepare(text),record=retainTheorySource(prepared.item,{table,source,owner:["capture-equality",String(index)],
      context:prepared.context,constructors:inputs.constructors},{lookup:name=>records.get(name)});
    const built=retainedTheoryArtifacts(record,{table,owner:["capture-equality","generated",String(index)]});
    records.set(record.name,built.record);capturedEnv=withSourceCaptures(capturedEnv,prepared,inputs.adapter);
    return {prepared,...built};
  };
  const parent=build("use chosen; theory P(U < UU0, i : M) { k : Two; }");
  const child=build("use chosen; theory C(U < UU0, i : M) extends p : P {}");
  assert.notEqual(parent.prepared.activations[0].binding.id,child.prepared.activations[0].binding.id);
  assert.equal(parent.prepared.activations[0].capture.id,child.prepared.activations[0].capture.id);
  const first=build("use chosen; theory F1(U < UU0) { F(a : M) : set U; }");
  const second=build("use chosen; theory F2(U < UU0) { F(a : M) : set U; }");
  const both=build("theory Both(U < UU0) extends f1 : F1, f2 : F2 {}");
  assert.equal(both.record.fields.filter(field=>field.kind==="sort").length,1);
  const repeat1=prepare("use receiver(tt); theory A(U < UU0) { k : M; }");
  const repeat2=prepare("use receiver(tt); theory B(U < UU0) { k : M; }");
  assert.equal(repeat1.activations[0].capture.id,repeat2.activations[0].capture.id,"computed receivers also share semantic identities");
  assert.notEqual(repeat1.activations[0].binding.id,repeat2.activations[0].binding.id);
  const other=inputs.context.lookup("other");
  const changed=prepare("use chosen; theory D(U < UU0) { k : M; }",{context:inputs.context.bind("chosen",other)});
  assert.notEqual(changed.activations[0].capture.id,parent.prepared.activations[0].capture.id,"a newly resolved receiver keeps a different meaning");
  const declarations=[parent,child,first,second,both].flatMap(built=>built.artifacts.map(({binding,syntax,...annotations})=>
    bindingDeclaration(binding,syntax,annotations)));
  const result=translator.translateSyntax({declarations:[...declarations,...parse(`
    def instance_ : C(U0, left_) := C.make(left_, right_);
    def intended : instance_.k = right_ := refl(right_);
    def wrong : instance_.k = left_ := refl(left_);
  `).declarations]},"",capturedEnv);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.doesNotThrow(()=>snapshotSyntax({captures:parent.prepared.captures,activations:parent.prepared.activations,
    context:parent.prepared.context.snapshot()}));
});
