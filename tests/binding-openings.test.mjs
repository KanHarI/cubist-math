import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {sourceBindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
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
async function setup(t,extra="") {
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
    ${extra}
  `,"base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base");
  const inputs=sourceBindingInputs(registry,env,{reserved:reservedReferences("U0 UU0 Unit tt refl")});
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

const operatorModels=`
  theory Arithmetic(U < UU0) {
    M : U; x : M;
    plus(a, b : M) : M notation a + b;
    negate(a : M) : M notation -a;
  }
  def leftOps : Arithmetic(U0) := Arithmetic.make(Two, right_, fun (a, b : Two) => a, fun (a : Two) => right_);
  def rightOps : Arithmetic(U0) := Arithmetic.make(Two, right_, fun (a, b : Two) => b, fun (a : Two) => left_);
  theory Routed(U < UU0) {
    M : U;
    plus(a, b : M) : M notation a + b;
    power(a : M, b : Two) : M notation a ^ rightOps.(b);
  }
  def routed : Routed(U0) := Routed.make(Two, fun (a, b : Two) => a, fun (a, b : Two) => b);
`;

test("retained selected operators bind notation separately from caller names and nested selections",async t=>{
  const {retain,check,table}=await setup(t,operatorModels);
  const declarations=[
    "def source_ : Two := leftOps.(left_ + right_);",
    "def negative : Two := leftOps.(-left_);",
    "def nested : Two := leftOps.(rightOps.(left_ + right_));",
    "def local : Two := leftOps.((fun (plus : Two) => plus + right_)(left_));",
    "def sequential : Two { use leftOps; let saved := left_ + right_; use rightOps; exact saved + right_; }",
    "def recipe : Two := routed.(left_ ^ (left_ + right_));",
    "def override : Two := routed.(left_ ^ leftOps.(left_ + right_));",
    "def recipeLocal(x : Two) : Two := routed.(left_ ^ (x + left_));",
    "def callerName(x : Two) : Two := routed.(left_ ^ x);",
    "def endpoint : Two := leftOps.(refl(left_) @ 1);",
    "def missing : Two := leftOps.(chosen.(left_ + right_));",
  ].map(retain);
  const original=JSON.stringify(declarations);
  const copy=cloneBindingSyntax(declarations[5].syntax,table,["operator-copy"]);
  assert.equal(sameBindingSyntax(declarations[5].syntax,copy.syntax),true);
  assert.ok(copy.syntax.owned.every(id=>!declarations[5].syntax.owned.includes(id)));
  assert.ok(copy.syntax.owned.some(id=>table.get(id).role==="notation"));
  declarations[5]={...declarations[5],syntax:copy.syntax};
  assert.doesNotThrow(()=>snapshotSyntax(declarations));
  const {result,equal}=check(declarations,`def leftOps : Arithmetic(U0) := rightOps;
    def rightOps : Arithmetic(U0) := Arithmetic.make(Two, right_, fun (a, b : Two) => a, fun (a : Two) => right_);`);
  assert.deepEqual(failures(result).map(([name])=>name),["missing"],JSON.stringify(failures(result)));
  for(const name of ["source_","local","override","endpoint"]) {
    assert.equal(equal(name,"left_"),true,name);assert.equal(equal(name,"right_"),false,name);
  }
  for(const name of ["negative","nested","sequential","recipe"]) {
    assert.equal(equal(name,"right_"),true,name);assert.equal(equal(name,"left_"),false,name);
  }
  assert.equal(equal("recipeLocal","fun (x : Two) => left_"),true);
  assert.equal(equal("recipeLocal","fun (x : Two) => right_"),false);
  assert.equal(equal("callerName","fun (x : Two) => x"),true);
  assert.equal(equal("callerName","fun (x : Two) => right_"),false);
  assert.equal(JSON.stringify(declarations.slice(0,5)),JSON.stringify(JSON.parse(original).slice(0,5)));
});

test("retained numeral uses keep their reader and Nat through operand recipes and destination shadowing",async t=>{
  const {retain,check}=await setup(t,`
    theory Numeric(U < UU0) { M : U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral; }
    def plain : Numeric(U0) := Numeric.make(Nat, fun (n : Nat) => n);
    def shifted : Numeric(U0) := Numeric.make(Nat, fun (n : Nat) => succ(n));
    theory Powers(U < UU0) { M : U; power(x : M, n : Nat) : M notation x ^ shifted.(n); }
    def powers : Powers(U0) := Powers.make(Nat, fun (x, n : Nat) => n);
  `);
  const declarations=[
    "def literal_value : Nat := plain.(2);",
    "def nested : Nat := shifted.(plain.(0));",
    "def recipe_value : Nat := powers.(zero ^ 0);",
    "def local(shifted : Unit) : Nat := powers.(zero ^ 0);",
    "def param(m : Numeric(U0)) : m.M := m.(2);",
    "def missing_reader : Two := chosen.(0);",
    "def missing_literal : Nat := plain.(0b10);",
    "def limited : Nat := plain.(257);",
  ].map(retain);
  const {result,equal}=check(declarations,"def plain : Numeric(U0) := shifted; def Nat : U0 := Unit;");
  assert.deepEqual(failures(result).map(([name])=>name),["missing_reader","missing_literal","limited"],JSON.stringify(failures(result)));
  assert.match(failures(result).find(([name])=>name==="limited")[1],/limited to 256/);
  assert.equal(equal("literal_value","succ(succ(zero))"),true);
  assert.equal(equal("literal_value","succ(succ(succ(zero)))"),false);
  assert.equal(equal("nested","zero"),true);assert.equal(equal("nested","succ(zero)"),false);
  assert.equal(equal("recipe_value","succ(zero)"),true);assert.equal(equal("recipe_value","zero"),false);
  assert.equal(equal("local","fun (shifted : Unit) => succ(zero)"),true);
});

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

test("file-level notation contexts survive headers, ordered theory operators and inherited helpers",async t=>{
  const {table,inputs,program,env,source}=await setup(t,operatorModels+`
    theory Digits(U < UU0) { M : U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral; }
    def digits : Digits(U0) := Digits.make(Nat, fun (n : Nat) => n);
    def numberReceiver(n : Nat) : Arithmetic(U0) := match n { zero => leftOps; succ(k) => rightOps; };
  `);
  const checker=Object.create(program.checker);checker.bindingName=label=>`notations__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"notations",compilationBindings:program.compilationBindings});
  const term=translator.term.bind(translator);let receiverCalls=0;
  translator.term=(node,...args)=>{if(node.kind==="call"&&node.fn.spelling==="numberReceiver")receiverCalls++;return term(node,...args);};
  const records=new Map();let capturedEnv=env,index=0;
  const build=text=>{
    const owner=["file-notation",String(index++)];
    const prepared=activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),env),
      parse(text).declarations[0],inputs,{owner,source});
    const record=retainTheorySource(prepared.item,{table,source,owner,context:prepared.context,
      constructors:inputs.constructors},{lookup:name=>records.get(name)});
    const built=retainedTheoryArtifacts(record,{table,owner:[...owner,"generated"]});
    records.set(record.name,built.record);capturedEnv=withSourceCaptures(capturedEnv,prepared,inputs.adapter);
    assert.doesNotThrow(()=>snapshotSyntax({record,context:prepared.context.snapshot(),activations:prepared.activations}));
    return {prepared,...built};
  };
  const header=build(`use leftOps; theory Header(U < UU0, p : (left_ + right_) = left_) { anchor : Unit; }`);
  const parent=build(`use leftOps; theory Selected(U < UU0) {
    M : set U;
    def captured(x : Two) : Two := x + right_;
    choose(a, b : M) : M notation a + b;
    def own(a, b : M) : M := a + b;
  }`);
  const child=build(`use rightOps; theory Child(U < UU0) extends s : Selected {}`);
  const later=build(`use leftOps; use rightOps; theory Later(U < UU0) {
    anchor : Unit; def captured : Two := left_ + right_;
  }`);
  const ordered=build(`use digits; use numberReceiver(0); theory Ordered(U < UU0) {
    anchor : Unit; def captured : Two := left_ + right_;
  }`);
  assert.equal(receiverCalls,1,"a later source receiver consumes the earlier captured notation");
  const numeric=build(`use digits; theory Numeric(U < UU0, n : Nat, p : n = 0) {
    anchor : Unit; def captured : Nat := 0;
  }`);
  const refused=build(`use leftOps; use chosen; theory Refused(U < UU0) {
    anchor : Unit; def captured : Two := left_ + right_;
  }`);
  const first=build("use digits; theory First(U < UU0) { F(p : zero = 0) : set U; }");
  const second=build("use digits; theory Second(U < UU0) { F(p : zero = 0) : set U; }");
  const shared=build("theory Shared(U < UU0) extends first_ : First, second_ : Second {}");
  assert.equal(shared.record.fields.filter(field=>field.kind==="sort").length,1);
  assert.equal(first.prepared.activations[0].notation.id,second.prepared.activations[0].notation.id);
  assert.notEqual(first.prepared.activations[0].binding.id,second.prepared.activations[0].binding.id);
  assert.equal(new LexicalContext(JSON.parse(JSON.stringify(parent.prepared.context.snapshot()))).selectedNotation(),
    parent.prepared.activations[0].notation.id);
  assert.ok(bindingUses(parent.record.derived.find(field=>field.label==="captured").syntax)
    .some(use=>use.id===parent.prepared.activations[0].notation.id));
  const declarations=[header,parent,child,later,ordered,numeric,refused,first,second,shared].flatMap(built=>built.artifacts.map(({binding,syntax,...annotations})=>
    bindingDeclaration(binding,syntax,annotations)));
  const result=translator.translateSyntax({declarations:[...parse(`def leftOps : Unit := tt;
    def digits : Unit := tt; def x : Two := right_;`).declarations,...declarations,...parse(`
    def header_value : Header(U0, refl(left_)) := Header.make(refl(left_), tt);
    def chosen : Child(U0) := Child.make(Two, _, fun (a, b : Two) => b);
    def captured_value : Two := chosen.captured(left_);
    def own_value : Two := chosen.own(left_, right_);
    def later_instance : Later(U0) := Later.make(tt);
    def ordered_instance : Ordered(U0) := Ordered.make(tt);
    def numeric_instance : Numeric(U0, zero, refl(zero)) := Numeric.make(zero, refl(zero), tt);
    def later_value : Two := later_instance.captured;
    def ordered_value : Two := ordered_instance.captured;
    def numeric_value : Nat := numeric_instance.captured;
    def intended : captured_value = left_ := refl(left_);
    def wrong : captured_value = right_ := refl(right_);
  `).declarations]},"",capturedEnv);
  assert.deepEqual(failures(result).map(([name])=>name),["Refused.captured","wrong"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/\+.*(not|no)/);
  assert.match(failures(result)[0][1],/chosen's notation/);
  assert.doesNotMatch(failures(result)[0][1],/\u0000id/);
  const scope=new Scope(translator.unit(),new Map(),result.env),equal=(name,source)=>
    scope.equal(result.env.get(name),translator.term(parse(source,true),scope));
  assert.equal(equal("captured_value","left_"),true);assert.equal(equal("captured_value","right_"),false);
  assert.equal(equal("ordered_value","left_"),true);assert.equal(equal("ordered_value","right_"),false);
  assert.equal(receiverCalls,1,"generation never reactivates the captured source receiver");
  for(const name of ["own_value","later_value"]) {
    assert.equal(equal(name,"right_"),true);assert.equal(equal(name,"left_"),false);
  }
  assert.equal(equal("numeric_value","zero"),true);assert.equal(equal("numeric_value","succ(zero)"),false);
});

test("a retained source notation cannot fall back when its capture environment is absent",async t=>{
  const {table,inputs,program,env,source}=await setup(t,operatorModels);
  const translator=new Translator({checker:program.checker,normalize:false,compilationBindings:program.compilationBindings});
  const text="use leftOps; def captured : Two := left_ + right_;";
  const prepared=activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),env),
    parse(text).declarations[0],inputs,{owner:["missing-notation"],source});
  const syntax=resolveBindingSyntax(prepared.item,{table,source,owner:["missing-notation","body"],
    context:prepared.context,constructors:inputs.constructors});
  const node=lowerBindingSyntax(syntax,inputs.adapter).body[0].value;
  const missing=new Scope(translator.unit({bindingAdapter:inputs.adapter}),new Map(),env);
  assert.throws(()=>translator.term(node,missing),/no checked context for its identity/);
  const present=missing.withEnv(withSourceCaptures(env,prepared,inputs.adapter));
  assert.equal(present.equal(translator.term(node,present),translator.term(parse("left_",true),present)),true);
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

test("file-level activation classifies attached notation against the ordered opened receiver",async t=>{
  const {table,inputs,program,env,source}=await setup(t,`
    theory Numerals(U < UU0) { M : U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral; }
    def recipe : Numerals(U0) := Numerals.make(Nat, fun (n : Nat) => n);
    notation recipe { numeral(n : Nat) := succ(n); }
    theory Pack(U < UU0) { recipe : Numerals(U); }
    def outer : Pack(U0) := Pack.make(Numerals.make(Nat, fun (n : Nat) => succ(succ(n))));
  `);
  const checker=Object.create(program.checker);
  checker.bindingName=label=>`activation__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,compilationBindings:program.compilationBindings});
  let index=0;
  const prepare=text=>activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),env),
    parse(text).declarations[0],inputs,{owner:["attached","source",String(index++)],source});
  assert.throws(()=>prepare("use recipe; theory Refused(U < UU0) { M : U; }"),/named notation activation/);
  const prepared=prepare(`use outer; use recipe;
    theory T(U < UU0) { M : U; point : M; def picked : Nat := read(zero); }`);
  assert.equal(prepared.activations.length,2);
  const record=retainTheorySource(prepared.item,{table,source,owner:["attached","T"],context:prepared.context,
    constructors:prepared.constructors});
  const built=retainedTheoryArtifacts(record,{table,owner:["attached","generated"]});
  const declarations=built.artifacts.map(({binding,syntax,...annotations})=>bindingDeclaration(binding,syntax,annotations));
  const result=translator.translateSyntax({declarations:[...declarations,...parse(`
    def chosen : T(U0) := T.make(Two, left_);
    def value : Nat := chosen.picked;
    def intended : value = succ(succ(zero)) := refl(succ(succ(zero)));
    def wrong : value = succ(zero) := refl(succ(zero));
  `).declarations]},"",withSourceCaptures(env,prepared,inputs.adapter));
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  const scope=new Scope(translator.unit(),new Map(),result.env);
  assert.equal(scope.equal(result.env.get("value"),translator.term(parse("succ(succ(zero))",true),scope)),true);
  assert.equal(scope.equal(result.env.get("value"),translator.term(parse("succ(zero)",true),scope)),false);
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
  assert.equal(parent.prepared.activations[0].notation.id,child.prepared.activations[0].notation.id);
  const first=build("use chosen; theory F1(U < UU0) { F(a : M) : set U; }");
  const second=build("use chosen; theory F2(U < UU0) { F(a : M) : set U; }");
  const both=build("theory Both(U < UU0) extends f1 : F1, f2 : F2 {}");
  assert.equal(both.record.fields.filter(field=>field.kind==="sort").length,1);
  const repeat1=prepare("use receiver(tt); theory A(U < UU0) { k : M; }");
  const repeat2=prepare("use receiver(tt); theory B(U < UU0) { k : M; }");
  assert.equal(repeat1.activations[0].capture.id,repeat2.activations[0].capture.id,"computed receivers also share semantic identities");
  assert.equal(repeat1.activations[0].notation.id,repeat2.activations[0].notation.id);
  assert.notEqual(repeat1.activations[0].binding.id,repeat2.activations[0].binding.id);
  const other=inputs.context.lookup("other");
  const changed=prepare("use chosen; theory D(U < UU0) { k : M; }",{context:inputs.context.bind("chosen",other)});
  assert.notEqual(changed.activations[0].capture.id,parent.prepared.activations[0].capture.id,"a newly resolved receiver keeps a different meaning");
  assert.notEqual(changed.activations[0].notation.id,parent.prepared.activations[0].notation.id);
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
