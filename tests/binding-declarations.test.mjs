import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {ScopePoints} from "../web/translator/scope-points.mjs";
import {resolveBindingModule,lowerBindingModule,bindingDeclaration,lowerBindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {sourceOrigin} from "../web/cubist/bindings.mjs";
import {cloneBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";

const module=await create();
const base="inductive Two { left_; right_; } inductive Nat { zero; succ(n : Nat); } inductive Loopy { base; loop(x : Loopy) : x = x; } inductive List(A : U0) : U0 { nil; cons(x : A, xs : List(A)); } inductive Tree { leaf; node(l : Tree, d : Nat, r : Tree); } def recurse_ : U0 := Unit;";

// Exercise complete ordinary declarations through the real translator's
// admission path. This pilot prepares the explicitly migrated family only;
// the production module resolver moves with the retained families in CB2/3.
async function prepared(t,source,{clone=false,destination=new Map()}={}) {
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check(base,"base")).gaps,[]);
  const points=[],recorder=new ScopePoints("module-pilot",{onPoint:point=>points.push(point)}),table=recorder.table;
  const imports=new Map();
  for(const [label,value] of program.modules.get("base")) {
    if(!/^[A-Za-z_][A-Za-z0-9_]*$/.test(label))continue;
    const start=base.indexOf(label),record=table.allocate(["import"],{role:"declaration",label,
      origin:sourceOrigin({revision:"base-1",module:"base",start,end:start+label.length})});
    imports.set(record.id,value);
  }
  const prepared=resolveBindingModule(parse(source),source,{table,imports,source:{revision:"pilot-1",module:"pilot"}});
  if(clone)prepared.declarations=prepared.declarations.map(({binding,syntax},index)=>({binding,
    syntax:cloneBindingSyntax(syntax,table,["module","pilot","clone",String(index)]).syntax}));
  const {adapter}=prepared,artifacts=prepared.declarations.map(d=>d.syntax);
  const env=new Map([...destination,...prepared.env]);
  const checker=Object.create(program.checker);
  checker.bindingName=label=>`pilot__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"pilot",scopePoints:recorder});
  const result=translator.translateSyntax(lowerBindingModule(prepared),source,env,{bindingAdapter:adapter});
  return {program,translator,result,points,table,artifacts,adapter};
}

test("retained generated declarations enter a mixed source queue with exact references and shared refusals",async t=>{
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check(base+" notation digits { numeral(n : Nat) := n; }","base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,imports=new Map();
  const env=program.modules.get("base");
  for(const [label,value] of env)if(/^[A-Za-z_][A-Za-z0-9_]*$/.test(label)) {
    const binding=registry.ofValue(value);if(binding)imports.set(binding.id,value);
  }
  const source="def saved(x : Two) : Two := left_; def broken : Unit := Two; def downstream : Unit := broken;";
  const resolved=resolveBindingModule(parse(source),source,{table,imports,source:{revision:"generated",module:"pilot"}});
  const declarations=resolved.declarations.map(({binding,syntax})=>bindingDeclaration(binding,syntax,
    {generated:{theory:"T",family:"base",role:"make"}}));
  assert.doesNotThrow(()=>snapshotSyntax(declarations),"the queue contains inert syntax, not adapters or handles");
  const serialized=JSON.parse(JSON.stringify(declarations));
  const before=parse("def left_ : Two := right_;").declarations;
  const after=parse("def native : Nat := digits.(2);").declarations;
  const checker=Object.create(program.checker);
  checker.bindingName=label=>`pilot__${label}`;
  checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
  const translator=new Translator({checker,normalize:false,moduleName:"pilot",compilationBindings:registry});
  const result=translator.translateSyntax({declarations:[...before,...serialized,...after]},source,env);
  assert.deepEqual(result.declarations.filter(d=>d.status==="not-translated").map(d=>d.name),["broken","downstream"]);
  assert.equal(result.env.get("downstream").blockedBy,"pilot__broken");
  assert.equal(result.env.get(resolved.adapter.key(resolved.declarations[1].binding.id)),result.env.get("broken"));
  const scope=new Scope(translator.unit(),new Map(),result.env);
  const actual=translator.term(parse("saved(right_)",true),scope);
  const originalScope=new Scope(translator.unit(),new Map(),env);
  const intended=translator.term(parse("left_",true),originalScope);
  const wrong=translator.term(parse("right_",true),originalScope);
  assert.equal(scope.equal(actual,intended),true);
  assert.equal(scope.equal(actual,wrong),false);
  assert.equal(scope.equal(result.env.get("native"),translator.term(parse("succ(succ(zero))",true),originalScope)),true);
  assert.equal(declarations[0].body[0].value.kind,"bindingReference","entry lowering does not mutate the retained artifact");
  const invalid=structuredClone(declarations[0]);
  invalid.body[0].value.resolution={tag:"reserved",label:"ambient_lookup"};
  assert.throws(()=>lowerBindingDeclaration(invalid,table),/late lookup is not allowed/);
});

test("recursive bodies do not replace an earlier same-named declaration in their signature",async t=>{
  const source=`def recurse_(n : Nat, x : recurse_) : recurse_ := match n {
    zero => x; succ(k) => recurse_(k, x);
  }; def client : Unit := recurse_(succ(zero), tt);`;
  const {program,translator,result}=await prepared(t,source);
  assert.deepEqual(result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]),[]);
  const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
  assert.equal(scope.equal(result.env.get("client"),translator.term(parse("tt",true),scope)),true);
});

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
def predecessor(n : Nat) : Nat := induction n return Nat { zero => zero; succ(k) with h => k; };
def predecessor_statement(n : Nat) : Nat { induction n { zero => { exact zero; } succ(k) with h => { exact k; } } }
def nested(n : Nat) : Nat {
  match n { zero => { exact zero; } succ(k) => {
    match k { zero => { exact zero; } succ(j) => { exact nested(k); } }
  } }
}
def predecessor_value : Nat := predecessor(succ(succ(zero)));
def predecessor_statement_value : Nat := predecessor_statement(succ(succ(zero)));
def nested_value : Nat := nested(succ(succ(zero)));
def loops(t : Loopy) : Unit { induction t {
  base => { exact tt; }
} obligations { loop(x) @ i with ih => { exact ih; } } }
def loops_value : Unit := loops(base);
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
    for(const label of ["predecessor_value","predecessor_statement_value"]) {
      assert.equal(scope.equal(result.env.get(label),expected("succ(zero)")),true,label);
      assert.equal(scope.equal(result.env.get(label),expected("zero")),false,label);
    }
    assert.equal(scope.equal(result.env.get("nested_value"),expected("zero")),true);
    assert.equal(scope.equal(result.env.get("loops_value"),expected("tt")),true);
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

test("retained proof statements bind goal-dependent values without capturing earlier scopes",async t=>{
  const source=`
def introduced(x : Two) : Two -> Two { let saved := x; intro x; exact saved; }
def nested : forall U < UU0. forall A : U. A -> A { intro U; intro A; intro x; exact x; }
def extensional : (fun (x : Two) => x) = (fun (y : Two) => y) { ext x; rfl; }
def obtained(x : Two) : Two {
  let p : exists y : Two. exists z : Two. y = y := (x, (right_, refl(x)));
  obtain (x, (y, h)) := p;
  exact y;
}
def shadowed(x : Two) : Two { obtain (x, y) := typed((exists z : Two. Two), (right_, x)); exact y; }
def value_intro : Two := introduced(left_, right_);
def value_nested : Two := nested(U0, Two, right_);
def value_obtain : Two := obtained(left_);
def value_shadow : Two := shadowed(left_);
def too_early : Two { let saved := y; obtain (x, y) := typed((exists z : Two. Two), (left_, right_)); exact saved; }
`;
  for(const clone of [false,true]) {
    const {result,program,translator}=await prepared(t,source,{clone});
    const failures=result.declarations.filter(d=>d.status!=="checked-native-cubical");
    assert.deepEqual(failures.map(d=>d.name),["too_early"],failures.map(d=>[d.name,d.reason]));
    assert.match(failures[0].reason,/Untranslated name: y/);
    const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
    for(const [label,intended,captured] of [["value_intro","left_","right_"],["value_nested","right_","left_"],
      ["value_obtain","right_","left_"],["value_shadow","left_","right_"]]) {
      assert.equal(scope.equal(result.env.get(label),translator.term(parse(intended,true),scope)),true,label);
      assert.equal(scope.equal(result.env.get(label),translator.term(parse(captured,true),scope)),false,label);
    }
    for(const declaration of result.declarations.filter(d=>d.term))
      assert.doesNotMatch(JSON.stringify(declaration.term),/\\u0000id/,declaration.name);
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

test("module preparation and admission share duplicate ownership without replacing an earlier identity",async t=>{
  const {result,program,translator}=await prepared(t,"def saved : Two := right_; def saved : Two := left_; def client : Two := saved;");
  assert.match(result.declarations[1].reason,/Duplicate declaration saved/);
  assert.equal(result.declarations[2].status,"checked-native-cubical");
  const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
  assert.equal(scope.equal(result.env.get("client"),translator.term(parse("right_",true),scope)),true);
  assert.equal(scope.equal(result.env.get("client"),translator.term(parse("left_",true),scope)),false);
});

test("identity clauses preserve nominal shadowing and construct values without destination spellings",async t=>{
  const source=`
def same(n : Nat) : Nat := match n { zero => zero; m => m; };
def legacy(n : Nat) : Nat := induction n return Nat { zero => zero; succ h => succ(h); };
def shadow(n : Nat) : Nat := induction n return Nat { zero => zero; succ(k) with k => k; };
def len2(A : U0, xs : List(A)) : Nat := match xs, A {
  nil, B => zero; cons(x, rest), B => succ(len2(B, rest));
};
def same_value : Nat := same(succ(succ(zero)));
def legacy_value : Nat := legacy(succ(succ(zero)));
def shadow_value : Nat := shadow(succ(succ(zero)));
def length_value : Nat := len2(Two, cons(left_, cons(right_, nil)));
`;
  for(const clone of [false,true]) {
    const {result,program,translator}=await prepared(t,source,{clone});
    assert.deepEqual(result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]),[]);
    const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
    const zero=translator.term(parse("zero",true),scope),two=translator.term(parse("succ(succ(zero))",true),scope);
    for(const label of ["same_value","legacy_value","length_value"])assert.equal(scope.equal(result.env.get(label),two),true,label);
    assert.equal(scope.equal(result.env.get("shadow_value"),zero),true);
    assert.equal(scope.equal(result.env.get("shadow_value"),two),false);
  }
  const program=new CubicalProgram(module,async()=>base);t.after(()=>program.dispose());
  const nominal=await program.check(`import base; ${source}`,"main");
  assert.deepEqual(nominal.gaps,[]);
  const translator=new Translator({checker:program.checker}),scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
  assert.equal(scope.equal(program.modules.get("main").get("shadow_value"),translator.term(parse("zero",true),scope)),true);
});

test("clause variables are distinct by public label in direct and compiled paths",async t=>{
  const source=`
def duplicate_tree(t : Tree) : Nat := induction t return Nat { leaf => zero; node(x, x, r) with a, b => x; };
def duplicate_match(t : Tree) : Nat := match t { leaf => zero; node(x, x, r) => zero; };
def duplicate_dimension(t : Loopy) : Unit := match t { base => tt; loop(y) @ y => tt; };
def duplicate_compiled_dimension(t : Loopy, u : Unit) : Unit := match t, u { base, _ => tt; loop(y) @ y, _ => tt; };
def pick(t : Tree) : Nat := induction t return Nat { leaf => zero; node(l, d, r) with a, b => d; };
def picked : Nat := pick(node(leaf, succ(zero), leaf));
def hypothesis(n : Nat) : Nat := induction n return Nat { zero => zero; succ(k) with h => h; };
`;
  const program=new CubicalProgram(module,async()=>base);t.after(()=>program.dispose());
  const nominal=await program.check(`import base; ${source}`,"main");
  assert.deepEqual(nominal.gaps.map(gap=>gap.name),["duplicate_tree","duplicate_match","duplicate_dimension","duplicate_compiled_dimension"]);
  for(const gap of nominal.gaps)assert.match(gap.reason,/^[xy] is bound twice in this clause/);
  for(const clone of [false,true]) {
    const {result,program,translator}=await prepared(t,source,{clone});
    const failures=result.declarations.filter(d=>d.status!=="checked-native-cubical");
    assert.deepEqual(failures.map(d=>d.name),nominal.gaps.map(gap=>gap.name));
    for(const failure of failures)assert.match(failure.reason,/^[xy] is bound twice in this clause/);
    const scope=new Scope(translator.unit(),new Map(),program.modules.get("base"));
    assert.equal(scope.equal(result.env.get("picked"),translator.term(parse("succ(zero)",true),scope)),true);
    const term=result.declarations.find(d=>d.name==="hypothesis").term;
    assert.doesNotMatch(JSON.stringify(term),/\\u0000id/);
    const shown=program.checker.displayText(term,1000);
    assert.match(shown,/with h/);
    assert.doesNotMatch(shown,/id \[/);
  }
});
