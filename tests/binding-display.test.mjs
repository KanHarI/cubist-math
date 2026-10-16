import test from "node:test";
import assert from "node:assert/strict";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {BindingTable,LexicalContext,bindingResolution,reservedResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,bindingSyntaxView,sameBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {bindingDeclaration} from "../web/translator/binding-module.mjs";
import {mapSyntax} from "../web/translator/syntax-graph.mjs";
import {parameterLambdas} from "../web/cubist/telescopes.mjs";
import {generatedDeclaration} from "../web/generated-cubist.mjs";

function fixture(text) {
  const table=new BindingTable("display-test"),source={revision:table.revision,module:"main"};
  const context=new LexicalContext(reservedReferences(text).map(label=>[label,reservedResolution(label)]));
  let serial=0;
  const resolve=(code,ctx=context)=>resolveBindingSyntax(parse(code).declarations[0],{table,source,context:ctx,owner:[String(serial++)]});
  const binding=table.allocate(["declaration"],{role:"declaration",label:"f",origin:sourceOrigin({...source,start:0,end:1})});
  const print=syntax=>generatedDeclaration(bindingDeclaration(binding,syntax),{table});
  const expression=syntax=>bindingSyntaxView(syntax,parameterLambdas(syntax.tree.params,syntax.tree.value??syntax.tree.body[0].value));
  return {table,context,source,resolve,binding,print,expression};
}

test("CB5: a helper's free parameter survives printing under an equal-label local",()=>{
  const text="def f(A : U0, x : A) : A := (fun (y : A) => x)(x);",f=fixture(text);
  const syntax=f.resolve(text),id=syntax.tree.body[0].value.fn.name.bindingId;
  const renamed={...syntax,tree:mapSyntax(syntax.tree,node=>node.bindingId===id?{...node,text:"x",label:"x"}:undefined)};
  const output=f.print(renamed);
  assert.match(output,/Display alias x1 denotes local binder x/);
  assert.match(output,/fun \(x1 : A\) => x/);
  assert.equal(sameBindingSyntax(f.expression(renamed),f.expression(f.resolve(output))),true);
  const captured=output.replace(/=> x\)/,"=> x1)");
  assert.notEqual(captured,output);
  assert.equal(sameBindingSyntax(f.expression(renamed),f.expression(f.resolve(captured))),false,
    "the control distinguishes printing the inner binder instead of the captured parameter");
});

test("CB5: nested and grouped binders reparse to their original binding structure",()=>{
  for(const text of [
    "def f(A : U0, x : A) : A := (fun (x : A) => (fun (x : A) => x)(x))(x);",
    "def f(A : U0) : U0 := forall A, x : A. A;",
    "def f(A : U0, x : A) : A := (fun (x : A) => (fun (x1 : A) => x)(x))(x);",
  ]) {
    const f=fixture(text),syntax=f.resolve(text),printed=f.print(syntax);
    assert.doesNotMatch(printed,/⟦/);
    assert.equal(sameBindingSyntax(f.expression(syntax),f.expression(f.resolve(printed))),true,printed);
    assert.equal(f.print(syntax),printed,"stable without identity allocation or mutation");
  }
});

test("CB5: same-named captures and public-parameter shadows receive distinct identity markers",()=>{
  const text="def f(c : Unit) := (left_, right_);",f=fixture(text),globals=new Map();
  let context=f.context;
  for(const module of ["left_","right_"]) {
    const record=f.table.allocate([module],{role:"declaration",label:"c",origin:sourceOrigin({...f.source,module,start:0,end:1})});
    context=context.bind(module,bindingResolution(record.id));
    globals.set(record.id,{name:"c",module,binding:module});
  }
  const syntax=f.resolve(text,context),links=[];
  const printed=generatedDeclaration(bindingDeclaration(f.binding,syntax),{table:f.table,globals,links});
  assert.match(printed,/f := fun \(c : Unit\)/,"the public parameter label stays c");
  const captured=links.filter(link=>["left_","right_"].includes(link.binding));
  assert.equal(captured.length,2);
  assert.notEqual(captured[0].name,captured[1].name);
  assert.ok(captured.every(link=>/^c⟦[0-9]+⟧$/.test(link.name)));
  assert.ok(captured.every(link=>printed.slice(link.start,link.end)===link.name));
});

test("CB5: a referenced anonymous public parameter stays visibly anonymous",()=>{
  const text="def f(x : Unit) : Unit := x;",f=fixture(text),syntax=f.resolve(text);
  const id=syntax.tree.params[0].name.bindingId;
  const renamed={...syntax,tree:mapSyntax(syntax.tree,node=>node.bindingId===id?{...node,text:"_",label:"_"}:undefined)};
  const printed=f.print(renamed);
  assert.match(printed,/anonymous parameter/);
  assert.equal((printed.match(/_⟦1⟧/g)??[]).length,3,"legend, binder and reference share the marker");
});

test("CB5: checked header arguments never print an unbound name or capture a global",()=>{
  const text="def f : Unit := tt;",f=fixture(text),syntax=f.resolve(text);
  const record=f.table.allocate(["captured"],{role:"declaration",label:"x",origin:sourceOrigin({...f.source,module:"producer",start:0,end:1})});
  const globals=new Map([[record.id,{name:"x",module:"producer",keys:["producer__x"]}]]);
  const print=value=>generatedDeclaration(bindingDeclaration(f.binding,{...syntax,tree:{...syntax.tree,
    body:[{kind:"exact",value:{kind:"instantiated",value,args:[]}}]}}),{table:f.table,globals});
  assert.match(print({tag:"DefRef",name:"producer__x"}),/:= x;/);
  assert.match(print({tag:"Var",name:"missing__x"}),/:= checked⟦1⟧;/);
  assert.doesNotMatch(print({tag:"Var",name:"\u0000private"}),/\u0000/);
  assert.match(print({tag:"Lam",name:"x",domain:{tag:"Unit"},body:{tag:"DefRef",name:"producer__x"}}),/:= checked⟦1⟧;/);
  assert.match(print({tag:"Lam",name:"y",domain:{tag:"Unit"},body:{tag:"DefRef",name:"producer__x"}}),/fun \(y : Unit\) => x/);
});

test("CB5: printing a model opening cannot rebind an already captured declaration",()=>{
  const text="def f(m : Unit) : Unit := m.(external);",f=fixture(text);
  const record=f.table.allocate(["external"],{role:"declaration",label:"c",origin:sourceOrigin({...f.source,module:"producer",start:0,end:1})});
  const resolved=f.resolve(text,f.context.withNotations([]).bind("external",bindingResolution(record.id))),links=[];
  // A moved capture retains its identity even under a new model opening.
  const syntax={...resolved,tree:mapSyntax(resolved.tree,node=>node.kind==="bindingReference"&&node.spelling==="external"
    ?{...node,resolution:bindingResolution(record.id)}:undefined)};
  const printed=generatedDeclaration(bindingDeclaration(f.binding,syntax),{table:f.table,links,
    globals:new Map([[record.id,{name:"c",module:"producer",binding:"producer__c"}]])});
  assert.match(printed,/m\.\(c⟦\d+⟧\)/,"an opened model's c cannot steal the captured declaration");
  const link=links.find(link=>link.binding==="producer__c");
  assert.equal(printed.slice(link.start,link.end),link.name);
});


test("CB5: formatting placeholders cannot replace member or named-argument labels",()=>{
  for(const text of [
    "def f(A : U0, S : A) : A := S.z0(S.z1);",
    "def f(A : U0, S : A) : A := S(z0 := S, z1 := S);",
  ]) {
    const f=fixture(text),syntax=f.resolve(text),links=[];
    const printed=generatedDeclaration(bindingDeclaration(f.binding,syntax),{table:f.table,links});
    assert.equal(sameBindingSyntax(f.expression(syntax),f.expression(f.resolve(printed))),true,printed);
    assert.match(printed,/z0/);assert.match(printed,/z1/);
    assert.ok(links.every(link=>!/^z[01]$/.test(link.name)),"raw field labels cannot acquire a binder link");
  }
});

test("CB5: disjoint scopes reuse their labels while overlapping scopes retain their bindings",()=>{
  for(const text of [
    "def f(A : U0, a : A) : A := ((fun (x : A) => x)(a), (fun (x : A) => x)(a));",
    "def f(A : U0, a : A) : A := (fun (x : A) => (fun (x : A) => x)(x))(a);",
    "def f(A : U0) : U0 := forall x, x1 : A. forall x : A. x1;",
  ]) {
    const f=fixture(text),syntax=f.resolve(text),printed=f.print(syntax);
    assert.equal(sameBindingSyntax(f.expression(syntax),f.expression(f.resolve(printed))),true,printed);
    if(text.includes("), (fun"))assert.doesNotMatch(printed,/Display alias|x1|⟦/);
  }
});


test("CB5: operator operands preserve binder grouping through rendering and parsing",()=>{
  for(const text of [
    "def f(A : U0) : U0 := (forall y : A. A) -> A;",
    "def f(A : U0, B : U0, x : A) : U0 := (x = x) -> B;",
    "def f(A : U0) : U0 := (forall x, y : A. A) -> A;",
    "def f(A : U0, B : U0) : U0 := (exists y : A. B) and B;",
    "def f(A : U0) : U0 := (fun (y : A) => y) = (fun (y : A) => y);",
    "def f(A : U0, a : A, j : Interval) : A := (path i => a) @ j;",
    "def f(A : U0) : U0 := A -> forall y : A. A;",
    "def f(A : U0) : U0 := forall x : (forall y : A. A). A;",
  ]) {
    const f=fixture(text),syntax=f.resolve(text),printed=f.print(syntax);
    assert.equal(sameBindingSyntax(f.expression(syntax),f.expression(f.resolve(printed))),true,printed);
    if(text.includes("(x = x) -> B"))assert.match(printed,/:= \(\(x = x\) -> B\);/);
  }
  const text="def f(A : U0) : (fun (x : A) => x) = (fun (x : A) => x) { calc { (fun (x : A) => x) = (fun (x : A) => x) by { rfl; } } }";
  const f=fixture(text),syntax=f.resolve(text),printed=f.print(syntax);
  assert.equal(sameBindingSyntax(syntax,f.resolve(printed)),true,printed);
});

test("CB5: binders in separate scopes of one clause receive distinct labels",()=>{
  const text="def f(A : U0, a : A, s : A) : A := (fun (i : A) => match s return A { sq @ i @ i1 => i1; })(a);";
  const f=fixture(text),syntax=f.resolve(text),printed=f.print(syntax);
  assert.match(printed,/sq @ i1 @ i11 => i11/);
  assert.doesNotMatch(printed,/⟦/);
  assert.equal(sameBindingSyntax(f.expression(syntax),f.expression(f.resolve(printed))),true,printed);
});
