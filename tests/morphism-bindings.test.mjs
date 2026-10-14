import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {BindingTable,LexicalContext,bindingResolution,reservedResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {RetainedInterfaces,interfaceType} from "../web/cubist/retained-interfaces.mjs";
import {morphismSource} from "../web/cubist/morphisms.mjs";
import {equationalSupport} from "../web/translator/initial-models.mjs";

const declaration=text=>parse(text).declarations[0];
function setup(headerText="def T(U < UU0) : Unit := tt;") {
  const source={revision:"source",module:"main"},table=new BindingTable("compilation");
  const outer=table.allocate(["global"],{role:"declaration",label:"M",origin:sourceOrigin({...source,start:0,end:1})});
  const context=new LexicalContext([...['U0','UU0','Unit','tt','IsSet'].map(label=>[label,reservedResolution(label)]),
    ["M",bindingResolution(outer.id)]]);
  const interfaces=new RetainedInterfaces({table,source,owner:["theory"],context});
  const d=declaration(headerText),header=interfaces.parameters(d.name,d.params);
  const retain=(text,kind="operation")=>interfaces.retain(declaration(text),{kind});
  const fields=[];
  const field=(entry,extra={})=>fields.push({...entry,name:entry.label,type:interfaceType(entry).tree,...extra});
  const record=()=>({name:"T",universes:["U"],universeIds:[header.tree.params[0].name.bindingId],
    params:header.tree.params.slice(1).map(p=>({id:p.name.bindingId,name:p.name.text,type:p.type})),parents:[],
    bindingSyntax:header,fields,derived:interfaces.entries.filter(entry=>entry.kind==="derived")});
  return {interfaces,outer,retain,field,record};
}

test("morphism shape analysis distinguishes same-labelled external, carrier and local identities",()=>{
  const {outer,retain,field,record}=setup();
  const external=retain("def outside(x : M) : M := x;");field(external);
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  field(retain("def c : M := tt;"));
  const polymorphic=retain("def poly(M : U0, x : M) : M := x;");field(polymorphic);
  const result=morphismSource(record());
  assert.equal(result.missing,undefined);assert.equal(result.pending,undefined);
  assert.equal(result.support.status,"conditional");assert.equal(result.isoSupport.status,"conditional");
  assert.ok(result.declarations.some(d=>d.name==="T.Hom.id"));
  const markers=[...result.typeMarkers.values()];
  assert.ok(markers.some(({type})=>type.resolution?.id===outer.id),"a same-named source global stays external");
  const local=polymorphic.syntax.tree.params[0].name.bindingId;
  assert.ok(markers.some(({type,locals})=>type.resolution?.id===local&&locals.has(local)),
    "a local type parameter carries its own template binder correspondence");
  assert.ok(markers.every(({type})=>type.resolution?.id!==carrier.id),"carrier positions are mapped, not classified as fixed types");
});

test("morphism planning returns pending interpretations instead of treating them as fixed",()=>{
  const {retain,field,record}=setup();
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  field(retain("def op(x : match tt { unknown => Unit; }) : M := tt;"));
  const result=morphismSource(record());
  assert.ok(result.pending.some(use=>use.kind==="deferred-pattern"));
  assert.equal(result.declarations,undefined);
  assert.equal(result.support.status,"pending");
  assert.equal(result.missing,undefined,"an unresolved interpretation is not a support refusal");
});

test("Hom transport support follows proof identities and records its dependency",()=>{
  const {retain,field,record}=setup();
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  const proof=retain("def proof_ : Unit := tt;","law");field(proof);
  const operation=retain("def op(p : proof_ = proof_) : M := tt;");field(operation);
  const result=morphismSource(record());
  assert.equal(result.support.status,"unsupported");
  assert.equal(result.support.dependency.id,proof.id);
  assert.equal(result.support.field,operation.id);
  assert.equal(result.isoSupport,result.support);
  assert.equal(result.declarations,undefined);
});

test("a later helper cannot retarget an earlier header dependency in Hom support",()=>{
  const {retain,field,record}=setup("def T(U < UU0, n : Unit) : Unit := tt;");
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  field(retain("def op(p : n = n) : M := tt;"));
  const later=retain("def n : Unit := tt;","derived");
  const retained=record(),result=morphismSource(retained);
  assert.equal(result.support.status,"conditional");
  const domain=result.support.mapping.operations[0].inputs[0].type;
  assert.equal(domain.left.resolution.id,retained.params[0].id);
  assert.notEqual(domain.left.resolution.id,later.id);
  assert.equal(equationalSupport(retained).status,"conditional");
});

test("Hom variance and equational constructor support remain different predicates",()=>{
  const {retain,field,record}=setup();
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  const operation=retain("def run(k : M -> Unit) : M := tt;");field(operation);
  const retained=record();
  assert.equal(morphismSource(retained).support.status,"conditional");
  const equational=equationalSupport(retained);
  assert.equal(equational.status,"unsupported");assert.equal(equational.field,operation.id);
  assert.equal(equational.dependency.id,carrier.id);
});

test("an indexed set can have a Hom plan while its Iso plan remains unsupported",()=>{
  const {retain,field,record}=setup();
  const carrier=retain("def M : U := Unit;","sort");field(carrier);
  field(retain("def M_is_set : IsSet(U, M) := tt;","evidence"),{of:carrier.id,evidence:"IsSet"});
  const family=retain("def F(x : M) : U := Unit;","sort");field(family,{family:true});
  field(retain("def F_is_set(x : M) : IsSet(U, F(x)) := tt;","evidence"),{of:family.id,evidence:"IsSet"});
  const result=morphismSource(record());
  assert.equal(result.support.status,"conditional");
  assert.equal(result.isoSupport.status,"unsupported");
  assert.ok(result.declarations.some(d=>d.name==="T.Hom.compose"));
  assert.ok(!result.declarations.some(d=>d.name==="T.Iso"));
});
