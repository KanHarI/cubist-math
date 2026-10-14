import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {BindingTable,LexicalContext,reservedResolution} from "../web/cubist/bindings.mjs";
import {RetainedInterfaces,interfaceSignature} from "../web/cubist/retained-interfaces.mjs";
import {bindingUses,sameBindingSyntax} from "../web/cubist/binding-syntax.mjs";
import {DependencyAnalysis} from "../web/cubist/dependencies.mjs";

const declaration=source=>parse(source).declarations[0];
const setup=()=>({table:new BindingTable("compilation"),owner:["parent"],source:{revision:"source",module:"parent"},
  context:new LexicalContext(["U0","UU0","Unit","tt"].map(label=>[label,reservedResolution(label)]))});

test("retained interfaces resolve complete grouped telescopes in source order",()=>{
  const options=setup(),interfaces=new RetainedInterfaces(options);
  const header=declaration("def T(U < UU0, n : Unit) : Unit := tt;");
  const syntax=interfaces.parameters(header.name,header.params),n=syntax.tree.params[1].name.bindingId;
  const earlier=interfaces.retain(declaration("def op(p : n = n) : Unit := tt;"),{kind:"operation"});
  const later=interfaces.retain(declaration("def n : Unit := tt;"),{kind:"derived"});
  const grouped=interfaces.retain(declaration("def f(A : U0, A, x : A, p : x = x) : A := x;"),{kind:"derived"});
  const params=grouped.syntax.tree.params;
  assert.equal(params[1].type,params[2].type);
  assert.equal(params[1].type.resolution.id,params[0].name.bindingId);
  assert.notEqual(params[1].type.resolution.id,params[1].name.bindingId);
  assert.equal(params[3].type.left.resolution.id,params[2].name.bindingId);
  const analysis=new DependencyAnalysis([{id:n,kind:"parameter"},...interfaces.entries]);
  assert.ok(analysis.references(interfaceSignature(earlier)).some(use=>use.id===n&&use.category==="parameter"));
  assert.ok(analysis.dependencies(interfaceSignature(earlier)).every(use=>use.id!==later.id));
});

test("structural self is visible only in the body and remains shadowable by parameters",()=>{
  const options=setup(),interfaces=new RetainedInterfaces(options);
  const declarationHeader=declaration("def T(loop : U0) : Unit := tt;");
  const header=interfaces.parameters(declarationHeader.name,declarationHeader.params);
  const previous=header.tree.params[0].name.bindingId;
  const recursive=interfaces.retain(declaration("def loop(x : loop) : loop := loop(x);"),{kind:"derived",self:true});
  assert.equal(recursive.syntax.tree.params[0].type.resolution.id,previous);
  assert.equal(recursive.syntax.tree.type.resolution.id,previous);
  assert.equal(recursive.syntax.tree.body[0].value.fn.resolution.id,recursive.id);
  const shadowed=interfaces.retain(declaration("def shadow(shadow : Unit) : Unit := shadow;"),{kind:"derived",self:true});
  assert.equal(shadowed.syntax.tree.body[0].value.resolution.id,shadowed.syntax.tree.params[0].name.bindingId);
});

test("inherited complete interfaces freshen locals and map only explicit open identities",()=>{
  const options=setup(),parent=new RetainedInterfaces(options);
  const pHeader=declaration("def P(U < UU0) : Unit := tt;");
  const p=parent.parameters(pHeader.name,pHeader.params);
  const carrier=parent.retain(declaration("def M : U := Unit;"),{kind:"sort"});
  const helper=parent.retain(declaration("def first(x, y : M) : M := x;"),{kind:"derived"});
  const child=new RetainedInterfaces({...options,owner:["child"],source:{revision:"source",module:"child"}});
  const cHeader=declaration("def C(V < UU0) : Unit := tt;");
  const c=child.parameters(cHeader.name,cHeader.params);
  const correspondence=new Map([[p.tree.params[0].name.bindingId,c.tree.params[0].name.bindingId]]);
  const inheritedCarrier=child.inherit(carrier,correspondence,{label:"Carrier"});
  correspondence.set(carrier.id,inheritedCarrier.id);
  child.retain(declaration("def x : Carrier := tt;"),{kind:"operation"});
  const inheritedHelper=child.inherit(helper,correspondence);
  const original=helper.syntax.tree.params[0].name.bindingId;
  const replacement=inheritedHelper.syntax.tree.params[0].name.bindingId;
  assert.notEqual(original,replacement);
  assert.equal(inheritedHelper.syntax.tree.body[0].value.resolution.id,replacement);
  assert.equal(inheritedHelper.syntax.tree.params[0].type.resolution.id,inheritedCarrier.id);
  assert.equal(inheritedHelper.syntax.tree.params[0].type,inheritedHelper.syntax.tree.params[1].type);
  assert.equal(options.table.get(replacement).origin.module,"parent");
  assert.deepEqual(bindingUses(interfaceSignature(inheritedHelper)).filter(use=>use.kind==="binding").map(use=>use.id),
    [inheritedCarrier.id,inheritedCarrier.id]);
  const count=options.table.snapshot().bindings.length;
  assert.equal(sameBindingSyntax(interfaceSignature(helper),interfaceSignature(inheritedHelper),correspondence),true);
  assert.equal(options.table.snapshot().bindings.length,count,"comparison does not clone or allocate");
});

test("diamond sharing compares instantiated signatures before assigning one child identity",()=>{
  const options=setup(),root=new RetainedInterfaces(options);
  const header=declaration("def Root(U < UU0, A : U) : Unit := tt;");
  const r=root.parameters(header.name,header.params);
  const member=root.retain(declaration("def point(x : A) : A := x;"),{kind:"operation"});
  const branches=["left","right"].map(label=>{
    const branch=new RetainedInterfaces({...options,owner:[label]});
    const h=branch.parameters(header.name,header.params),map=new Map(r.tree.params.map((p,k)=>[p.name.bindingId,h.tree.params[k].name.bindingId]));
    return {entry:branch.inherit(member,map),header:h};
  });
  const child=new RetainedInterfaces({...options,owner:["child"]}),h=child.parameters(header.name,header.params);
  const candidates=branches.map(({entry,header})=>({entry,correspondence:new Map(header.tree.params.map((p,k)=>[p.name.bindingId,h.tree.params[k].name.bindingId]))}));
  const shared=child.inheritShared(candidates);
  assert.equal(child.entries.length,1);
  for(const candidate of candidates)assert.equal(candidate.correspondence.get(candidate.entry.id),shared.id);
  assert.equal(shared.binding.original,member.id);
  assert.notEqual(shared.syntax.tree.params[0].name.bindingId,branches[0].entry.syntax.tree.params[0].name.bindingId);

  // The same ancestor at two different actual arguments is not a diamond
  // sharing certificate, even if every printed field/type label is equal.
  const other=new RetainedInterfaces({...options,owner:["other"]});
  const o=other.parameters(header.name,header.params);
  const conflicting=branches.map(({entry,header},k)=>({entry,correspondence:new Map(header.tree.params.map((p,j)=>
    [p.name.bindingId,(k?o:h).tree.params[j].name.bindingId]))}));
  const count=options.table.snapshot().bindings.length;
  assert.throws(()=>other.inheritShared(conflicting),/different origins, kinds or instantiated types/);
  assert.equal(options.table.snapshot().bindings.length,count,"a rejected comparison allocates no clones");
  assert.equal(other.entries.length,0);
});

test("independent carriers share by kind and alpha-equivalence, while operations remain distinct",()=>{
  const options=setup();
  const parent=(label,parameter,kind="sort",level="set")=>{
    const interfaces=new RetainedInterfaces({...options,owner:[label]});
    const h=declaration("def T(U < UU0) : Unit := tt;");
    const header=interfaces.parameters(h.name,h.params);
    const entry=interfaces.retain({...declaration(`def F(${parameter} : Unit) : U := Unit;`),level},{kind});
    return {header,entry};
  };
  const child=new RetainedInterfaces({...options,owner:["child"]});
  const h=declaration("def C(V < UU0) : Unit := tt;"),header=child.parameters(h.name,h.params);
  const candidates=parents=>parents.map(({entry,header:h})=>({entry,correspondence:new Map([[h.tree.params[0].name.bindingId,header.tree.params[0].name.bindingId]])}));
  const shared=child.inheritShared(candidates([parent("p","x"),parent("q","y")]),{label:"Family"});
  assert.equal(shared.label,"Family");
  for(const parents of [[parent("a","x","operation"),parent("b","x","operation")],
    [parent("s","x"),parent("t","x","sort","prop")]]) {
    const before=options.table.snapshot().bindings.length;
    assert.throws(()=>child.inheritShared(candidates(parents)),/different origins, kinds or instantiated types/);
    assert.equal(options.table.snapshot().bindings.length,before);
  }
});

test("a common helper origin cannot hide different instantiated values behind an equal signature",()=>{
  const options=setup(),parent=new RetainedInterfaces(options);
  const field=parent.retain(declaration("def c : Unit := tt;"),{kind:"operation"});
  const helper=parent.retain(declaration("def get : Unit := c;"),{kind:"derived"});
  const branches=["left","right"].map(label=>{
    const branch=new RetainedInterfaces({...options,owner:[label]});
    const own=branch.inherit(field,new Map());
    return {entry:branch.inherit(helper,new Map([[field.id,own.id]])),field:own};
  });
  const child=new RetainedInterfaces({...options,owner:["child"]});
  assert.throws(()=>child.inheritShared(branches.map(({entry})=>({entry,correspondence:new Map()}))),
    /different origins, kinds or instantiated types/);
  const unified=child.inherit(field,new Map());
  const shared=child.inheritShared(branches.map(({entry,field})=>({entry,correspondence:new Map([[field.id,unified.id]])})));
  assert.equal(shared.syntax.tree.body[0].value.resolution.id,unified.id);
});
