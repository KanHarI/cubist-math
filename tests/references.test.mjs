import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {reference} from "../web/cubist/artifact-builder.mjs";
import {rewritten, freeNames, relocated} from "../web/cubist/scopes.mjs";
import {BindingTable,BindingAdapter,LexicalContext,bindingResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,lowerBindingSyntax} from "../web/cubist/binding-syntax.mjs";

const resolved=(tree,labels)=>{
  const table=new BindingTable("reference-tests"),source={revision:table.revision,module:"main"};
  const context=new LexicalContext(labels.map(label=>{
    const binding=table.allocate(["declarations"],{role:"declaration",label,origin:sourceOrigin({...source,start:0,end:1})});
    return [label,bindingResolution(binding.id)];
  }));
  return resolveBindingSyntax(tree,{table,context,source,owner:["source"]}).tree;
};

const expression = source => parse(`def result := ${source};`).declarations[0].value;
const refs = node => {
  const found = [];
  rewritten(node, n => {if (n.kind === "bindingReference") found.push(n.resolution.id); return n;});
  return found;
};

test("declaration references survive traversals, relocation and serialization", () => {
  const table=new BindingTable("traversal"),binding=table.allocate(["g"],{role:"declaration",label:"g",
    origin:sourceOrigin({revision:table.revision,module:"main",start:0,end:1})});
  const captured = rewritten(expression("g(x)"),node=>node.kind==="name"&&node.name==="g"
    ?reference(binding):node);
  const identities = refs(captured);
  assert.equal(identities.length, 1);
  assert.deepEqual([...freeNames(captured)], ["x"]);
  for (const spelling of ["g", "x", "T", "__theory_type_0"]) {
    const renamed = rewritten(captured,n=>n.kind==="name"?{...n,name:spelling}:n);
    assert.deepEqual(refs(renamed), identities);
    assert.deepEqual(refs(relocated(renamed, {start: 100, end: 101, synthetic: true})), identities);
    assert.deepEqual(refs(JSON.parse(JSON.stringify(renamed))), identities);
  }
});

test("local and captured receivers have structural field selections", () => {
  const local = resolved(expression("fun (T : Unit) => T.M"),["T"]);
  assert.equal(local.body.kind, "member");
  assert.equal(local.body.value.resolution.id,local.name.bindingId);
  assert.equal(local.body.field.text, "M");
  assert.ok(refs(local).includes(local.name.bindingId));
  const global = resolved(expression("T.parent.M"),["T"]);
  assert.equal(global.kind, "member");
  assert.equal(global.value.kind, "member");
  assert.equal(global.value.value.kind, "bindingReference");
  assert.equal(global.value.value.resolution.tag,"binding");
  assert.deepEqual([...freeNames(global)], []);
});

test("lowering binding syntax leaves its retained declaration unchanged", () => {
  const table=new BindingTable("lowering"),source={revision:table.revision,module:"main"};
  const binding=table.allocate(["f"],{role:"declaration",label:"f",origin:sourceOrigin({...source,start:0,end:1})});
  const context=new LexicalContext([["f",bindingResolution(binding.id)]]);
  const syntax=resolveBindingSyntax(expression("f"),{table,context,source,owner:["use"]});
  const adapter=new BindingAdapter(table),before=JSON.stringify(syntax);
  const lowered=lowerBindingSyntax(syntax,adapter);
  assert.equal(lowered.kind,"name");
  assert.equal(lowered.name,adapter.key(binding.id));
  assert.equal(lowered.spelling,"f");
  assert.equal(JSON.stringify(syntax),before);
  assert.equal(syntax.tree.kind,"bindingReference");
});

test("a captured syntax closure is opaque to caller traversal and relocation", () => {
  const closure = {kind: "scoped", node: expression("x"), scope: {env: new Map([["x", "original"]])}, start: 0, end: 1};
  const result = rewritten(closure,n=>n.kind==="name"?expression("wrong"):n);
  assert.equal(result.node, closure.node);
  assert.equal(result.scope, closure.scope);
  assert.equal(relocated(closure, {start: 20, end: 21}).node, closure.node);
  assert.deepEqual([...freeNames(closure)], []);
});

test("parameter telescopes expose only earlier groups, and never their own shared domain", () => {
  const declaration = parse("def f(A, x : A, y : x) : Unit := tt;").declarations[0];
  assert.deepEqual([...freeNames(declaration)].sort(), ["A", "Unit", "tt"]);
  const captured = resolved(declaration,["A"]);
  assert.equal(captured.params[0].type.kind, "bindingReference");
  assert.equal(captured.params[0].type,captured.params[1].type);
  assert.notEqual(captured.params[0].type.resolution.id,captured.params[0].name.bindingId);
  assert.equal(captured.params[2].type.resolution.id,captured.params[1].name.bindingId);
});

test("new syntax cannot silently opt out of scope checking", () => {
  assert.throws(() => freeNames({kind: "unregisteredBinder", body: expression("x")}), /Unregistered syntax kind/);
});

test("sequential statement binders scope their continuation", () => {
  for (const statement of ["let x := tt;", "obtain (x, z) := pair;", "intro x;", "ext x;", "simp only [] at h as x;"]) {
    const node = parse(`def f : Unit { ${statement} exact x; }`).declarations[0];
    assert.ok(!freeNames(node).has("x"), statement);
  }
});

test("a statement scopes its continuation but not its initializer", () => {
  const node = parse("def f : Unit { let x := x; exact x; }").declarations[0];
  assert.ok(freeNames(node).has("x"));
  const retained=resolved(node,["x"]),[binding,use]=retained.body;
  assert.notEqual(binding.value.resolution.id,binding.target.bindingId);
  assert.equal(use.value.resolution.id,binding.target.bindingId);
});
