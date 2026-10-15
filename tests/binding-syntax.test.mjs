import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {rewritten,relocated} from "../web/cubist/scopes.mjs";
import {qualifySource,syntaxValue} from "../web/cubist/source-syntax.mjs";
import {BindingTable, BindingAdapter, LexicalContext, SlotOutcomes, sourceOrigin, bindingResolution, reservedResolution} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax, cloneBindingSyntax, substituteBindingSyntax, lowerBindingSyntax,sameBindingSyntax,remapBindingSyntax} from "../web/cubist/binding-syntax.mjs";

const reserved = ["U0", "UU0", "Unit", "tt", "typed", "Interval"];
const prepare = () => {
  const table = new BindingTable("compilation");
  const context = new LexicalContext(reserved.map(name => [name, reservedResolution(name)]));
  return {table, context, adapter: new BindingAdapter(table, {reserved}), source: {revision: "source-1", module: "main"}, owner: ["declaration", "0"]};
};
const expression = source => parse(source, true);
const uses = tree => {
  const found = [];
  rewritten(tree, n => {if (n.kind === "bindingReference") found.push(n); return n;});
  return found;
};

test("binding comparison uses local alpha-equivalence and explicit external correspondence",()=>{
  const setup=prepare(),resolve=(text,owner)=>resolveBindingSyntax(expression(text),{...setup,owner:[owner]});
  const left=resolve("fun (A : U0) => fun (x : A) => x","left");
  const right=resolve("fun (B : U0) => fun (y : B) => y","right");
  assert.equal(sameBindingSyntax(left,right),true);
  assert.equal(sameBindingSyntax(left,cloneBindingSyntax(left,setup.table,["clone"]).syntax),true);
  assert.equal(sameBindingSyntax(left,resolve("fun (A : U0) => fun (x : A) => A","different")),false);
  const origin=sourceOrigin({...setup.source,start:0,end:1});
  const a=setup.table.allocate(["parent-a"],{role:"field",label:"M",origin});
  const b=setup.table.allocate(["parent-b"],{role:"field",label:"M",origin});
  const field=record=>resolveBindingSyntax(expression("fun (x : M) => x"),{...setup,
    owner:[record.id],context:setup.context.bind("M",bindingResolution(record.id))});
  assert.equal(sameBindingSyntax(field(a),field(b)),false,"same labels cannot merge different fields");
  assert.equal(sameBindingSyntax(field(a),field(b),new Map([[a.id,b.id]])),true);
  assert.equal(sameBindingSyntax(left,JSON.parse(JSON.stringify(right))),true);
});

test("binding comparison retains reserved, missing and pending-constructor identities",()=>{
  const setup=prepare();
  const context=new LexicalContext(["Unit","Void","tt","refl","U0","U1"].map(label=>[label,reservedResolution(label)]));
  let serial=0;
  const resolve=text=>resolveBindingSyntax(expression(text),{...setup,context,owner:[String(serial++)]});
  for(const [a,b] of [["Unit","Void"],["U0","U1"],["tt = tt","refl = refl"],
    ["fun (x : Unit) => x","fun (y : U0) => y"],["missing_a","missing_b"]])
    assert.equal(sameBindingSyntax(resolve(a),resolve(b)),false,`${a} versus ${b}`);
  const a=resolve("match tt { x => x; }");
  const b=resolveBindingSyntax(expression("match tt { x => x; }"),{...setup,
    context:context.bind("x",reservedResolution("Unit")),owner:["other"]});
  assert.equal(sameBindingSyntax(a,b),false,"a pending slot's enclosing resolution is semantic");
});

test("open ID remapping cannot capture a local in either direction",()=>{
  const setup=prepare(),origin=sourceOrigin({...setup.source,start:0,end:1});
  const c=setup.table.allocate(["field"],{role:"field",label:"c",origin});
  const syntax=resolveBindingSyntax(expression("fun (x : Unit) => c"),{...setup,
    context:setup.context.bind("c",bindingResolution(c.id))});
  const local=syntax.tree.name.bindingId;
  for(const pair of [[c.id,local],[local,c.id]])
    assert.throws(()=>remapBindingSyntax(syntax,setup.table,new Map([pair])),/local binders/);
  const clone=cloneBindingSyntax(syntax,setup.table,["fresh"]).syntax;
  assert.notEqual(clone.tree.name.bindingId,local);
  assert.equal(clone.tree.body.resolution.id,c.id);
});

test("grouped domains precede every own binder and subsequent groups use the complete telescope", () => {
  const setup = prepare();
  const declaration = parse("def f(U < UU0, A : U, x, y : A, p : x = y) : A := x;").declarations[0];
  const syntax = resolveBindingSyntax(declaration, setup), {params, type, body} = syntax.tree;
  const [u, a, x, y, p] = params.map(param => param.name.bindingId);
  assert.equal(new Set([u, a, x, y, p]).size, 5);
  assert.equal(params[1].type.resolution.id, u);
  assert.equal(params[2].type.resolution.id, a);
  assert.equal(params[3].type.resolution.id, a);
  assert.deepEqual(uses(params[4].type).map(n => n.resolution.id), [x, y]);
  assert.equal(type.resolution.id, a);
  assert.equal(body[0].value.resolution.id, x);
  // Even a same-spelled first binder in a group cannot bind its domain.
  const grouped = resolveBindingSyntax(expression("fun (A : U0) => fun (A, x : A) => x"), {...setup, owner: ["declaration", "1"]});
  const outer = grouped.tree.name.bindingId, inner = grouped.tree.body;
  assert.equal(inner.domain.resolution.id, outer);
  assert.notEqual(inner.names[0].bindingId, outer);
  assert.equal(inner.body.resolution.id, inner.names[1].bindingId);
});

test("inferred headers and parameter lambdas share identities and retain named argument labels", () => {
  const setup = prepare();
  const declaration = parse("def f{{U < UU0, A : U}}(x, y : A) := x;").declarations[0];
  const syntax = resolveBindingSyntax(declaration, setup);
  assert.equal(syntax.owned.length, 4);
  const lowered = lowerBindingSyntax(syntax, setup.adapter);
  assert.deepEqual(lowered.valueParameters.map(p => p.name.label), ["U", "A", "x", "y"]);
  assert.equal(lowered.value.name, lowered.valueParameters[0].name);
  assert.equal(lowered.value.body.name, lowered.valueParameters[1].name);
  assert.equal(lowered.value.body.body.names[0], lowered.valueParameters[2].name);
  assert.equal(lowered.value.body.body.body.name, lowered.valueParameters[2].name.text);
  assert.deepEqual(lowered.valueParameters.map(p => !!p.implicit), [true, true, false, false]);
});

test("anonymous binder positions have distinct owned IDs without binding source holes",()=>{
  const setup=prepare();
  const syntax=resolveBindingSyntax(parse("def f(_, _ : Unit, x : Unit) : Unit := _;").declarations[0],setup);
  const ids=syntax.tree.params.map(p=>p.name.bindingId);
  assert.equal(new Set(ids).size,3);
  for(const id of ids)assert.ok(syntax.owned.includes(id));
  assert.deepEqual(ids.map(id=>setup.table.get(id).label),["_","_","x"]);
  assert.equal(syntax.tree.body[0].value.kind,"name");
  assert.equal(syntax.tree.body[0].value.name,"_");
  const lowered=lowerBindingSyntax(syntax,setup.adapter);
  assert.notEqual(lowered.params[0].name.text,lowered.params[1].name.text);
  assert.equal(lowered.params[0].name.label,"_");
  assert.equal(lowered.body[0].value.name,"_");
  const cloned=cloneBindingSyntax(syntax,setup.table,["anonymous-clone"]).syntax;
  assert.ok(cloned.owned.every(id=>!syntax.owned.includes(id)));
  assert.equal(sameBindingSyntax(syntax,cloned),true);
  assert.equal(sameBindingSyntax(
    resolveBindingSyntax(expression("fun (_ : Unit) => tt"),{...setup,owner:["anonymous"]}),
    resolveBindingSyntax(expression("fun (x : Unit) => tt"),{...setup,owner:["unused"]})),true);
});

test("a grouped domain is one scoped region even when it contains binders",()=>{
  const setup=prepare();
  const syntax=resolveBindingSyntax(parse("def f(a, b : (fun (n : Unit) => Unit)(tt)) : Unit := a;").declarations[0],setup);
  assert.deepEqual(syntax.owned.map(id=>setup.table.get(id).label),["a","b","n"]);
  assert.equal(syntax.tree.params[0].type,syntax.tree.params[1].type);
  const cloned=cloneBindingSyntax(syntax,setup.table,["clone"]).syntax;
  assert.equal(cloned.owned.length,3);
  assert.equal(cloned.tree.params[0].type,cloned.tree.params[1].type);
  const lowered=lowerBindingSyntax(cloned,setup.adapter);
  assert.equal(lowered.params[0].type,lowered.params[1].type);
  const malformed=parse("def f(a, b : Unit) : Unit := a;").declarations[0];
  malformed.params[1].type=expression("U0");
  assert.throws(()=>resolveBindingSyntax(malformed,prepare()),/Grouped parameters must share one domain/);
});

test("unmigrated reference namespaces and new syntax families are refused at source resolution",()=>{
  const setup=prepare();
  for(const source of [
    "def a(x : Unit) : Unit { simpa with [x] using x; }",
    "def a(x : Unit) : Unit { simpa without [r] using x; }",
    "def a(x : Unit) : Unit { simpa only [rules] using x; }",
  ])assert.throws(()=>resolveBindingSyntax(parse(source).declarations[0],setup),/family has not migrated: simpaOnly/);
  assert.throws(()=>resolveBindingSyntax({kind:"futureFamily"},setup),/family has not migrated: futureFamily/);
  for(const source of ["tt + tt","tt * tt","tt < tt","tt <= tt","-tt","0b10"])
    assert.throws(()=>resolveBindingSyntax(expression(source),setup),error=>/selected notation/.test(error.message)&&Number.isInteger(error.offset)&&error.sourceEnd>error.offset);
  assert.throws(()=>resolveBindingSyntax(expression("tt pl.(+) tt"),setup),/complete source notation inventory/);
});

test("authored provenance is opaque to rewriting, relocation and structural comparison",()=>{
  const source="fun (x : Unit) => x";
  const tree=qualifySource(expression(source),{revision:"dep-revision",module:"dep"});
  const shifted=relocated(tree,{start:100,end:120,synthetic:true});
  assert.equal(shifted.origin,tree.origin);
  assert.equal(shifted.body.origin,tree.body.origin);
  assert.equal(shifted.body.start,100);
  const other=qualifySource(expression(source),{revision:"other-revision",module:"other"});
  assert.equal(syntaxValue(tree),syntaxValue(other));
  const seen=[];rewritten(tree,node=>{if(node.kind)seen.push(node.kind);return node;});
  assert.deepEqual(seen,["lambda","name","name"]);
});

test("cloning freshens binders and their uses without allocating when syntax is revisited or serialized", () => {
  const setup = prepare();
  const outer = setup.table.allocate(["import"], {role: "declaration", label: "x",
    origin: sourceOrigin({revision: "import-1", module: "dependency", start: 3, end: 4})});
  setup.context = setup.context.bind("outer", bindingResolution(outer.id));
  const syntax = resolveBindingSyntax(expression("fun (x : Unit) => (x, outer)"), setup);
  const before = setup.table.snapshot();
  rewritten(syntax.tree, n => n); lowerBindingSyntax(syntax, setup.adapter);
  assert.deepEqual(setup.table.snapshot(), before);
  const {syntax: cloned, correspondence} = cloneBindingSyntax(syntax, setup.table, ["instance", "0"]);
  assert.equal(cloned.tree.name.bindingId, correspondence.get(syntax.tree.name.bindingId));
  assert.deepEqual(uses(cloned.tree).map(n => n.resolution).filter(r => r.tag === "binding").map(r => r.id),
    [cloned.tree.name.bindingId, outer.id]);
  const restored = BindingTable.restore(JSON.parse(JSON.stringify(setup.table.snapshot())));
  assert.deepEqual(lowerBindingSyntax(JSON.parse(JSON.stringify(cloned)), new BindingAdapter(restored, {reserved})),
    lowerBindingSyntax(cloned, setup.adapter));
});

test("a bare pattern retains its enclosing resolution until its role is decided", () => {
  const setup = prepare();
  const syntax = resolveBindingSyntax(expression("fun (x : Unit) => match x { x => x; }"), setup);
  const outer = syntax.tree.name.bindingId, clause = syntax.tree.body.clauses[0];
  const slot = clause.constructor.bindingId;
  assert.equal(clause.body.resolution.tag, "slot");
  assert.equal(clause.body.resolution.id, slot);
  assert.equal(clause.body.resolution.enclosing.id, outer);
  const pending = lowerBindingSyntax(syntax, setup.adapter);
  assert.equal(pending.body.clauses[0].body.kind, "bindingReference");
  assert.equal(pending.body.clauses[0].constructor.text, "x");
  const variable = lowerBindingSyntax(syntax, setup.adapter, new SlotOutcomes().decide(slot, "variable"));
  const constructor = lowerBindingSyntax(syntax, setup.adapter, new SlotOutcomes().decide(slot, "constructor"));
  assert.equal(variable.body.clauses[0].body.name, setup.adapter.key(slot));
  assert.equal(constructor.body.clauses[0].body.name, setup.adapter.key(outer));
});

test("qualified occurrences retain receiver shadowing and source ownership", () => {
  const setup = prepare(), at = sourceOrigin({...setup.source, start: 0, end: 1});
  const field = setup.table.allocate(["global"], {role: "declaration", label: "T.f", origin: at});
  setup.context = setup.context.bind("T.f", bindingResolution(field.id));
  const syntax = resolveBindingSyntax(expression("fun (T : Unit) => T.f"), setup);
  assert.equal(syntax.tree.body.kind, "member");
  assert.equal(syntax.tree.body.field.text, "f");
  assert.equal(syntax.tree.body.value.resolution.id, syntax.tree.name.bindingId);
  assert.equal(syntax.tree.body.value.origin.module, "main");
  const global = resolveBindingSyntax(expression("T.f"), {...setup, owner: ["second"]});
  assert.equal(global.tree.resolution.id, field.id);
});

test("ordinary term, universe and dimension binders elaborate and kernel-check through the shared adapter", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "");
  t.after(() => program.dispose());
  const translator = new Translator({checker: program.checker, normalize: false});
  for (const [index, source] of [
    "fun (U < UU0) => fun (A : U) => fun (x, y : A) => x",
    "fun (p : tt = tt) => typed(tt = tt, path i => p @ i)",
  ].entries()) {
    const setup = prepare();
    const syntax = resolveBindingSyntax(expression(source), {...setup, owner: ["expression", String(index)]});
    const scope = new Scope(translator.unit({source,bindingAdapter:setup.adapter}));
    const term = translator.term(lowerBindingSyntax(syntax, setup.adapter), scope);
    assert.ok(scope.infer(term).type);
    const {syntax: cloned} = cloneBindingSyntax(syntax, setup.table, ["clone", String(index)]);
    const copied = translator.term(lowerBindingSyntax(cloned, setup.adapter), scope);
    assert.equal(scope.equal(term, copied), true);
    if (source.includes("path i")) assert.ok(syntax.owned.some(id => setup.table.get(id).role === "dimension"));
  }
});

test("the pattern compiler resolves slots at the matched type, including nested candidates and saved missing lookups", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "");
  t.after(() => program.dispose());
  const result = await program.check("inductive Two { left_; right_; }\ninductive Box { box(value : Two); }\ndef first : Two := left_;\ninductive Unrelated { late_; }", "base");
  assert.deepEqual(result.gaps, []);
  const globals = program.modules.get("base"), setup = prepare(), env = new Map(globals);
  setup.constructors = [];
  for (const [label, value] of globals) {
    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(label) || ["Unrelated", "late_"].includes(label)) continue;
    const record = setup.table.allocate(["import"], {role: "declaration", label,
      origin: sourceOrigin({revision: "base-1", module: "base", start: 0, end: 1})});
    setup.context = setup.context.bind(label, bindingResolution(record.id));
    env.set(setup.adapter.key(record.id), value);
    if (value.tag === "InductiveConstructor") setup.constructors.push({id: record.id, label, nullary: !value.arity && !value.dims});
  }
  const translator = new Translator({checker: program.checker, normalize: false});
  let serial = 0;
  const resolve = (source, context = setup.context) => resolveBindingSyntax(expression(source), {...setup, context, owner: ["pilot", String(serial++)]});
  const elaborateSyntax = (syntax, source = "") => {
    const scope = new Scope(translator.unit({source, bindingAdapter: setup.adapter}), new Map(), env);
    const term = translator.term(lowerBindingSyntax(syntax, setup.adapter), scope);
    scope.infer(term);
    return {term, scope};
  };
  const elaborate = (source, context = setup.context) => elaborateSyntax(resolve(source, context), source);
  // Historical mode cannot turn literal data into an invented destination
  // reference. Interval endpoints still bypass term elaboration normally.
  translator.nameBased=true;
  assert.throws(()=>elaborate("1"),/selected notation that reads it/);
  translator.nameBased=false;
  const left = elaborate("left_").term, right = elaborate("right_").term;
  for (const [source, expected, refused] of [
    ["(fun (left_ : Two) => match first return Two { left_ => left_; right_ => right_; })(right_)", right, left],
    ["(fun (x : Two) => match first return Two { x => x; })(right_)", left, right],
    ["(fun (left_ : Two) => match box(first) return Two { box(left_) => left_; box(right_) => right_; })(right_)", right, left],
  ]) {
    const {term, scope} = elaborate(source);
    assert.equal(scope.equal(term, expected), true, source);
    assert.equal(scope.equal(term, refused), false, source);
  }
  // This constructor exists only in the destination. At the source, the
  // bare pattern is a variable; Unit has no declared constructor table.
  const late = elaborate("match tt, tt { late_, _ => late_; }");
  assert.equal(late.scope.equal(late.term, elaborate("tt").term), true);
  const missing = new LexicalContext(setup.context.snapshot().filter(([label]) => label !== "left_"));
  assert.throws(() => elaborate("match first return Two { left_ => left_; right_ => right_; }", missing), /Untranslated name: left_/);

  const open = setup.table.allocate(["interface"], {role: "parameter", label: "argument",
    origin: sourceOrigin({...setup.source, start: 0, end: 1})});
  const context = setup.context.bind("argument", bindingResolution(open.id));
  const under = resolve("fun (x : Two) => match first return Two { x => argument; }", context);
  const argument = resolve("x", setup.context.bind("x", bindingResolution(under.tree.name.bindingId)));
  const replaced = substituteBindingSyntax(under, new Map([[open.id, argument]]), setup.table, ["substitution", "0"]);
  for (const syntax of [replaced, cloneBindingSyntax(replaced, setup.table, ["substitution", "copy"]).syntax]) {
    const value = elaborateSyntax(syntax);
    assert.equal(value.scope.equal(value.term, elaborate("fun (x : Two) => x").term), true);
    assert.equal(value.scope.equal(value.term, elaborate("fun (x : Two) => first").term), false);
  }
  // A substitution of the saved enclosing alternative must wait for the
  // slot. Constructor interpretation uses it; variable interpretation does
  // not. Both are checked independently by their resulting computations.
  for (const [label, expected, refused] of [["left_", right, left], ["field", left, right]]) {
    const context = setup.context.bind(label, bindingResolution(open.id));
    const source = label === "left_" ? "match first return Two { left_ => left_; right_ => right_; }"
      : "match first return Two { field => field; }";
    const pending = substituteBindingSyntax(resolve(source, context), new Map([[open.id, resolve("right_")]]), setup.table, ["fallback", label]);
    const value = elaborateSyntax(pending);
    assert.equal(value.scope.equal(value.term, expected), true);
    assert.equal(value.scope.equal(value.term, refused), false);
  }
});

test("source resolution preserves overlapping scopes and disjoint branches",()=>{
  const setup=prepare(),resolve=source=>resolveBindingSyntax(expression(source),setup).tree;
  const induction=resolve("induction n as z return Unit { zero => a; succ z => z; }");
  assert.notEqual(induction.index.bindingId,induction.hypothesis.bindingId);
  assert.equal(induction.step.resolution.id,induction.hypothesis.bindingId);
  const match=resolve("match s return Unit { left x => x; right y => x; }");
  assert.equal(match.leftBody.resolution.id,match.left.bindingId);
  assert.deepEqual(match.rightBody.resolution,{tag:"missing",label:"x"});
  const unpack=resolve("unpack x as (x, y) return Unit { x; }");
  assert.deepEqual(unpack.value.resolution,{tag:"missing",label:"x"});
  assert.equal(unpack.body.resolution.id,unpack.left.bindingId);
  const path=resolve("path i => p @ i");
  assert.equal(path.body.right.resolution.id,path.dimension.bindingId);
  const clauses=resolve("match c { base => p @ i; loop @ i => p @ i; }");
  assert.deepEqual(clauses.clauses[0].body.right.resolution,{tag:"missing",label:"i"});
  assert.equal(clauses.clauses[1].body.right.resolution.id,clauses.clauses[1].coordinates[0].bindingId);
});

test("unread numeral diagnostics do not change interval binding structure",()=>{
  const setup=prepare(),context=setup.context.withNotations([]).namespace("p",[],"P").namespace("q",[],"P");
  const resolve=label=>resolveBindingSyntax(expression(`${label}.(path i => r @ 0)`),
    {...setup,context,owner:[label]});
  assert.ok(sameBindingSyntax(resolve("p"),resolve("q")));
});
