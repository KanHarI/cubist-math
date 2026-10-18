import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {sourceBindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {notationBinding} from "../web/translator/theories.mjs";
import {retainSourceNotation} from "../web/translator/named-notation.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {resolveBindingSyntax,cloneBindingSyntax,sameBindingSyntax,bindingUses} from "../web/cubist/binding-syntax.mjs";
import {sourceOrigin} from "../web/cubist/bindings.mjs";
import {activateSourceItem,withSourceCaptures} from "../web/translator/retained-source-context.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";

const wasm=await create();
const failures=result=>result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]);
async function setup(t) {
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  const base=await program.check(`import hlevels; import lexemes;
    inductive Two : set U0 { left_; right_; }
    def source_value : Two := left_;
    def first(a, b : Two) : Two := a;
    def Natural : U0 := UNat;
    theory Reader(U < UU0) { M : U; read(n : UNat) : M; def numeral_(n : UNat) : M := read(n) notation numeral; }
    def plain : Reader(U0) := Reader.make(UNat, fun (n : UNat) => n);
    def raised : Reader(U0) := Reader.make(UNat, fun (n : UNat) => succ(n));
    theory ReaderBox(U < UU0) { anchor : Unit; plain : Reader(U); }
    def box : ReaderBox(U0) := ReaderBox.make(tt, raised);
  `,"base");
  assert.deepEqual(base.gaps,[],JSON.stringify(base.gaps));
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base");
  const inputs=sourceBindingInputs(registry,env,{reserved:reservedReferences("U0 UU0 Unit tt refl")});
  const checker=program.checker,definitionModule="named";
  const translator=new Translator({checker,definitionModule,normalize:false,moduleName:"client",compilationBindings:registry});
  const scope=new Scope(translator.unit(),new Map(),new Map([...env,...inputs.env]));
  let current=new Map([...env,...inputs.env]),serial=0;
  const source={revision:registry.revision,module:"recipe_source"};
  const prepare=text=>{
    const parsed=parse(text),item=(parsed.items??parsed.declarations).at(-1),owner=["source",String(serial++)];
    const inputs=sourceBindingInputs(registry,current,{reserved:reservedReferences(text)});
    const prepared=activateSourceItem(translator,new Scope(translator.unit({source:text}),new Map(),current),
      item,inputs,{owner,source});
    const env=withSourceCaptures(new Map([...current,...inputs.env]),prepared,inputs.adapter);
    return {prepared,env,options:{table,owner,source,context:prepared.context,constructors:inputs.constructors}};
  };
  const retain=(text,{declared=new Set()}={})=>{
    const entry=retainSourceNotation(translator,translator.unit({source:text,moduleName:"recipe_source"}),parse(text).items.at(-1),current,
      {declared,owner:["notation",String(serial++)]});
    const {artifact,prepared}=entry;
    const result=translator.translateSyntax({items:[entry.declaration],declarations:[]},text,entry.env);
    assert.deepEqual(result.directives,[]);
    current=result.env;
    return {artifact,receipt:current.get(notationBinding(artifact.binding.label)),prepared,env:current};
  };
  const retainDeclaration=text=>{
    const {prepared,env,options}=prepare(text),d=prepared.item;
    const binding=table.allocate([...options.owner,"header"],{role:"declaration",label:d.name.text,
      origin:sourceOrigin({...source,start:d.name.start,end:d.name.end})});
    const syntax=resolveBindingSyntax(d,options);
    current=env;
    return {binding,syntax,env,prepared};
  };
  const check=(source,{retained=[],env=current}={})=>{
    const parsed=parse(source);
    const result=translator.translateSyntax({...parsed,items:[...(parsed.items??parsed.declarations),
      ...retained.map(({binding,syntax})=>bindingDeclaration(binding,syntax))]},source,env);
    const here=new Scope(translator.unit(),new Map(),result.env);
    return {result,equal:(label,expected)=>here.equal(result.env.get(label),translator.term(parse(expected,true),here))};
  };
  return {retain,retainDeclaration,check,table,translator,scope};
}

test("named rule operands retain caller scope, laziness and fresh rule-local identities",async t=>{
  const {retain,check,table}=await setup(t);
  const {artifact}=retain(`notation captured {
    x + y := (fun (x : Two) => y)(left_);
    -x := source_value;
    x * y := match y { left_ => x; right_ => source_value; };
  }`);
  const snapshot=JSON.stringify(artifact);
  assert.doesNotThrow(()=>snapshotSyntax(artifact));
  for(const rule of artifact.rules) {
    const clone=cloneBindingSyntax(rule.syntax,table,["clone",rule.key]);
    assert.equal(sameBindingSyntax(rule.syntax,clone.syntax),true);
    assert.ok(clone.syntax.owned.every(id=>!rule.syntax.owned.includes(id)));
    assert.ok(bindingUses(rule.syntax).every(use=>!rule.syntax.owned.includes(use.id)));
  }
  const {result,equal}=check(`
    def source_value : Two := right_;
    def caller(x : Two) : Two := captured.(left_ + x);
    def ignored : Two := captured.(absent + right_);
    def own_global : Two := captured.(-absent);
    def nested : Two := captured.((right_ + left_) + right_);
    def branch(x : Two) : Two := captured.(x * left_);
    def constant : Two := captured.(right_ * right_);
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("caller","fun (x : Two) => x"),true);
  assert.equal(equal("caller","fun (x : Two) => left_"),false);
  assert.equal(equal("branch","fun (x : Two) => x"),true);
  for(const label of ["ignored","nested"])assert.equal(equal(label,"right_"),true,label);
  for(const label of ["own_global","constant"]) {
    assert.equal(equal(label,"left_"),true,label);assert.equal(equal(label,"right_"),false,label);
  }
  assert.equal(JSON.stringify(artifact),snapshot);
});

test("a missing rule-source name stays missing despite a destination declaration",async t=>{
  const {retain,check}=await setup(t);
  retain("notation missing { x + y := unavailable; }");
  const {result}=check("def unavailable : Two := left_; def rejected : Two := missing.(left_ + right_);");
  assert.deepEqual(failures(result).map(([name])=>name),["rejected"]);
  assert.match(failures(result)[0][1],/Untranslated name: unavailable/);
});

test("named numeral and lexeme rules keep source readers while preserving ignored inputs",async t=>{
  const {retain,check}=await setup(t);
  retain("notation numeric { numeral(n : UNat) := succ(n); }");
  retain("notation ignored { numeral(n : UNat) := zero; }");
  retain("notation text_reader { literal(s : Lexeme) := natural_literal(s); }");
  const {result,equal}=check(`
    def UNat : U0 := Unit;
    def natural_literal(s : Lexeme) : Unit := tt;
    def numeric_value : Natural := numeric.(0);
    def ignored_value : Natural := ignored.(999);
    def text_value : Natural := text_reader.(12);
    def too_large : Natural := numeric.(999);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["too_large"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/limited to 256/);
  assert.equal(equal("numeric_value","succ(zero)"),true);
  assert.equal(equal("numeric_value","zero"),false);
  assert.equal(equal("ignored_value","zero"),true);
  assert.equal(equal("text_value",`${"succ(".repeat(12)}zero${")".repeat(12)}`),true);
});

test("named operand recipes capture source models independently of operand labels",async t=>{
  const {retain,check}=await setup(t);
  retain("notation power { x ^ plain.(n) := n; }");
  const {result,equal}=check(`
    def plain : Reader(U0) := raised;
    def value : UNat := power.(zero ^ 0);
    def caller(plain : Unit, n : UNat) : UNat := power.(zero ^ n);
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("value","zero"),true);assert.equal(equal("value","succ(zero)"),false);
  assert.equal(equal("caller","fun (plain : Unit) => fun (n : UNat) => n"),true);
});

test("retained named selections keep the exact receipt through block use, copying and destination shadowing",async t=>{
  const {retain,retainDeclaration,check,table,translator}=await setup(t);
  const {artifact}=retain("notation chosen { x + y := x; }");
  const declarations=[
    "def selected_value : Two := chosen.(left_ + right_);",
    "def block_value(x : Two) : Two { use chosen; exact x + right_; }",
    "def local_name(chosen : Unit) : Two := chosen.(left_ + right_);",
  ].map(retainDeclaration);
  assert.ok(bindingUses(declarations[0].syntax).some(use=>use.id===artifact.binding.id));
  const copied=cloneBindingSyntax(declarations[0].syntax,table,["selection-copy"]);
  assert.equal(sameBindingSyntax(declarations[0].syntax,copied.syntax),true);
  declarations[0]={...declarations[0],syntax:copied.syntax};
  const {result,equal}=check("notation chosen { x + y := y; }",{retained:declarations});
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("selected_value","left_"),true);assert.equal(equal("selected_value","right_"),false);
  assert.equal(equal("block_value","fun (x : Two) => x"),true);
  assert.equal(equal("local_name","fun (chosen : Unit) => left_"),true);
  const missing=new Map(declarations[0].env);missing.delete(translator.identityAdapter.key(artifact.binding.id));
  const refused=check("",{retained:[declarations[0]],env:missing});
  assert.match(failures(refused.result)[0]?.[1]??"",/exact source notation receipt/);
});

test("file-level named contexts preserve source rule selection and empty label openings",async t=>{
  const {retain,retainDeclaration,check}=await setup(t);
  retain("notation numeric { numeral(n : UNat) := succ(n); }");
  const {artifact,prepared}=retain("use numeric; notation wrapped { -x := 0; x + y := numeric.(0); }");
  assert.equal(prepared.captures.length,0,"a standalone notation has no term receiver");
  assert.equal(prepared.activations[0].members.length,0);
  assert.doesNotThrow(()=>snapshotSyntax({artifact,activations:prepared.activations,context:prepared.context.snapshot()}));
  const retained=[
    "use wrapped; def file_value : UNat := -absent;",
    "use wrapped; def nested_value : UNat := absent + absent;",
    "use wrapped; def fallback(source_value : Two) : Two := source_value;",
  ].map(retainDeclaration);
  const {result,equal}=check(`notation numeric { numeral(n : UNat) := n; }
    notation wrapped { -x := x; x + y := y; }`,{retained,env:retained.at(-1).env});
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["file_value","nested_value"]) {
    assert.equal(equal(name,"succ(zero)"),true,name);assert.equal(equal(name,"zero"),false,name);
  }
  assert.equal(equal("fallback","fun (source_value : Two) => source_value"),true);
});

test("attached rules follow model identity through deferred selections and source captures",async t=>{
  const {retain,retainDeclaration,check,table}=await setup(t);
  const declared=new Set(["plain"]);
  const first=retain("notation plain { numeral(n : UNat) := succ(succ(n)); }",{declared});
  const retained=[
    "def attached_value : UNat := plain.(0);",
    "def parameter_value(plain : Reader(U0)) : plain.M := plain.(0);",
    "def opened_value : UNat { use box; exact plain.(0); }",
    "use plain; def captured_first : UNat := 0;",
  ].map(retainDeclaration);
  const priorContext=retained.at(-1).prepared.activations[0].notation.id;
  assert.ok(bindingUses(retained[0].syntax).some(use=>use.id===first.artifact.binding.id));
  assert.ok(bindingUses(retained[0].syntax).some(use=>use.id===first.artifact.model));
  const cloned=cloneBindingSyntax(retained[0].syntax,table,["attached-copy"]);
  assert.equal(sameBindingSyntax(retained[0].syntax,cloned.syntax),true);
  retained[0]={...retained[0],syntax:cloned.syntax};
  retain("notation plain { numeral(n : UNat) := n; }",{declared});
  const later=retainDeclaration("use plain; def captured_second : UNat := 0;");
  assert.notEqual(later.prepared.activations[0].notation.id,priorContext,
    "a different rule extension changes the semantic context even on the same model");
  const {result,equal}=check("def plain : Reader(U0) := raised;",{retained:[...retained,later]});
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["attached_value","captured_first"]) {
    assert.equal(equal(name,"succ(succ(zero))"),true,name);assert.equal(equal(name,"zero"),false,name);
  }
  assert.equal(equal("captured_second","zero"),true);
  assert.equal(equal("opened_value","succ(zero)"),true);
  assert.equal(equal("opened_value","succ(succ(zero))"),false);
  assert.equal(equal("parameter_value","fun (plain : Reader(U0)) => plain.read(zero)"),true);
});

test("source retention enforces attachment ownership and preserves notation printing",async t=>{
  const {retain,translator}=await setup(t);
  assert.throws(()=>retain("notation plain { numeral(n : UNat) := n; }"),/declared in another module/);
  assert.throws(()=>retain("notation plain { x + y := x; }",{declared:new Set(["plain"])}),/adds only a numeral or a literal/);
  retain("notation printed { literal(s : Lexeme) := natural_literal(s); }");
  assert.ok([...translator.checker.notationPrinting.values()].flat().some(entry=>entry.notation==="printed"&&entry.literal));
});

test("qualified named operators and bare operations use source identities without applying operand recipes",async t=>{
  const {retain,retainDeclaration,check}=await setup(t);
  retain("notation callable { x + y := first(x, y); -x := source_value; }");
  retain("notation numeric { numeral(n : UNat) := succ(n); }");
  retain("notation power { x ^ numeric.(n) := n; }");
  const retained=[
    "def binary_value : Two := left_ callable.(+) right_;",
    "def negated_value : Two := callable.(-) right_;",
    "def function_value : Two -> Two -> Two := callable.(+);",
    "def qualified_recipe : UNat := plain.(zero power.(^) 0);",
    "def ordinary_recipe : UNat := power.(zero ^ 0);",
    "def missing_operation : Two := left_ callable.(*) right_;",
    "def non_function : UNat -> UNat -> UNat := power.(^);",
  ].map(retainDeclaration);
  const {result,equal}=check(`def first(a, b : Two) : Two := b;
    notation callable { x + y := y; -x := right_; }
    notation power { x ^ y := x; }`,{retained});
  assert.deepEqual(failures(result).map(([name])=>name),["missing_operation","non_function"],JSON.stringify(failures(result)));
  for(const name of ["binary_value","negated_value"]) {
    assert.equal(equal(name,"left_"),true,name);assert.equal(equal(name,"right_"),false,name);
  }
  assert.equal(equal("function_value","fun (a, b : Two) => a"),true);
  assert.equal(equal("function_value","fun (a, b : Two) => b"),false);
  assert.equal(equal("qualified_recipe","zero"),true);assert.equal(equal("qualified_recipe","succ(zero)"),false);
  assert.equal(equal("ordinary_recipe","succ(zero)"),true);
});

test("a named receipt closes over used source identities without requiring the producer environment",async t=>{
  const {retain,check,translator}=await setup(t);
  const {artifact,receipt,env}=retain("notation closed { x + y := first(x, y); -x := source_value; }");
  assert.equal(receipt.rules.get("+").aliases.size,1);
  assert.equal(receipt.rules.get("unary -").aliases.size,1);
  const own=translator.identityAdapter.key(artifact.binding.id);
  const thin=new Map([...env].filter(([key])=>!key.startsWith("\u0000id ")||key===own));
  const {result,equal}=check("def picked : Two := closed.(left_ + right_); def constant : Two := closed.(-absent);",{env:thin});
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("picked","left_"),true);assert.equal(equal("picked","right_"),false);
  assert.equal(equal("constant","left_"),true);
});

test("lazy rule operands enter caller scope for interval and universe consumers",async t=>{
  const {retain,check}=await setup(t);
  retain("notation endpoint { p ^ i := p @ i; }");
  retain("notation universes { U + x := Reader(U); }");
  const {result,equal}=check(`
    def left_endpoint : Two := endpoint.(refl(left_) ^ 0);
    def line(p : left_ = left_) : left_ = left_ := path i => endpoint.(p ^ i);
    def universe_value : UU0 := universes.(U0 + absent);
    def invalid_interval : Two := endpoint.(refl(left_) ^ 2);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["invalid_interval"],JSON.stringify(failures(result)));
  assert.equal(equal("left_endpoint","left_"),true);
  assert.equal(equal("line","fun (p : left_ = left_) => p"),true);
  assert.equal(equal("universe_value","Reader(U0)"),true);
});

test("named-rule receipts survive isolated replay",async t=>{
  const library=sourceReader();
  const source=`import unat;
    notation increment { numeral(n : UNat) := succ(n); }
    def source_value : UNat := increment.(0);
    def anchor(x : UNat) : UNat := x;`;
  const program=new CubicalProgram(wasm,library,{collectScopes:true});
  t.after(()=>program.dispose());
  const result=await program.check(source,"main");
  assert.deepEqual(result.gaps,[],JSON.stringify(result.gaps));
  const points=[...program.scopePoints.values()].filter(point=>point.origin.module==="main"
    &&point.origin.start===source.lastIndexOf("x;")&&point.phase==="expression");
  assert.equal(points.length,1);
  const session=new ContextualSession(program,points[0].id);
  const [query]=await session.run("evaluate increment.(0)");
  assert.equal(query.kind,"value",JSON.stringify(query));
  assert.equal(query.text,"unat.(1)");
});

test("lazy operands retain distinct term and selection meanings through copying and invocation",async t=>{
  const {retain,retainDeclaration,check,table}=await setup(t);
  retain("notation m { numeral(n : UNat) := succ(n); x + y := add(x, y); }");
  retain("notation select_operand { m + x := m.(0); m * x := m; m ^ x := x m.(+) x; }");
  retain("notation forward { n + x := select_operand.(n + x); }");
  const saved=["def selected : UNat := select_operand.(m + absent);",
    "def qualified : UNat := select_operand.(m ^ succ(zero));",
    "def forwarded : UNat := forward.(m + absent);",
    "def term_missing : UNat := select_operand.(m * absent);"].map(retainDeclaration);
  for(const item of saved) {
    assert.doesNotThrow(()=>snapshotSyntax(item.syntax));
    const clone=cloneBindingSyntax(item.syntax,table,["copied-operand",item.binding.label]).syntax;
    assert.equal(sameBindingSyntax(item.syntax,clone),true);
    item.syntax=clone;
  }
  const {result,equal}=check("def m : Reader(U0) := plain;",{retained:saved});
  assert.deepEqual(failures(result).map(([name])=>name),["term_missing"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/Untranslated name: m/);
  assert.equal(equal("selected","succ(zero)"),true);
  assert.equal(equal("selected","zero"),false);
  assert.equal(equal("forwarded","succ(zero)"),true);
  assert.equal(equal("forwarded","zero"),false);
  assert.equal(equal("qualified","succ(succ(zero))"),true);
  assert.equal(equal("qualified","succ(zero)"),false);
});

test("lazy selector operands keep attached rules and the caller's ordinary operand notation",async t=>{
  const {retain,retainDeclaration,check}=await setup(t);
  retain("notation plain { numeral(n : UNat) := succ(succ(n)); }",{declared:new Set(["plain"])});
  retain(`notation select_operand {
    numeral(n : UNat) := n;
    m + x := m.(0);
    m * x := m.(x);
  }`);
  const saved=[
    "def attached : UNat := select_operand.(plain + absent);",
    "def parameter(plain : Reader(U0)) : plain.M := select_operand.(plain + absent);",
    "def ambient : UNat := select_operand.(plain * 0);",
    "def labels(read : UNat) : UNat := select_operand.(plain * read);",
    "def missing_label : UNat := select_operand.(plain * read);",
  ].map(retainDeclaration);
  retain("notation plain { numeral(n : UNat) := n; }",{declared:new Set(["plain"])});
  const {result,equal}=check("def plain : Reader(U0) := raised; def read : UNat := zero;",{retained:saved});
  assert.deepEqual(failures(result).map(([name])=>name),["missing_label"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/Untranslated name: read/);
  assert.equal(equal("attached","succ(succ(zero))"),true);
  assert.equal(equal("attached","zero"),false);
  assert.equal(equal("parameter","fun (plain : Reader(U0)) => plain.read(zero)"),true);
  assert.equal(equal("ambient","zero"),true);
  assert.equal(equal("ambient","succ(succ(zero))"),false);
  assert.equal(equal("labels","fun (read : UNat) => read"),true);
});

test("unused lazy namespace failures survive retained generation without becoming destination names",async t=>{
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  const source=`import hlevels; import unat;
notation ignore { x + y := zero; }
notation consume { x + y := x; }
theory Parent(U < UU0) { M : set U; c : M; }
theory Child(U < UU0) extends p : Parent {
  def ignored : UNat := ignore.(p.absent + zero);
  def rejected : UNat := consume.(p.absent + zero);
}
def value(S : Child(U0)) : S.ignored = zero { rfl; }
def wrong(S : Child(U0)) : S.ignored = succ(zero) { rfl; }`;
  const result=await program.check(source,"main");
  assert.deepEqual(result.gaps.map(g=>g.name),["Child.rejected","wrong"],JSON.stringify(result.gaps));
  assert.match(result.gaps[0].reason,/absent/);
  assert.ok(result.outputs.find(d=>d.name==="value").verified);
});

test("nested rule expansion preserves both producer sites and the outer caller",async t=>{
  const {retain,check,table}=await setup(t);
  const inner=retain("notation inside { x + y := x; }");
  const outer=retain("notation outside { x * y := inside.(x + y); }");
  const source="def value : Two := outside.(left_ * right_);";
  const {result,equal}=check(source);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("value","left_"),true);
  const original=inner.artifact.rules[0].syntax.tree.operands[0].bindingId;
  const copies=table.snapshot().bindings.filter(binding=>binding.original===original);
  assert.equal(copies.length,1);
  const {origin}=copies[0];
  assert.equal(origin.module,"recipe_source");
  assert.deepEqual(origin.expansion.map(frame=>[frame.binding,frame.site.module]),[
    [inner.artifact.binding.id,"recipe_source"],[outer.artifact.binding.id,"client"]]);
  assert.equal(source.slice(origin.expansion.at(-1).site.start,origin.expansion.at(-1).site.end),"left_ * right_");
  assert.ok(origin.expansion.every(frame=>frame.site.expansion.length===0));
});


test("missing notation readers keep their source diagnostics",async t=>{
  for(const [rule,code,advice] of [
    ["numeral(n : UNat) := n;","E847","import unat"],
    ["literal(s : Lexeme) := s;","E844","import lexemes"],
  ]) {
    const program=new CubicalProgram(wasm,async()=>"");t.after(()=>program.dispose());
    const source=`notation incomplete { ${rule} }
def independent : Unit := tt;`;
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps.map(gap=>gap.code),[code],JSON.stringify(result.gaps));
    assert.ok(result.gaps[0].reason.includes(advice));
    assert.equal(source.slice(result.gaps[0].start,result.gaps[0].end),rule);
    assert.ok(result.outputs.find(output=>output.name==="independent").verified);
  }
});

test("unselected retained notation reports source errors and preserves later declarations",async t=>{
  for(const [expression,code] of [["x * x","E912"],["-x","E901"],["f(0)","E911"],["f(0b101)","E909"]]) {
    const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
    const source=`import hlevels; import unat;
theory T(U < UU0) { M : set U; f(n : UNat) : M; law l(x : M) : ${expression} = x; }
def independent : Unit := tt;`;
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps.map(gap=>gap.code),[code],JSON.stringify(result.gaps));
    const gap=result.gaps[0];
    assert.ok(gap.start>=source.indexOf(expression)&&gap.end<=source.indexOf(expression)+expression.length,JSON.stringify(gap));
    assert.ok(result.outputs.find(output=>output.name==="independent").verified);
  }
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  const source="import unat;\nnotation n { x + y := x * y; }\ndef independent : Unit := tt;";
  const result=await program.check(source,"main"),[gap]=result.gaps;
  assert.deepEqual(result.gaps.map(gap=>gap.code),["E912"]);
  assert.equal(source.slice(gap.start,gap.end),"x * y");
  assert.ok(result.outputs.find(output=>output.name==="independent").verified);
});

test("theory notation printing uses its retained operand views",async t=>{
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  const result=await program.check(`import unat; import hlevels;
theory Ring(U < UU0) { R : set U; mul(x, y : R) : R notation x * y; pow(x : R, n : UNat) : R notation x ^ unat.(n); }
def Z : Ring(U0) := Ring.make(UNat, unat_is_set, mul, fun (x, n : UNat) => x);
def p(x, n : UNat) : Z.pow(x, unat.(n + 1)) = Z.pow(x, unat.(n + 1)) := refl(Z.pow(x, unat.(n + 1)));
use Z;
print(typeof(p));`,"main");
  assert.deepEqual(result.gaps,[]);
  assert.match(program.prints[0].text,/x \^ \(n \+ 1\)/);
  assert.doesNotMatch(program.prints[0].text,/unat\.\(/);
});

test("imported rule failures belong to the caller while operand errors keep their own spans",async t=>{
  const library=sourceReader();
  for(const [body,operand,code,nested,expected] of [
    ["add(x, 1)","zero","E911",false,["zero + zero","a + a"]],
    ["add(x.1, y)","zero","E349",false,["zero + zero","a + a"]],
    ["add(x.1, y)","zero","E349",true,["zero + zero","a + a"]],
    ["add(x, y)","zero.1","E349",false,[".1",".1"]],
  ]) {
    const lib=`import unat;\n// ${"source padding ".repeat(20)}\nnotation bad { x + y := ${body}; }`;
    const middle="import lib; notation wrapper { x + y := bad.(x + y); }";
    const program=new CubicalProgram(wasm,async(name,importer)=>({lib,middle})[name]??library(name,importer));
    t.after(()=>program.dispose());
    const rule=nested?"wrapper":"bad",arg=operand==="zero.1"?"a.1":"a";
    const source=`import ${nested?"middle":"lib"}; import unat;
print(evaluate(${rule}.(${operand} + zero)));
def f(a : UNat) : UNat := ${rule}.(${arg} + a);
def after : Unit := tt;`;
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps.map(gap=>gap.code),[code,code],JSON.stringify(result.gaps));
    assert.deepEqual(result.gaps.map(gap=>source.slice(gap.start,gap.end)),expected);
    assert.ok(result.gaps.every(gap=>gap.module==="main"&&gap.start>=0&&gap.end<=source.length));
    assert.ok(result.outputs.find(output=>output.name==="after").verified);
  }
});

test("explicit parent notation keeps missing-operation diagnostics and interval endpoints",async t=>{
  const header=`import hlevels; import unat;
theory P(U < UU0) { M : set U; c : M; op(x, y : M) : M notation x + y; f(n : UNat) : M; }\n`;
  for(const [expression,code] of [["x * x","E397"],["-x","E902"],["f(0b1)","E910"],["f(0)","E907"]]) {
    const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
    const source=header+`theory T(U < UU0) extends p : P { law l(x : M) : p.(${expression}) = x; }`;
    const result=await program.check(source,"main");
    assert.deepEqual(result.gaps.map(gap=>gap.code),[code],JSON.stringify(result.gaps));
    assert.match(result.gaps[0].reason,/p's notation/);
  }
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  const result=await program.check(header+`theory T(U < UU0) extends p : P {
    law at_zero(q : c = c) : p.(q @ 0) = c;
    law at_one(q : c = c) : p.(q @ 1) = c;
  }`,"main");
  assert.deepEqual(result.gaps,[]);
});
