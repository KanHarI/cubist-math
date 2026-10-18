import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {selected,sourceItemScope,SELECTION,operatorBinding} from "../web/translator/theories.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {selectionEffects,fileSelectionEffects} from "../web/cubist/scopes.mjs";

const module=await create(),library=sourceReader();
const shared=`import hlevels; import unat;
theory Pick(U < UU0) { M : set U; one : M; combine(x, y : M) : M notation x + y; }
def chosen : Pick(U0) := Pick.make(UNat, unat_is_set, zero, add);
def one : UNat := succ(zero);
def equation(n : UNat) : add(n, zero) = n := unat_add_zero(n);
def set_proof : IsSet(U0, UNat) := unat_is_set;`;
const check=(t,source)=>checkProgram(t,source,{module,
  reader:(name,importer)=>name==="shared"?shared:library(name,importer)});

test("captured numeral types elaborate lazily and preserve ignored notation arguments",async t=>{
  const {result,get}=await check(t,`import unat;
    notation ignored { numeral(n : UNat) := zero; }
    notation identity { numeral(n : UNat) := n; }
    def ignored_large : UNat := ignored.(999);
    def intended : ignored_large = zero := refl(zero);
    def wrong : ignored_large = succ(zero) := refl(succ(zero));
    def consumed_large : UNat := identity.(999);
  `);
  assert.deepEqual(result.gaps.map(g=>g.name),["wrong","consumed_large"],JSON.stringify(result.gaps));
  assert.match(result.gaps[1].reason,/limited to 256/);
  for(const name of ["ignored_large","intended"])assert.equal(get(name).verified,true);
});

test("one selection activation checks its receiver once and applies only the requested effects",async t=>{
  const {program,result}=await check(t,"import shared;");assert.deepEqual(result.gaps,[]);
  const env=program.modules.get("main"),translator=new Translator({checker:program.checker,compilationBindings:program.compilationBindings});
  const scope=new Scope(translator.unit(),new Map(),env),node=parse("chosen",true),term=translator.term.bind(translator);
  let reads=0;
  translator.term=(node,...args)=>{if(node.kind==="name"&&node.name==="chosen")reads++;return term(node,...args);};
  const notation=selected(translator,scope,node,{effects:selectionEffects.notation});
  assert.equal(reads,1);
  assert.equal(notation.env.get("one"),scope.env.get("one"));
  assert.ok(notation.env.get(SELECTION).operators.has("+"));
  assert.ok(notation.env.get(operatorBinding("+")));
  const opened=selected(translator,scope,node);
  assert.equal(reads,2);
  assert.equal(opened.equal(opened.env.get("one"),term(parse("zero",true),opened)),true);
  assert.equal(opened.equal(opened.env.get("one"),scope.env.get("one")),false);
  for(const kind of ["simp_rule","simp_set","hlevel_rule"])
    assert.equal(sourceItemScope(translator,scope,{kind,uses:[parse("missing_receiver",true)]}),scope);
  assert.throws(()=>fileSelectionEffects("future_consumer"),/explicit selection policy/);
});

const consumers=[
  ["definition","def client : Unit := tt;"],
  ["inductive","inductive Client { point_; }"],
  ["theory","theory Client(U < UU0) extends Missing { M : set U; }"],
  ["initial","initial Client : Missing(U0);"],
  ["free","free Client : Missing(U0) on Unit;"],
  ["evaluation","evaluate(tt) expecting tt;"],
  ["printing","print(typeof(tt));"],
  ["notation","notation Client { x + y := add(x, y); }"],
  ["use","use chosen;"],
];
for(const [label,consumer] of consumers)test(`required activation precedes ${label} processing`,async t=>{
  const {program,result,get}=await check(t,`import shared;
    def independent : Unit := tt;
    use chosen;
    def chosen : Unit := tt;
    ${consumer}`);
  assert.deepEqual(result.gaps.map(g=>g.code),["E834"],JSON.stringify(result.gaps));
  assert.equal(get("independent").verified,true);assert.equal(get("chosen").verified,true);
  assert.ok(!Object.values(program.symbols).some(output=>output.verified&&(output.name==="Client"||output.name.startsWith("Client."))));
  assert.equal(program.publications.get("main").length,0,
    "a failed activation cannot start an expansion in a fallback context");
});

for(const [kind,directive] of [["simp_rule","simp_rule equation;"],["simp_set","simp_set equations := [equation];"],
  ["hlevel_rule","hlevel_rule set_proof;"]])test(`${kind} does not activate a now-invalid file-level receiver`,async t=>{
  const {program,result}=await check(t,`import shared; use chosen; def chosen : Unit := tt; ${directive}`);
  assert.deepEqual(result.gaps,[]);
  const registry=program.simpRegistries.get("main");
  const rules=kind==="simp_set"?registry.sets.get("equations").rules:[...(kind==="hlevel_rule"?registry.hlevel:registry.defaults).values()];
  assert.ok(rules.some(rule=>rule.identity===(kind==="hlevel_rule"?"shared__set_proof":JSON.stringify({tag:"DefRef",name:"shared__equation"}))));
});

test("operand notation preserves caller labels and cannot supply an unbound name",async t=>{
  const {result,get}=await check(t,`import shared;
    theory Power(U < UU0) { M : set U; pow(x : M, n : UNat) : M notation x ^ chosen.(n); }
    def client(S : Power(U0), x : S.M, one : UNat) : S.M := S.(x ^ one);
    def intended(S : Power(U0), x : S.M, n : UNat) : client(S, x, n) = S.pow(x, n) { rfl; }
    def captured(S : Power(U0), x : S.M, n : UNat) : client(S, x, n) = S.pow(x, zero) { rfl; }
    def global_(S : Power(U0), x : S.M) : S.(x ^ one) = S.pow(x, succ(zero)) { rfl; }
    def missing(S : Power(U0), x : S.M) : S.M := S.(x ^ combine(zero, zero));
    def written : chosen.(one) = zero { rfl; }
  `);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"],["missing","E343"]],JSON.stringify(result.gaps));
  for(const name of ["client","intended","global_","written"])assert.equal(get(name).verified,true,name);
});

test("model operand recipes own source globals, named rules and abstract model interfaces",async t=>{
  const source=`import unat;
    theory Numeric(U < UU0) { M : U; read(n : UNat) : M; def numeral_(n : UNat) : M := read(n) notation numeral; }
    def recipe : Numeric(U0) := Numeric.make(UNat, fun (n : UNat) => n);
    def shifted : Numeric(U0) := Numeric.make(UNat, fun (n : UNat) => succ(n));
    notation named { numeral(n : UNat) := n; }
    def attached : Numeric(U0) := shifted;
    notation attached { numeral(n : UNat) := n; }
    theory Global(U < UU0) { M : U; pow(x : M, n : UNat) : M notation x ^ recipe.(n); }
    theory Named(U < UU0) { M : U; pow(x : M, n : UNat) : M notation x ^ named.(n); }
    theory Attached(U < UU0) { M : U; pow(x : M, n : UNat) : M notation x ^ attached.(n); }
    theory Header(U < UU0, recipe : Numeric(U0)) { M : U; pow(recipe : M, n : UNat) : M notation recipe ^ recipe.(n); }
    theory HelperShadow(U < UU0, recipe : Numeric(U0)) {
      M : U; def recipe : Numeric(U0) := shifted;
      pow(x : M, n : UNat) : M notation x ^ recipe.(n);
    }
    theory NamedShadow(U < UU0, named : Numeric(U0)) { M : U; pow(x : M, n : UNat) : M notation x ^ named.(n); }
    theory Field(U < UU0) { recipe : Numeric(U0); M : U; pow(recipe : M, n : UNat) : M notation recipe ^ recipe.(n); }
    theory Child(U < UU0) extends p : Field(recipe := reader, pow := power) {}
    theory Further(U < UU0) extends c : Child(reader := decoder) {}
    theory Replaced(U < UU0) extends p : Field(recipe := reader, pow := power notation x + reader.(n)) {}
    theory Parent(U < UU0) extends num : Numeric {
      pow(x : M, n : UNat) : M notation x ^ num.(n);
    }
    theory Missing(U < UU0) { M : U; pow(x : M, n : UNat) : M notation x ^ absent.(n); }
    def global_model : Global(U0) := Global.make(UNat, fun (x, n : UNat) => n);
    def named_model : Named(U0) := Named.make(UNat, fun (x, n : UNat) => n);
    def attached_model : Attached(U0) := Attached.make(UNat, fun (x, n : UNat) => n);
    def header_model : Header(U0, recipe) := Header.make(recipe, UNat, fun (x, n : UNat) => n);
    def helper_model : HelperShadow(U0, recipe) := HelperShadow.make(recipe, UNat, fun (x, n : UNat) => n);
    def namespace_model : NamedShadow(U0, shifted) := NamedShadow.make(shifted, UNat, fun (x, n : UNat) => n);
    def field_model : Further(U0) := Further.make(recipe, UNat, fun (x, n : UNat) => n);
    def replacement_model : Replaced(U0) := Replaced.make(shifted, UNat, fun (x, n : UNat) => n);
    def parent_model : Parent(U0) := Parent.make(UNat, fun (n : UNat) => n, fun (x, n : UNat) => n);
    def missing_model : Missing(U0) := Missing.make(UNat, fun (x, n : UNat) => n);
  `;
  const {result,get}=await checkProgram(t,`import recipes;
    def recipe : Numeric(U0) := shifted;
    def named : Unit := tt;
    def attached : Numeric(U0) := shifted;
    def reader : Numeric(U0) := shifted;
    def absent : Numeric(U0) := shifted;
    def global_value(recipe : Unit) : global_model.(zero ^ 0) = zero { rfl; }
    def global_wrong : global_model.(zero ^ 0) = succ(zero) { rfl; }
    def named_value(named : Unit) : named_model.(zero ^ 0) = zero { rfl; }
    def attached_value(attached : Unit) : attached_model.(zero ^ 0) = zero { rfl; }
    def header_value(recipe : Unit) : header_model.(zero ^ 0) = zero { rfl; }
    def helper_value(recipe : Unit) : helper_model.(zero ^ 0) = succ(zero) { rfl; }
    def helper_wrong : helper_model.(zero ^ 0) = zero { rfl; }
    def namespace_value(named : Unit) : namespace_model.(zero ^ 0) = zero { rfl; }
    def field_value(decoder : Unit) : field_model.(zero ^ 0) = zero { rfl; }
    def replacement_value(reader : Unit) : replacement_model.(zero + 0) = succ(zero) { rfl; }
    def parent_value(num : Unit) : parent_model.(zero ^ 0) = zero { rfl; }
    def caller_names(n : UNat) : global_model.(zero ^ n) = n { rfl; }
    def missing_value : UNat := missing_model.(zero ^ 0);
  `,{module,reader:(name,importer)=>name==="recipes"?source:library(name,importer)});
  assert.deepEqual(result.gaps.map(g=>g.name),["global_wrong","helper_wrong","missing_value"],JSON.stringify(result.gaps));
  assert.match(result.gaps.at(-1).reason,/Untranslated name: absent/);
  for(const name of ["global_value","named_value","attached_value","header_value","helper_value","namespace_value","field_value","replacement_value","parent_value","caller_names"])
    assert.equal(get(name).verified,true,name);
});

test("captured operand receivers keep caller references and defer refused dependencies until use",async t=>{
  const source=`import shared;
    ${"// source padding\n".repeat(100)}
    theory Power(U < UU0) {
      M : U; pow(x : M, n : UNat) : M notation x ^ chosen.(n);
    }
    theory Partial(U < UU0) {
      M : U; point : M;
      def broken : Pick(U0) := tt;
      pow(x : M, n : UNat) : M notation x ^ broken.(n);
    }
    def invalid : Unit := tt;
    theory Invalid(U < UU0) { M : U; pow(x : M, n : UNat) : M notation x ^ invalid.(n); }
    def instance_ : Power(U0) := Power.make(UNat, fun (x, n : UNat) => n);
    def partial : Partial(U0) := Partial.make(UNat, zero, fun (x, n : UNat) => n);
    def invalid_instance : Invalid(U0) := Invalid.make(UNat, fun (x, n : UNat) => n);
  `;
  const {program,result}=await checkProgram(t,source,{module,reader:(name,importer)=>name==="shared"?shared:library(name,importer)});
  assert.deepEqual(result.gaps.map(g=>g.name),["Partial.broken"],JSON.stringify(result.gaps));
  const client=`def value(n : UNat) : UNat := instance_.(zero ^ n);
    def healthy : UNat := partial.(point);
    def uses_broken : UNat := partial.(zero ^ zero);
    def uses_invalid : UNat := invalid_instance.(zero ^ zero);`;
  const references=[];let declaration;
  const checker=program.checker,definitionModule="client";
  const translator=new Translator({checker,definitionModule,moduleName:"client",compilationBindings:program.compilationBindings,
    onDeclarationStart:node=>{declaration=node.name.text;},
    onReference:node=>{if(declaration==="value")references.push(node);}});
  const checked=translator.translateSyntax(parse(client),client,program.modules.get("main"));
  const failures=checked.declarations.filter(d=>d.status!=="checked-native-cubical");
  assert.deepEqual(failures.map(d=>d.name),["uses_broken","uses_invalid"],JSON.stringify(failures));
  assert.match(failures[0].reason,/Untranslated dependency: Partial.broken/);
  assert.match(failures[1].reason,/use selects a model of a theory/);
  assert.equal(failures[1].errorStart,client.lastIndexOf("zero"));
  assert.equal(failures[1].errorEnd,client.lastIndexOf("zero")+4);
  assert.ok(references.every(node=>node.start<client.indexOf("def healthy")),JSON.stringify(references));
  for(const start of [client.indexOf("instance_."),client.indexOf("zero ^"),client.indexOf("n);")])
    assert.ok(references.some(node=>node.start===start),`caller reference at ${start}`);
});
