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
const shared=`import hlevels; import nat;
theory Pick(U < UU0) { M : set U; one : M; combine(x, y : M) : M notation x + y; }
def chosen : Pick(U0) := Pick.make(Nat, nat_is_set, zero, add);
def one : Nat := succ(zero);
def equation(n : Nat) : add(n, zero) = n := nat_add_zero(n);
def set_proof : IsSet(U0, Nat) := nat_is_set;`;
const check=(t,source)=>checkProgram(t,source,{module,
  reader:(name,importer)=>name==="shared"?shared:library(name,importer)});

test("captured numeral types elaborate lazily and preserve ignored notation arguments",async t=>{
  const {result,get}=await check(t,`import nat;
    notation ignored { numeral(n : Nat) := zero; }
    notation identity { numeral(n : Nat) := n; }
    def ignored_large : Nat := ignored.(999);
    def intended : ignored_large = zero := refl(zero);
    def wrong : ignored_large = succ(zero) := refl(succ(zero));
    def consumed_large : Nat := identity.(999);
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
    theory Power(U < UU0) { M : set U; pow(x : M, n : Nat) : M notation x ^ chosen.(n); }
    def client(S : Power(U0), x : S.M, one : Nat) : S.M := S.(x ^ one);
    def intended(S : Power(U0), x : S.M, n : Nat) : client(S, x, n) = S.pow(x, n) { rfl; }
    def captured(S : Power(U0), x : S.M, n : Nat) : client(S, x, n) = S.pow(x, zero) { rfl; }
    def global_(S : Power(U0), x : S.M) : S.(x ^ one) = S.pow(x, succ(zero)) { rfl; }
    def missing(S : Power(U0), x : S.M) : S.M := S.(x ^ combine(zero, zero));
    def written : chosen.(one) = zero { rfl; }
  `);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"],["missing","E343"]],JSON.stringify(result.gaps));
  for(const name of ["client","intended","global_","written"])assert.equal(get(name).verified,true,name);
});

test("model operand recipes own source globals, named rules and abstract model interfaces",async t=>{
  const source=`import nat;
    theory Numeric(U < UU0) { M : U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral; }
    def recipe : Numeric(U0) := Numeric.make(Nat, fun (n : Nat) => n);
    def shifted : Numeric(U0) := Numeric.make(Nat, fun (n : Nat) => succ(n));
    notation named { numeral(n : Nat) := n; }
    def attached : Numeric(U0) := shifted;
    notation attached { numeral(n : Nat) := n; }
    theory Global(U < UU0) { M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n); }
    theory Named(U < UU0) { M : U; pow(x : M, n : Nat) : M notation x ^ named.(n); }
    theory Attached(U < UU0) { M : U; pow(x : M, n : Nat) : M notation x ^ attached.(n); }
    theory Header(U < UU0, recipe : Numeric(U0)) { M : U; pow(recipe : M, n : Nat) : M notation recipe ^ recipe.(n); }
    theory HelperShadow(U < UU0, recipe : Numeric(U0)) {
      M : U; def recipe : Numeric(U0) := shifted;
      pow(x : M, n : Nat) : M notation x ^ recipe.(n);
    }
    theory NamedShadow(U < UU0, named : Numeric(U0)) { M : U; pow(x : M, n : Nat) : M notation x ^ named.(n); }
    theory Field(U < UU0) { recipe : Numeric(U0); M : U; pow(recipe : M, n : Nat) : M notation recipe ^ recipe.(n); }
    theory Child(U < UU0) extends p : Field(recipe := reader, pow := power) {}
    theory Further(U < UU0) extends c : Child(reader := decoder) {}
    theory Replaced(U < UU0) extends p : Field(recipe := reader, pow := power notation x + reader.(n)) {}
    theory Parent(U < UU0) extends num : Numeric {
      pow(x : M, n : Nat) : M notation x ^ num.(n);
    }
    theory Missing(U < UU0) { M : U; pow(x : M, n : Nat) : M notation x ^ absent.(n); }
    def global_model : Global(U0) := Global.make(Nat, fun (x, n : Nat) => n);
    def named_model : Named(U0) := Named.make(Nat, fun (x, n : Nat) => n);
    def attached_model : Attached(U0) := Attached.make(Nat, fun (x, n : Nat) => n);
    def header_model : Header(U0, recipe) := Header.make(recipe, Nat, fun (x, n : Nat) => n);
    def helper_model : HelperShadow(U0, recipe) := HelperShadow.make(recipe, Nat, fun (x, n : Nat) => n);
    def namespace_model : NamedShadow(U0, shifted) := NamedShadow.make(shifted, Nat, fun (x, n : Nat) => n);
    def field_model : Further(U0) := Further.make(recipe, Nat, fun (x, n : Nat) => n);
    def replacement_model : Replaced(U0) := Replaced.make(shifted, Nat, fun (x, n : Nat) => n);
    def parent_model : Parent(U0) := Parent.make(Nat, fun (n : Nat) => n, fun (x, n : Nat) => n);
    def missing_model : Missing(U0) := Missing.make(Nat, fun (x, n : Nat) => n);
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
    def caller_names(n : Nat) : global_model.(zero ^ n) = n { rfl; }
    def missing_value : Nat := missing_model.(zero ^ 0);
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
      M : U; pow(x : M, n : Nat) : M notation x ^ chosen.(n);
    }
    theory Partial(U < UU0) {
      M : U; point : M;
      def broken : Pick(U0) := tt;
      pow(x : M, n : Nat) : M notation x ^ broken.(n);
    }
    def instance_ : Power(U0) := Power.make(Nat, fun (x, n : Nat) => n);
    def partial : Partial(U0) := Partial.make(Nat, zero, fun (x, n : Nat) => n);
  `;
  const {program,result}=await checkProgram(t,source,{module,reader:(name,importer)=>name==="shared"?shared:library(name,importer)});
  assert.deepEqual(result.gaps.map(g=>g.name),["Partial.broken"],JSON.stringify(result.gaps));
  const client=`def value(n : Nat) : Nat := instance_.(zero ^ n);
    def healthy : Nat := partial.(point);
    def uses_broken : Nat := partial.(zero ^ zero);`;
  const references=[];let declaration;
  const checker=Object.create(program.checker);checker.bindingName=name=>`client__${name}`;
  checker.define=(name,...args)=>program.checker.define(checker.bindingName(name),...args);
  const translator=new Translator({checker,moduleName:"client",compilationBindings:program.compilationBindings,
    onDeclarationStart:node=>{declaration=node.name.text;},
    onReference:node=>{if(declaration==="value")references.push(node);}});
  const checked=translator.translateSyntax(parse(client),client,program.modules.get("main"));
  const failures=checked.declarations.filter(d=>d.status!=="checked-native-cubical");
  assert.deepEqual(failures.map(d=>d.name),["uses_broken"],JSON.stringify(failures));
  assert.match(failures[0].reason,/Untranslated dependency: Partial.broken/);
  assert.ok(references.every(node=>node.start<client.indexOf("def healthy")),JSON.stringify(references));
  for(const start of [client.indexOf("instance_."),client.indexOf("zero ^"),client.indexOf("n);")])
    assert.ok(references.some(node=>node.start===start),`caller reference at ${start}`);
});
