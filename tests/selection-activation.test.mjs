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
