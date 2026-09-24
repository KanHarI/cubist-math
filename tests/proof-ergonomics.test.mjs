import test from "node:test";
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {formatMathScript} from "../web/mathscript/formatter.mjs";
import {parse} from "../web/mathscript/parser.mjs";
import {expandedSyntax} from "../web/mathscript/tuples.mjs";

const readLibrary = name => readFile(new URL(`../web/proofs/${name}.cubist`,import.meta.url),"utf8");
const sample = name => readFile(new URL(`../docs/examples/proof-ergonomics/implemented/${name}.cubist`,import.meta.url),"utf8");

test("short arithmetic, cubical and dependent examples elaborate to native axiom-free proofs",async t=>{
  for(const name of ["arithmetic","cubical","dependent","type-transport"]) {
    const program=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>program.dispose());
    const result=await program.check(await sample(name),`ergonomics_${name}`);
    assert.equal(result.complete,true,`${name}: ${JSON.stringify(result.gaps)}`);
    assert.ok(result.outputs.every(d=>d.verified&&d.axioms.length===0),name);
    if(name==="arithmetic") for(const role of ["calculation witness","rewrite witness","simplification witness"]) {
      const link=result.links.find(item=>item.role===role);
      assert.ok(link,role);
      assert.equal(program.inspect(link.binding).type.tag,"Path",role);
    }
    if(name==="arithmetic") {
      const steps=result.links.filter(item=>item.role==="calculation step");
      assert.ok(steps.length>=2);
      assert.equal(new Set(steps.map(item=>item.binding)).size,steps.length);
      for(const step of steps) assert.equal(program.inspect(step.binding).type.tag,"Path");
    }
  }
});

test("new proof syntax survives formatting with the same expanded AST",async()=>{
  for(const name of ["arithmetic","cubical","dependent","type-transport"]) {
    const source=await sample(name),formatted=formatMathScript(source);
    assert.equal(formatMathScript(formatted),formatted,name);
    assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)),name);
  }
});

test("incomplete grouped binders and introductions fail without hanging the parser",()=>{
  const parser=new URL("../web/mathscript/parser.mjs",import.meta.url).href;
  for(const source of ["def f(x","def f : forall x","def f = fun (x",
    "def f : Nat { intro x"]) {
    const script=`import {parse} from ${JSON.stringify(parser)}; parse(process.argv[1]);`;
    const child=spawnSync(process.execPath,["--input-type=module","-e",script,source],
      {encoding:"utf8",timeout:1000});
    assert.equal(child.error,undefined,source);
    assert.notEqual(child.status,0,source);
    assert.match(child.stderr,/Expected a name\./,source);
  }
});

test("rewrites retain occurrence, carrier and dependent-position obligations",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def first(n : Nat) : (n + 0) + (n + 0) = n + (n + 0) {
      rw [nat_add_zero(n)] at lhs occurrence 1;
    }
    def second(n : Nat) : (n + 0) + (n + 0) = (n + 0) + n {
      rw [nat_add_zero(n)] at lhs occurrence 2;
    }
    def reverse(n : Nat) : n = n + 0 { rw [<- nat_add_zero(n)] at lhs; }
    def default_second(n : Nat) : n + 0 = n + 0 {
      rw [nat_add_zero(n)] occurrence 2;
      exact nat_add_zero(n);
    }
    def missing(n : Nat) : n + 0 = n { rw [nat_add_zero(n)] at lhs occurrence 2; }
    def dependent(A : U0, C : A -> U0, f : forall a : A, C(a), x : A, y : A, p : x = y) :
      f(x) = f(x) { rw [p] at lhs; }
    def after : 0 = 0 { rfl; }
  `,"rewrite_rejections");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,false,false,true]);
  assert.match(result.outputs[4].reason,/occurrence 2/);
  assert.match(result.outputs[5].reason,/unsupported dependent position/);
});

test("simp stops on cycles and does not equate a loop with reflexivity",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def cyclic(n : Nat) : n + 0 = n { simp only [nat_add_zero, <- nat_add_zero]; }
    def false_claim : 0 = 1 { simp only []; }
    def loop_claim(A : U0, x : A, p : x = x) : p = refl(x) { simp only []; }
    def good : 0 = 0 { simp only []; }
  `,"simp_rejections");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,false,true]);
  assert.match(result.outputs[0].reason,/cycle|budget/);
  assert.match(result.outputs[1].reason,/unresolved equality/);
  assert.match(result.outputs[2].reason,/unresolved equality/);
});

test("simpa reconstructs the original equality and rejects a false supplied term",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def good(n : Nat) : n + 0 = n { simpa only [nat_add_zero] using refl(n); }
    def bad : 0 = 1 { simpa only [] using refl(0); }
  `,"simpa_reconstruction");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,false]);
  assert.deepEqual(result.outputs[0].axioms,[]);
  assert.match(result.outputs[1].reason,/Type mismatch/);
});

test("simpa transports through checked paths of types without inventing equivalences",async t=>{
  const source=await sample("type-transport");
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const checked=await program.check(source,"type_transport");
  assert.equal(checked.complete,true,JSON.stringify(checked.gaps));
  assert.equal(checked.outputs.length,5);
  assert.ok(checked.outputs.every(output=>output.verified&&output.axioms.length===0));
  const frozen=checked.links.find(link=>link.role==="simplification witness"&&link.freeze);
  assert.equal(frozen?.freeze.text,"simpa only [nat_add_zero] using h;");
  assert.equal(program.inspect(frozen.rewriteSteps[0].binding).type.tag,"Path");
  const replaySource=source.slice(0,frozen.freeze.start)+frozen.freeze.text
    +source.slice(frozen.freeze.end);
  const replay=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>replay.dispose());
  assert.equal((await replay.check(replaySource,"type_transport_frozen")).complete,true);

  const rejected=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>rejected.dispose());
  const bad=await rejected.check(`
    def no_path(A B : U0, a : A) : B { simpa only [] using a; }
    def maps_are_not_type_paths(A B : U0, f : A -> B, g : B -> A, a : A) : B {
      simpa only [f, g] using a;
    }
    def nontrivial_loop(A : U0, p : A = A, a : A) : A {
      simpa only [p] using a;
    }
  `,"type_transport_rejections");
  assert.deepEqual(bad.outputs.map(output=>output.verified),[false,false,false]);
  assert.match(bad.outputs[0].reason,/Type mismatch/);
  assert.match(bad.outputs[1].reason,/homogeneous equality/);
  assert.match(bad.outputs[2].reason,/cycle/);
});

test("simp tries rules at each child before rewriting its parent",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def equality(f : Nat -> Nat, a b c d : Nat,
      p : f(a) = c, q : a = b, r : f(b) = d) : f(a) = d {
      simp only [p, q, r];
    }
    def type_goal(P : Nat -> U0, f : Nat -> Nat, a b c d : Nat,
      p : f(a) = c, q : a = b, r : f(b) = d, h : P(d)) : P(f(a)) {
      simpa only [p, q, r] using h;
    }
  `,"simp_child_order");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output=>output.axioms.length===0));
});

test("a quantified rule with an incompatible parameter type leaves later rules available",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def through(f : Nat -> Nat, n : Nat) : f(n + 0) = f(n) {
      exact cong(f,nat_add_zero(n));
    }
    def family(P : Nat -> U0, n : Nat) : P(n + 0) = P(n) {
      simp only [through, nat_add_zero];
    }
  `,"simp_incompatible_candidate");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output=>output.axioms.length===0));
});

test("universe templates retain their defining simplification sets during use and inspection",async t=>{
  const modules={rules:`import primes;
    simp_set units = [nat_add_zero];
    def generic(U : Universe, n : Nat) : n + 0 = n { simp only [units]; }
  `};
  const program=new CubicalProgram(await createCubical(),
    module=>modules[module]??readLibrary(module));
  t.after(()=>program.dispose());
  const result=await program.check(`import rules;
    simp_set units = [];
    def use(n : Nat) : n + 0 = n { exact generic(U0,n); }
  `,"template_rule_scope");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs[0].axioms,[]);
  assert.equal(program.inspect("rules__generic",{universes:[0]}).type.tag,"Pi");
});

test("freeze is withheld when removing a rule changes conditional premise search",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def freeze_case(f g k : Nat -> Nat, a b t : Nat,
      c : forall n : Nat, g(n) = n -> f(n) = k(n),
      divert : g(a) = b, unit : forall n : Nat, g(n) = n,
      fallback : f(a) = t) : f(a) + f(b) = t + k(b) {
      simp [c, divert, unit, fallback];
    }
  `,"simp_freeze_premise_search");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs[0].axioms,[]);
  const link=result.links.find(item=>item.role==="simplification witness");
  assert.ok(link);
  assert.equal(link.freeze,null);
});

test("freezing a simplified hypothesis preserves its witness for dependent proofs",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`import primes;
    def dependent(f g k : Nat -> Nat, a b : Nat,
      c : forall n : Nat, g(n) = n -> f(n) = k(n),
      divert : g(a) = b, unit : forall n : Nat, g(n) = n,
      fallback : f(a) = k(a), h : f(a) + f(b) = k(a) + k(b)) : 0 = 0 {
      simp only [c, divert, unit, fallback] at h as h1;
      simp [c, divert, unit, fallback] at h as h2;
      have stable : h2 = h1 { rfl; }
      rfl;
    }
    def stable(n : Nat, h : n + 0 = n, unused : 2 = 3) : n = n {
      simp [h, unused] at h as h2;
      exact h2;
    }
  `;
  const result=await program.check(source,"simp_freeze_witness");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  const links=result.links.filter(item=>item.role==="simplification witness");
  assert.equal(links.length,3);
  assert.equal(links[1].freeze,null);
  assert.equal(links[2].freeze?.text,"simp only [h] at h as h2;");
  const edit=links[2].freeze;
  const replay=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>replay.dispose());
  assert.equal((await replay.check(source.slice(0,edit.start)+edit.text+source.slice(edit.end),
    "simp_freeze_witness_replay")).complete,true);
});

test("a naturality square must preserve its varying right boundary",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const invalid=(await sample("cubical")).replace("H(p @ i) @ j","H(x) @ j");
  const result=await program.check(invalid,"invalid_square");
  const square=result.outputs.find(d=>d.name==="naturality_square");
  assert.equal(square.verified,false);
});

test("a grouped binder checks its shared domain before a binder shadows that name",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def Carrier = Nat;
    def grouped(Carrier item : Carrier) : item = item { rfl; }
    def applied : grouped(0, 1) = grouped(0, 1) { rfl; }
    def inferred_lambda(A : U0) : A -> A { exact fun x => x; }
    def quantified : forall A B : U0, A -> B -> A { intro A B x y; exact x; }
  `,"group_shadowing");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,true]);
});

test("normal program checking rolls back a failed universe specialization",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def identity(U : Universe, A : U, x : A) = x;
    def before = identity(U0, Nat, 0);
    def failed : 0 = 1 { exact identity(U1, U0, Nat); }
    def after = identity(U0, Nat, 1);
  `,"transaction");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,true,false,true]);
  assert.ok(program.kernel.definitions.has("transaction__identity__U0"));
  assert.equal(program.kernel.definitions.has("transaction__identity__U1"),false);
});

test("a late declaration observer error rolls back its native definition",async t=>{
  let reject=true;
  const program=new CubicalProgram(await createCubical(),readLibrary,{
    onDeclaration() {if(reject){reject=false;throw Error("observer rejected declaration");}}
  });
  t.after(()=>program.dispose());
  await assert.rejects(program.check("def discarded = 0;","observer_failure"),/observer rejected declaration/);
  assert.equal(program.kernel.definitions.has("observer_failure__discarded"),false);
  const recovered=await program.check("def accepted = 1;","observer_recovery");
  assert.equal(recovered.outputs[0].verified,true);
});

test("a quantified simp rule enforces repeated parameter consistency",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def duplicated(n : Nat) : n + n = n + n { rfl; }
    def different : 0 + 1 = 0 + 1 { simp only [duplicated]; }
    def same : 1 + 1 = 1 + 1 { simp only [duplicated]; }
  `,"repeated_match");
  assert.equal(result.outputs[0].verified,true);
  assert.equal(result.outputs[1].verified,true);
  assert.equal(result.outputs[2].verified,false);
  assert.match(result.outputs[2].reason,/cycle/);
});

test("registered default and named sets retain checked proofs and format stably",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=await sample("registered-simp");
  const result=await program.check(source,"registered_simp");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.equal(result.outputs.length,9);
  assert.ok(result.outputs.every(d=>d.verified&&d.axioms.length===0));
  const work=result.outputs.find(d=>d.name==="recursive_premise").rewriteWork;
  assert.ok(work.traversals>work.successfulRewrites);
  assert.ok(work.candidateVisits>=work.traversals);
  assert.equal(work.premiseProofs,0);
  const choices=result.links.filter(link=>link.role==="simplification witness"&&link.freeze);
  assert.equal(choices.length,6);
  const recursive=choices.find(choice=>choice.freeze.original==="simp;"
    &&choice.freeze.text.includes("nat_add_zero"));
  assert.ok(recursive);
  assert.doesNotMatch(recursive.freeze.text,/double_zero_if/);
  for(const [index,choice] of choices.entries()) {
    assert.ok(choice.rewriteSteps?.length,choice.name);
    for(const step of choice.rewriteSteps)
      assert.equal(program.inspect(step.binding).type.tag,"Path");
    const {start,end,original,text}=choice.freeze;
    assert.equal(source.slice(start,end),original);
    assert.match(text,/^simp(?:a)? only \[/);
    const frozen=source.slice(0,start)+text+source.slice(end);
    const replay=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>replay.dispose());
    const checked=await replay.check(frozen,`frozen_simp_${index}`);
    assert.equal(checked.complete,true,JSON.stringify(checked.gaps));
  }
  const formatted=formatMathScript(source);
  assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)));
});

test("imported simp registrations are scoped and conflicting named sets fail only on use",async t=>{
  const sources={
    rules_a:`import primes; simp_rule nat_add_zero; simp_set units = [nat_add_zero];`,
    rules_b:`import primes; simp_rule nat_add_zero priority 7; simp_set units = [nat_add_zero];`,
  };
  const programs=[];
  const check=async(source,name)=>{
    const program=new CubicalProgram(await createCubical(),module=>sources[module]??readLibrary(module));
    programs.push(program);
    t.after(()=>program.dispose());
    return program.check(source,name);
  };
  const a=await check(`import rules_a;
    def good(n : Nat) : n + 0 = n { simp; }
    def named(n : Nat) : n + 0 = n { simp only [units]; }
  `,"client_a");
  assert.equal(a.complete,true,JSON.stringify(a.gaps));
  const isolated=await check(`import primes;
    def absent(n : Nat) : n + 0 = n { simp; }
    def explicit(n : Nat) : n + 0 = n { simp only [nat_add_zero]; }
  `,"client_isolated");
  assert.deepEqual(isolated.outputs.map(d=>d.verified),[false,true]);
  const conflict=await check(`import rules_a; import rules_b;
    def default_ok(n : Nat) : n + 0 = n { simp; }
    def ambiguous(n : Nat) : n + 0 = n { simp only [units]; }
    simp_set units = [nat_add_zero];
    def locally_resolved(n : Nat) : n + 0 = n { simp only [units]; }
  `,"client_conflict");
  assert.deepEqual(conflict.outputs.map(d=>d.verified),[true,false,true]);
  assert.match(conflict.outputs[1].reason,/ambiguous/);
  assert.equal(programs.at(-1).simpRegistries.get("client_conflict").defaults.size,1);
  assert.equal([...programs.at(-1).simpRegistries.get("client_conflict").defaults.values()][0].priority,7);
  const reversed=await check(`import rules_b; import rules_a;
    def works(n : Nat) : n + 0 = n { simp; }
  `,"client_reverse_order");
  assert.equal(reversed.complete,true,JSON.stringify(reversed.gaps));
  assert.equal([...programs.at(-1).simpRegistries.get("client_reverse_order").defaults.values()][0].priority,7);
  const shadowed=await check(`import rules_a;
    def nat_add_zero(n : Nat) = n;
    def proven(n : Nat) : n + 0 = n { simp; }
  `,"client_shadowed_rule");
  assert.equal(shadowed.complete,true,JSON.stringify(shadowed.gaps));
  assert.equal(shadowed.links.find(link=>link.role==="simplification witness")?.freeze,null);
});

test("invalid registrations do not enter the default rule set",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def ordinary(n : Nat) = n;
    def useless(n : Nat) : 0 = 0 { rfl; }
    simp_rule ordinary;
    simp_rule useless;
    simp_set bad = [ordinary];
    def missing(n : Nat) : n + 0 = n { simp; }
    def explicit(n : Nat) : n + 0 = n { simp only [nat_add_zero]; }
  `,"invalid_registry");
  assert.equal(result.complete,false);
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,false,true]);
  assert.equal(result.gaps.filter(g=>g.directive).length,3);
  assert.match(result.gaps[0].reason,/homogeneous equality/);
});

test("exclusions remove defaults and hypothesis simplification keeps the source",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    simp_rule nat_add_zero;
    simp_set units = [nat_add_zero];
    def removed(n : Nat) : n + 0 = n { simp without [nat_add_zero]; }
    def removed_set(n : Nat) : n + 0 = n { simp [units] without [units]; }
    def retained(n : Nat, h : n + 0 = n) : n + 0 = n {
      simp at h as normalized;
      exact h;
    }
    def normalized(n : Nat, h : n + 0 = n) : n = n {
      simp at h as shorter;
      exact shorter;
    }
    def global_rejected(n : Nat) : n = n {
      simp only [] at nat_add_zero as bad;
      rfl;
    }
  `,"local_simp");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,true,true,false]);
  assert.match(result.outputs[0].reason,/unresolved equality/);
  assert.match(result.outputs[1].reason,/unresolved equality/);
  assert.match(result.outputs[4].reason,/local hypothesis/);
  assert.deepEqual(result.outputs[3].axioms,[]);
});

test("conditional simp retains an explicitly selected or reflexive premise proof",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def zero_if(n : Nat, h : n = 0) : n + 0 = 0 {
      calc {
        n + 0 = n by nat_add_zero(n);
        _ = 0 by h;
      }
    }
    simp_rule zero_if;
    def selected(n : Nat, h : n = 0) : n + 0 = 0 {
      simp with [h];
    }
    def missing(n : Nat) : n + 0 = 0 {
      simp;
    }
    def reflexive : 0 + 0 = 0 {
      simp;
    }
    def wrong(n : Nat, h : n = 1) : n + 0 = 0 {
      simp with [h];
    }
  `,"conditional_simp");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,false,true,false]);
  assert.deepEqual(result.outputs[1].axioms,[]);
  assert.match(result.outputs[2].reason,/unresolved equality/);
  assert.match(result.outputs[4].reason,/unresolved equality/);
  const reflexiveLink=result.links.find(link=>link.role==="simplification witness"&&link.description?.includes("1 rewrites"));
  assert.ok(reflexiveLink);
});

test("conditional premise simplification is bounded and keeps nested witnesses",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def folded(n : Nat) = n + 0;
    def twice(n : Nat) = folded(n);
    def inner(n : Nat, h : n + 0 = n) : folded(n) = n { exact h; }
    def outer(n : Nat, h : folded(n) = n) : twice(n) = n { exact h; }
    def nested(n : Nat) : twice(n) = n {
      simp only [outer, inner, nat_add_zero];
    }
    def simpa_nested(n : Nat) : twice(n) = n {
      simpa only [outer, inner, nat_add_zero] using refl(n);
    }
    def no_base(n : Nat) : twice(n) = n {
      simp only [outer, inner];
    }
    def no_self(n : Nat) : twice(n) = n {
      simp only [outer];
    }
  `,"nested_premises");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,true,true,false,false]);
  assert.deepEqual(result.outputs[4].axioms,[]);
  assert.deepEqual(result.outputs[5].axioms,[]);
  assert.ok(result.outputs[4].rewriteWork.premiseAttempts>=2);
  assert.ok(result.outputs[4].rewriteWork.premiseProofs>=2);
  assert.ok(result.outputs[4].rewriteWork.premiseRewriteSteps>=2);
  for(const output of result.outputs.slice(6))
    assert.match(output.reason,/unproved premise/);
  assert.ok(result.outputs[6].rewriteWork.premiseAttempts>0);
  assert.equal(result.outputs[6].rewriteWork.premiseProofs,0);
  const step=result.links.find(link=>link.role==="simplification step"
    &&link.description.includes("using outer"));
  assert.match(step?.description??"",/Premise simplified using inner, nat_add_zero/);
  assert.equal(program.inspect(step.binding).type.tag,"Path");
});

test("rewrite errors identify the selected rule and explain an unproved premise",async t=>{
  const reverseSource="def reverse(n : Nat) : n = n { rw [<- refl(n)] at lhs; }";
  const reverseRule=parse(reverseSource).declarations[0].body[0].rules[0];
  assert.equal(reverseSource.slice(reverseRule.start,reverseRule.end),"<- refl(n)");
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`import primes;
    def bad_rw(n : Nat) : n + 0 = n {
      rw [nat_add_zero(n)] at lhs occurrence 2;
    }
    def bad_simp(n : Nat) : n = n {
      simp only [0];
    }
    def zero_if(n : Nat, h : n = 0) : n + 0 = 0 {
      calc {
        n + 0 = n by nat_add_zero(n);
        _ = 0 by h;
      }
    }
    def missing_premise(n : Nat) : n + 0 = 0 {
      simp only [zero_if];
    }
  `;
  const result=await program.check(source,"rule_diagnostics");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,true,false]);
  for(const [name,token] of [["bad_rw","nat_add_zero(n)"],
    ["bad_simp","[0]"],["missing_premise","[zero_if]"]]) {
    const output=result.outputs.find(d=>d.name===name);
    const statementStart=source.indexOf(`def ${name}`);
    const expected=source.indexOf(token,statementStart)+(token.startsWith("[")?1:0);
    assert.equal(output.errorStart,expected,name);
    assert.equal(result.gaps.find(g=>g.name===name).start,expected,name);
  }
  assert.match(result.outputs.find(d=>d.name==="missing_premise").reason,
    /unproved premise at parameter 2.*simp with \[name\]/);
  assert.match(result.outputs.find(d=>d.name==="bad_rw").reason,/occurrence 2.* at \d+:\d+/);
  assert.match(result.outputs.find(d=>d.name==="bad_simp").reason,/homogeneous equality.* at \d+:\d+/);
});
