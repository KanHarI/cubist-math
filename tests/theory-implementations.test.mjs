import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module=await createCubical();
const base=`import nat; import hlevels; use nat;
theory Base(U < UU0) {
  M : set U;
  op(x : M) : M;
  law self(x : M) : op(x) = op(x);
}`;
const twice=`theory Twice(U < UU0) extends Base {
  step(x : M) : M;
  def op(x : M) : M := step(step(x));
  def self(x : M) : op(x) = op(x) := refl(op(x));
}`;
async function checked(t,source,fixtures={}) {
  const library=sourceReader();
  const result=await checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
  assert.deepEqual(result.result.gaps,[]);
  return result;
}

test("inherited operations and laws compute from new fields through both diamond orders",async t=>{
  for(const parents of ["Twice, Base","Base, Twice"]) {
    const {result}=await checked(t,`${base} ${twice}
      theory Diamond(U < UU0) extends ${parents} {}
      def sample : Diamond(U0) := Diamond.make(M := Nat, M_is_set := nat_is_set, step := succ);
      def shared : sample.twice.base = sample.base { rfl; }
      def through_parent(x : Nat) : sample.base.op(x) = succ(succ(x)) { rfl; }
      print(evaluate(sample.base.op(3)));
      def identity : Diamond.Hom(sample, sample) := Diamond.Hom.id(sample);
      def composed := Diamond.Hom.compose(identity, identity);
      def unchanged : composed.twice.base.map(3) = 3 { rfl; }
      def iso := Diamond.Iso.compose(Diamond.Iso.id(sample), Diamond.Iso.inverse(Diamond.Iso.id(sample)));
      def iso_unchanged : iso.to.base.map(3) = 3 { rfl; }
    `);
    assert.equal(result.prints.at(-1).text,"5");
  }
});

test("implemented operations keep inherited laws as constructor obligations in dependency order",async t=>{
  await checked(t,`${base}
    theory Implemented(U < UU0) extends Base {
      step(x : M) : M;
      def op(y : M) : M := step(y);
    }
    def sample : Implemented(U0) := Implemented.make(M := Nat, M_is_set := nat_is_set,
      step := succ, self := fun (x : Nat) => refl(succ(x)));
    def through_parent(x : Nat) : sample.base.op(x) = succ(x) { rfl; }
  `);
});

test("one group inverse implements both quasigroup divisions and all their laws",async t=>{
  await checked(t,await readFile(new URL("fixtures/theory-group-lattice.cubist",import.meta.url),"utf8"));
});

test("implemented members retain captured names across modules and derived renaming",async t=>{
  const {result}=await checked(t,`import fixture; use nat;
    def advance(n : Nat) : Nat := n;
    theory Renamed(U < UU0) extends twice_ : Twice(op := twice) {}
    def sample : Renamed(U0) := Renamed.make(M := Nat, M_is_set := nat_is_set, value := advance);
    def definition_is_shared(x : Nat) : sample.twice(x) = sample.twice_.op(x) { rfl; }
    print(evaluate(sample.twice(3)));
  `,{
    fixture:`import nat; import hlevels; use nat;
      def advance(n : Nat) : Nat := succ(n);
      theory Base(U < UU0) { M : set U; op(n : Nat) : M; }
      theory Twice(U < UU0) extends Base {
        value(n : Nat) : M;
        def op(n : Nat) : M := value(advance(n));
      }`,
  });
  assert.equal(result.prints.at(-1).text,"4");
});

test("initial and free models refuse missing implemented-member folds before publishing",async t=>{
  const {get}=await checkProgram(t,`${base} ${twice}
    initial Missing : Twice(U0);
    free MissingFree(A : U0) : Twice(U0) on A;
    def healthy : Unit := tt;
  `,{module});
  for(const name of ["Missing","MissingFree"]) {
    assert.equal(get(name).verified,false);
    assert.equal(get(name).code,"E881");
  }
  assert.equal(get("healthy").verified,true);
});

test("incorrect bodies, law proofs, signatures and cycles cannot publish a theory",async t=>{
  const cases=[
    ["def op(x : M) : M := tt;",/Type mismatch/],
    ["def self(x : M) : op(x) = op(x) := tt;",/Type mismatch/],
    ["def op(x : M) : Unit := tt;",/inherited parameter and result types/],
    ["def op(x : M) : M := op(x);",/Cycle among nonrecursive helpers/],
    ["def op(x : M) : M := base.op(x);",/Cycle among nonrecursive helpers/],
    ["def op(x : M) : M := later(x); def later(x : M) : M := op(x);",/Untranslated name/],
    ["def M : U := Unit;",/two fields named M/],
  ];
  for(const [body,reason] of cases) {
    const {result,get,program}=await checkProgram(t,`${base}
      theory Bad(U < UU0) extends Base { ${body} }
      def leaked : U0 := Bad(U0);
      def healthy : Unit := tt;
    `,{module});
    assert.equal(get("Bad").verified,false,body);
    assert.match(get("Bad").reason,reason,body);
    assert.equal(get("leaked").verified,false,body);
    assert.equal(get("healthy").verified,true,body);
    assert.ok(!Object.values(program.symbols).some(symbol=>symbol.name==="Bad.make"),body);
    assert.ok(result.gaps.length>=2,body);
  }
});

test("conflicting implementations and cycles across inherited operations are refused",async t=>{
  for(const [source,reason] of [
    [`theory First(U < UU0) extends Base { def op(x : M) : M := x; }
      theory Second(U < UU0) extends Base { step(x : M) : M; def op(x : M) : M := step(x); }
      theory Bad(U < UU0) extends First, Second {}`,/field named op/],
    [`theory Pair(U < UU0) extends Base { other(x : M) : M; }
      theory Bad(U < UU0) extends Pair { def op(x : M) : M := other(x); def other(x : M) : M := op(x); }`,/Cycle among nonrecursive helpers/],
  ]) {
    const {get}=await checkProgram(t,`${base} ${source} def healthy : Unit := tt;`,{module});
    assert.equal(get("Bad").verified,false);
    assert.match(get("Bad").reason,reason);
    assert.equal(get("healthy").verified,true);
  }
});
