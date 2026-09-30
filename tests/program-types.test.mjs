import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";

const module=await createCubical();
async function check(t,source,options={}) {
  const program=new CubicalProgram(module,sourceReader(),options);
  t.after(()=>program.dispose());
  const result=await program.check(source,"main");
  return {program,result};
}
const ok=result=>assert.equal(result.complete,true,JSON.stringify(result.gaps));

test("Nat, its constructors and W require ordinary source imports",async t=>{
  const {result}=await check(t,`def missing : Nat := 0;
def successor := succ;
def tree := W(U0, U0, Unit, fun (a : Unit) => Void);
`,{prelude:false});
  assert.equal(result.complete,false);
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,false]);
  for(const output of result.outputs)assert.match(output.reason,/Untranslated name/);
});

test("Nat is an ordinary name that can be bound or shadowed",async t=>{
  const {result}=await check(t,`def identity(Nat : U0, x : Nat) := x;
def Nat := Unit;
def point : Nat := tt;
`);
  ok(result);
});

test("imported Nat has generic constructors, literals and elimination",async t=>{
  const {program,result}=await check(t,`import nat;
def two : Nat := 2;
def double(n : Nat) : Nat := match n { zero => zero; succ(k) => succ(succ(double(k))); };
def four : double(two) = 4 { rfl; }
def predecessor(n : Nat) := induction n as k return Nat { zero => 0; succ h => k; };
def pred_two : predecessor(two) = 1 { rfl; }
`);
  ok(result);
  assert.equal(program.inspect("main__two").type.tag,"Sort");
  const tags=new Set(),seen=new WeakSet();
  const visit=value=>{if(!value||typeof value!=="object"||seen.has(value))return;seen.add(value);if(value.tag)tags.add(value.tag);Object.values(value).forEach(visit);};
  for(const [name] of program.kernel.definitions){const view=program.inspect(name);visit(view.expression);visit(view.type);}
  for(const tag of ["Nat","Zero","Succ","NatRec","W","Sup","WRec"])assert.equal(tags.has(tag),false,tag);
  assert.ok(tags.has("Con"));assert.ok(tags.has("Elim"));
});

test("constructor shadowing does not retarget literals in imported Nat",async t=>{
  const {result}=await check(t,`import nat;
inductive N { zero; succ(n : N); }
def ordinary : N := succ(zero);
def literal : Nat := 2;
def same : literal = 2 { rfl; }
`);
  ok(result);
});

test("source W and its dependent eliminator compute at finite universes",async t=>{
  const {result}=await check(t,`import nat;
import w;
def Tree := W(U1, U0, Unit, fun (a : Unit) => Void);
def leaf : Tree := sup(tt, fun (v : Void) => typed(Tree, absurd(v)));
def result := wrec(U1, U0, U0, Unit, (fun (a : Unit) => Void),
  (fun (t : Tree) => Nat),
  (fun (a : Unit, children : Void -> Tree, ih : Void -> Nat) => 2), leaf);
def computed : result = 2 { rfl; }
`);
  ok(result);
});

test("a fresh driver replays a level binder after a conflicting term entry",async t=>{
  const {program,result}=await check(t,`import w; def witness : Unit := tt;
`);
  ok(result);
  const reference=program.kernel.definitions.get("w__wrec");
  const {value,type}=program.kernel.definition(reference);
  const node=program.kernel.node(value);
  const driver=new InstructionDriver(program.kernel);
  const unit=driver.graph.unit();
  driver.graph.extend(unit,program.kernel.symbolName(node.payload));
  assert.doesNotThrow(()=>new InstructionDriver(program.kernel).check(value,type));
});

test("the producer refuses the reserved primitive syntax and instruction slots",async t=>{
  const {program,result}=await check(t,"def retained : Unit := tt;");
  ok(result);
  for(const kind of ["Nat","Zero","Succ","NatRec","W","Sup","WRec"])
    assert.throws(()=>program.kernel.term(kind),/Unknown term constructor/);
  for(const operation of ["nat","zero","succ","natElim","w","sup","wElim"]) {
    const opcode=instructions.indexOf(operation);
    assert.ok(opcode>0,operation);
    assert.equal(module._cb_instr(program.kernel.handle,opcode,0,0,0,0),0,operation);
    assert.match(program.kernel.error(),/Unknown instruction/);
    module._cb_clear_error(program.kernel.handle);
  }
});

test("imported Nat keeps a folded 2^22 value and discards it without unary evaluation",async t=>{
  let source=`def double(n : Nat) : Nat := match n { zero => 0; succ(k) => succ(succ(double(k))); };\ndef power0 : Nat := 1;\n`;
  for(let n=1;n<=22;n++)source+=`def power${n} : Nat := double(power${n-1});\n`;
  source+="def folded : power22 = power22 { rfl; }\ndef discarded := (fun (unused : Nat) => 0)(power22);\ndef zero_result : discarded = 0 { rfl; }\n";
  const {program,result}=await check(t,source);
  ok(result);
  assert.ok(program.kernel.arena().nodes<30000);
  assert.equal(program.inspect("main__power22").expression.tag,"App");
  assert.equal(program.inspect("main__discarded",{normalize:true}).expression.index,0);
});

test("an ordinary W declaration at a fixed higher universe checks",async t=>{
  const {result}=await check(t,`inductive BigW(A : UU0, B : A -> UU0) : UU0 {
    big_sup(a : A, children : B(a) -> BigW(A,B));
  }
  def Small := BigW(Unit, fun (a : Unit) => Void);
  def leaf : Small := big_sup(tt, fun (v : Void) => typed(Small, absurd(v)));
  `);
  ok(result);
});
