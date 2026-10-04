import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";
import { cubicalKinds } from "../web/cubical-kernel.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

// Nat and W as source declarations. The cases whose verdicts and prints are
// the test are cubist-tests/program_types*.cubist (tests/cubist-tests.test.mjs
// compares them); here, what neither shows, and the programs that need an
// option or are generated.

const module=await createCubical();
const check = (t, source, options = {}) => checkProgram(t, source, { module, options });
const ok=result=>assert.equal(result.complete,true,JSON.stringify(result.gaps));
const types=testModule("program_types",{module});

test("Nat, its constructors and W require ordinary source imports",async t=>{
  const {result}=await check(t,`def missing : Nat := 0;
def successor := succ;
def tree := W(U0, U0, Unit, fun (a : Unit) => Void);
`,{prelude:false});
  assert.equal(result.complete,false);
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,false]);
  for(const output of result.outputs)assert.match(output.reason,/Untranslated name/);
});

// Imported Nat and W are source declarations, as the module's prints show:
// no definition the program holds uses a retired primitive, and they build
// with constructors and eliminators.
test("imported Nat and W use no retired primitive", async () => {
  const { program } = await types();
  const tags = new Set(), seen = new WeakSet();
  const visit = value => { if (!value || typeof value !== "object" || seen.has(value)) return; seen.add(value); if (value.tag) tags.add(value.tag); Object.values(value).forEach(visit); };
  for (const [name] of program.kernel.definitions) { const view = program.inspect(name); visit(view.expression); visit(view.type); }
  for (const tag of ["Nat", "Zero", "Succ", "NatRec", "W", "Sup", "WRec"]) assert.equal(tags.has(tag), false, tag);
  assert.ok(tags.has("Con")); assert.ok(tags.has("Elim"));
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
  // The retired kinds and instructions have no names, and their numbers
  // stay reserved: the C kernel refuses each.
  for(const kind of ["Nat","Zero","Succ","NatRec","W","Sup","WRec","Pushout","PushLeft","PushRight","PushPath","PushElim"])
    assert.throws(()=>program.kernel.term(kind),/Unsupported cubical constructor/);
  const kinds=cubicalKinds.flatMap((name,tag)=>name===null?[tag]:[]);
  assert.equal(kinds.length,12);
  for(const tag of kinds) {
    assert.equal(module._cb_term(program.kernel.handle,tag,0,0,0,0,0),0,`kind ${tag}`);
    assert.match(program.kernel.error(),/Unknown term constructor/);
    module._cb_clear_error(program.kernel.handle);
  }
  const opcodes=instructions.flatMap((name,opcode)=>name===null?[opcode]:[]);
  assert.equal(opcodes.length,11);
  for(const opcode of opcodes) {
    assert.equal(module._cb_instr(program.kernel.handle,opcode,0,0,0,0),0,`opcode ${opcode}`);
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

