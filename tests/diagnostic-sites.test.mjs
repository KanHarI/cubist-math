import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {checkProgram} from "./check-program.mjs";

const module=await createCubical();
const bad="// The imported module has its own coordinates.\ndef broken := ;";

test("root and imported parse failures retain their source-qualified location through recovery",async t=>{
  let message;try {parse(bad);}catch(error) {message=error.message;}
  let dependency=bad;
  const program=new CubicalProgram(module,async()=>dependency);
  t.after(()=>program.dispose());
  await assert.rejects(program.check(bad,"authored"),error=>{
    assert.equal(error.message,message);
    assert.equal(error.diagnostic.kind,"parse");
    assert.equal(error.diagnostic.primary.module,"authored");
    assert.equal(error.diagnostic.primary.start,error.offset);
    assert.equal(error.offset,bad.indexOf(";"));
    return true;
  });
  const failed=await program.check("import dependency; def good := tt;","client");
  const gap=failed.gaps.find(gap=>gap.module==="dependency");
  assert.equal(gap.start,bad.indexOf(";"));
  assert.equal(gap.diagnostic.primary.module,"dependency");
  assert.equal(gap.diagnostic.primary.start,gap.start);
  assert.equal(JSON.parse(JSON.stringify(gap)).diagnostic.kind,"parse");
  dependency="def repaired := tt;";
  const repaired=await program.check("import dependency; def good := repaired;","client");
  assert.equal(repaired.complete,true);
  assert.deepEqual(repaired.gaps,[]);
});

test("duplicate declarations keep their diagnostic site without replacing the original symbol",async t=>{
  const source="def original := tt; def original := Unit;";
  const {program,result}=await checkProgram(t,source,{module});
  const gap=result.gaps.find(gap=>gap.duplicate);
  assert.equal(gap.diagnostic.primary.module,"main");
  assert.equal(gap.diagnostic.primary.start,source.lastIndexOf("original"));
  assert.equal(gap.start,gap.diagnostic.primary.start);
  assert.equal(program.symbols.main__original.verified,true);
  assert.equal(program.symbols.main__original.start,0);
});
