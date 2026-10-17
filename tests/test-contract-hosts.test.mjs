import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {execFile} from "node:child_process";
import {promisify} from "node:util";
import {mkdtemp,readFile,writeFile,rm} from "node:fs/promises";
import {fileURLToPath} from "node:url";
import {basename,join} from "node:path";
import {stripped} from "../tools/inline-errors.mjs";

const run=promisify(execFile),cwd=fileURLToPath(new URL("../",import.meta.url));
const environment={...process.env};delete environment.NODE_TEST_CONTEXT;

test("explicit source case selection runs its ID and rejects empty, duplicate and missing selections",async()=>{
  const select=ids=>run(process.execPath,["--test","tests/cubist-contracts.test.mjs"],
    {cwd,env:{...environment,CUBIST_TEST_CASES:JSON.stringify(ids)}});
  const {stdout}=await select(["generation.hom_universe.too_low"]);
  assert.match(stdout,/generation\.hom_universe\.too_low/);
  assert.match(stdout,/tests 1\b/);
  for(const ids of [[],["missing"],["generation.hom_universe.theory","generation.hom_universe.theory"]])
    await assert.rejects(select(ids),error=>error.code===1&&/selection must be|Unknown test case/.test(error.stdout));
});

test("comment writer preserves semantic expectations and refuses a broken contract before writing",async t=>{
  const directory=await mkdtemp(join(cwd,"build/pragma-writer-"));
  t.after(()=>rm(directory,{recursive:true,force:true}));
  const name=`../build/${basename(directory)}/fixture`,path=join(directory,"fixture.cubist");
  const source="# test(refusal)\n# expect_error(E606)\ndef bad : Void := tt;\n";
  await writeFile(path,source);
  const write=()=>run(process.execPath,["tools/inline-errors.mjs","--write",name],{cwd,env:environment});
  await write();
  const annotated=await readFile(path,"utf8");
  assert.match(annotated,/\/\/ Error: E606:/);
  assert.equal(stripped(annotated),source);
  const broken=annotated.replace("# expect_error(E606)","# expect_error(E343)");
  await writeFile(path,broken);
  await assert.rejects(write(),error=>error.code===1&&/Expected one owned E343/.test(error.stderr));
  assert.equal(await readFile(path,"utf8"),broken);
});
