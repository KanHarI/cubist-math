// Re-run the committed semantic witnesses on #219's pinned frontend. The
// current WASM is usable only when the archived native inputs match its stamp.
// node tools/capture-bindings-history.mjs REPORT.json
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtemp, symlink, rm, writeFile, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import create from "../web/dist/cubical.mjs";
import { buildStamp, assertFreshBuild } from "./build-stamp.mjs";
import { hashEntries, digestFormats } from "./frontend-generation-evidence.mjs";
import { bindingCases } from "../tests/fixtures/capture-bindings.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const destination = process.argv[2], revision = "d3d8f21eb3a2e8e64fbf5ec89ce2fb4b192aaa13";
if (!destination) throw Error("Usage: node tools/capture-bindings-history.mjs REPORT.json");
assertFreshBuild();
const directory = await mkdtemp(join(tmpdir(), "cubist-capture-history-"));
try {
  const archive = execFileSync("git", ["archive", revision, "web", "tools", "library", "archive", "kernel", "wasm", "Makefile", "package.json"],
    {cwd:root, maxBuffer:64*1024*1024});
  execFileSync("tar", ["-x", "-C", directory], {input:archive});
  await symlink(join(root,"web/dist"), join(directory,"web/dist"), "dir");
  buildStamp(pathToFileURL(`${directory}/`)).assertFreshBuild();
  const { CubicalProgram } = await import(pathToFileURL(join(directory,"web/cubical-program.mjs")));
  const { sourceReader } = await import(pathToFileURL(join(directory,"tools/module-sources.mjs")));
  const wasm = await create(), library = sourceReader(), observations = [];
  const ids = ["recursive-wrapper-same-module", "ordered-header", "imported-pattern-rename",
    "recursive-bare-same-module", "family-domain-helper-absent"];
  const expected = {
    "recursive-wrapper-same-module": {clients:{captured:true, independent:true}, gaps:[]},
    "ordered-header": {clients:{identity:false,param:true,captured_param:false,N:false,generated:false,captured:false},
      gaps:[["identity","E817",true],["captured_param","E606",true],["N","E854",true],["generated","E340",true],["captured","E340",true]]},
    "imported-pattern-rename": {clients:{meaning:false,independent:true}, gaps:[["C","E801",false],["meaning","E340",true]]},
    "recursive-bare-same-module": {clients:{captured:true,independent:true}, gaps:[]},
    "family-domain-helper-absent": {clients:{member:false,captured:false,independent:true},
      gaps:[["T","E343",true],["member","E340",true],["captured","E340",true]]},
  };
  for (const id of ids) {
    const c = bindingCases.find(c => c.id === id);
    assert.ok(c, `missing committed witness ${id}`);
    const program = new CubicalProgram(wasm, (name, importer) => c.fixtures?.[name] ?? library(name, importer));
    try {
      const result = await program.check(c.source, "main");
      assert.deepEqual(result.gaps.filter(gap => gap.module !== "main"), [], `${id}: imported source must check`);
      const clients = Object.fromEntries(c.clients.map(name => {
        const output = result.outputs.find(output => output.name === name);
        assert.ok(output, `${id}: missing client ${name}`);
        assert.deepEqual(output.axioms ?? [], [], `${id}: no additional assumptions`);
        return [name, output.verified];
      }));
      observations.push({id, sourceDigest:hashEntries(Object.entries(program.sources)), clients,
        gaps:result.gaps.map(({module,name,code,start,end}) => ({module,name,code,start,end,
          rangeInPrimarySource:start == null || start >= 0 && start <= program.sources[module].length &&
            (end == null || end >= start && end <= program.sources[module].length)}))});
    } finally { program.dispose(); }
  }
  for (const {id, clients, gaps} of observations) assert.deepEqual({clients,
    gaps:gaps.map(gap => [gap.name,gap.code,gap.rangeInPrimarySource])}, expected[id], `${id}: pinned historical behavior changed`);
  const report = {version:1, revision, witnessesRevision:execFileSync("git",["rev-parse","HEAD"],{cwd:root,encoding:"utf8"}).trim(),
    dirty:!!execFileSync("git",["status","--porcelain"],{cwd:root,encoding:"utf8"}).trim(), digestFormats,
    witnessDigest:hashEntries([["tests/fixtures/capture-bindings.mjs", await readFile(join(root,"tests/fixtures/capture-bindings.mjs"))]]),
    build:JSON.parse(await readFile(join(root,"web/dist/build-stamp.json"),"utf8")), observations};
  await writeFile(resolve(destination), JSON.stringify(report,null,2)+"\n");
  console.log(JSON.stringify(observations,null,2));
} finally { await rm(directory,{recursive:true,force:true}); }
