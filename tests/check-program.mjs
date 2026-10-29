// A fresh program that checks one source, for tests, disposed of when the
// test ends. With the result come `get(name)`, a declaration that must be
// there, and `verdicts`: each declaration's name, mapped to true when it
// verified and otherwise to its reason. Without a `module`, the program has a
// WASM instance of its own.
import assert from "node:assert/strict";
import { after } from "node:test";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

export async function checkProgram(t, source, options) {
  return checked(dispose => t.after(dispose), source, options);
}
async function checked(disposeLater, source, { module, reader = sourceReader(), name = "main", options = {} } = {}) {
  const program = new CubicalProgram(module ?? await createCubical(), reader, options);
  disposeLater(() => program.dispose());
  const result = await program.check(source, name);
  const get = declaration => {
    const found = result.outputs.find(output => output.name === declaration);
    assert.ok(found, `no declaration ${declaration}`);
    return found;
  };
  const verdicts = Object.fromEntries(result.outputs.map(output => [output.name, output.verified ? true : output.reason]));
  return { program, result, get, verdicts };
}

// A Cubist test, cubist-tests/NAME.cubist, checked as the command line checks
// the file: its imports resolve in cubist-tests/, then library/, then the
// archive. It gives what checkProgram does, and the module's source.
export async function checkTestModule(t, name, options = {}) {
  return testModuleChecked(dispose => t.after(dispose), name, options);
}
async function testModuleChecked(disposeLater, name, options) {
  const path = fileURLToPath(new URL(`../cubist-tests/${name}.cubist`, import.meta.url));
  const source = await readFile(path, "utf8");
  return { source, ...await checked(disposeLater, source, { reader: sourceReader({ path }), name, ...options }) };
}

// A Cubist test module checked once for all the tests of a file: call the
// result to have the check, made on first use; the program is disposed of
// when the file's tests end.
export function testModule(name, options = {}) {
  let result = null;
  after(async () => { if (result) (await result).program.dispose(); });
  return () => result ??= testModuleChecked(() => {}, name, options);
}
