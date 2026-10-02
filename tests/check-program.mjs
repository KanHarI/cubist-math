// A fresh program that checks one source, for tests, disposed of when the
// test ends. With the result come `get(name)`, a declaration that must be
// there, and `verdicts`: each declaration's name, mapped to true when it
// verified and otherwise to its reason. Without a `module`, the program has a
// WASM instance of its own.
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

export async function checkProgram(t, source, { module, reader = sourceReader(), name = "main", options = {} } = {}) {
  const program = new CubicalProgram(module ?? await createCubical(), reader, options);
  t.after(() => program.dispose());
  const result = await program.check(source, name);
  const get = declaration => {
    const found = result.outputs.find(output => output.name === declaration);
    assert.ok(found, `no declaration ${declaration}`);
    return found;
  };
  const verdicts = Object.fromEntries(result.outputs.map(output => [output.name, output.verified ? true : output.reason]));
  return { program, result, get, verdicts };
}
