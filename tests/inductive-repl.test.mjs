// An inductive declaration entered in a REPL session (L2.1), with the
// experimental option on, is used by the entries after it.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const texts = results => results.map(result => `${result.kind}: ${result.text}`);

test("a REPL session declares a type and uses it in later entries", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false, experimental: ["h1"] });
  t.after(() => program.dispose());
  const repl = new ReplSession(program);
  const declared = texts(await repl.run("inductive N { z; s(n : N); }"));
  assert.ok(declared.some(line => /^defined: N/.test(line)), declared.join("\n"));
  assert.deepEqual(texts(await repl.run("let two : N := s(s(z));")), ["defined: two : N"]);
  assert.deepEqual(texts(await repl.run("typeof two;")), ["type: N"]);
});
