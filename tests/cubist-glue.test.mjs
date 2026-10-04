import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkTestModule, checkProgram } from "./check-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// Glue types, glue and unglue in Cubist source (cubist-tests/glue.cubist,
// whose comments state each refusal: tests/cubist-tests.test.mjs).
// A printed path carries no type: the declaration gives it.
test("a Glue line prints as the source writes it, and the printed source checks", async t => {
  const { program } = await checkTestModule(t, "glue");
  const [printed] = (await new ReplSession(program, { base: "glue" }).run("evaluate glued_line;")).map(output => output.text);
  assert.match(printed, /^fun \(A : U0\) => path i => Glue\(A, face\(i, 0, A, \(fun \(x : A\) => x, .*\)\), face\(i, 1, A, /);
  const { result, verdicts } = await checkProgram(t, `import glue;
def again : forall A : U0. A = A := ${printed};
def same : glued_line = again { rfl; }`, { reader: sourceReader({ path: new URL("../cubist-tests/main.cubist", import.meta.url).pathname }) });
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});
