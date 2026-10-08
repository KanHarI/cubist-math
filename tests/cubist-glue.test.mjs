import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { expandedSyntax } from "../web/cubist/tuples.mjs";
import { checkTestModule } from "./check-program.mjs";

// Glue types, glue and unglue in Cubist source (cubist-tests/glue_.cubist,
// whose comments state each refusal: tests/cubist-tests.test.mjs). A Glue
// line prints as the source writes it, and cubist-tests/glue_printed.cubist
// writes the print back; here, that its copy is what the print shows.
test("a Glue line prints as the source writes it, and the module writes that source back", async t => {
  const { source, result } = await checkTestModule(t, "glue_printed");
  const [printed] = result.prints.map(print => print.text);
  assert.match(printed, /^fun \(A : U0\) => path i => Glue\(A, face\(i, 0, A, \(fun \(x : A\) => x, .*\)\), face\(i, 1, A, /);
  // A definition with a stated type keeps its value as the block's exact.
  const again = parse(source).declarations.find(d => d.name.text === "again");
  assert.equal(expandedSyntax(again.body[0].value), expandedSyntax(parse(printed, true)));
});
