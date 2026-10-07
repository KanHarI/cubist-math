import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { expandedSyntax } from "../web/cubist/tuples.mjs";
import { checkTestModule } from "./check-program.mjs";

// `induction` on any declared type. Its cases, refusals and warning are
// cubist-tests/declared_induction.cubist, and how an eliminator prints is
// cubist-tests/induction_printed.cubist, whose comments state each error,
// warning and output (tests/cubist-tests.test.mjs); here, that the source the
// module writes back is what its prints show.
test("a printed eliminator, written back, is the source the module checks", async t => {
  const { source, result } = await checkTestModule(t, "induction_printed");
  const values = Object.fromEntries(parse(source).declarations.filter(d => d.value)
    .map(d => [d.name.text, expandedSyntax(d.value)]));
  const [size, length] = result.prints.map(print => print.text);
  const syntax = text => expandedSyntax(parse(text, true));
  assert.equal(values.size_again, syntax(size));
  // An erased universe prints as __U, which the elaborator asks to replace;
  // written out, the instance checks.
  assert.match(length, /__U/);
  assert.equal(values.length_again, syntax(length));
  assert.equal(values.length_written, syntax(length.replace("__U", "U0")));
});
