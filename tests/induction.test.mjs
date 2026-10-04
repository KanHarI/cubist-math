import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { checkTestModule } from "./check-program.mjs";

// `induction` on any declared type. Its cases, refusals and warning are
// cubist-tests/induction.cubist, and how an eliminator prints is
// cubist-tests/induction_printed.cubist, whose comments state each error,
// warning and output (tests/cubist-tests.test.mjs); here, that the source the
// module writes back is what its prints show.
const collapsed = text => text.replace(/\s+/g, " ").trim();

test("a printed eliminator, written back, is the source the module checks", async t => {
  const { source, result } = await checkTestModule(t, "induction_printed");
  const values = Object.fromEntries(parse(source).declarations.filter(d => d.value)
    .map(d => [d.name.text, collapsed(source.slice(d.valueStart, d.valueEnd))]));
  const [size, length] = result.prints.map(print => collapsed(print.text));
  assert.equal(values.size_again, size);
  // An erased universe prints as __U, which the elaborator asks to replace;
  // written out, the instance checks.
  assert.match(length, /__U/);
  assert.equal(values.length_again, length);
  assert.equal(values.length_written, length.replace("__U", "U0"));
});
