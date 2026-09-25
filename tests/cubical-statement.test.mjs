import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/mathscript/parser.mjs";
import { sourceStatement } from "../web/cubical-statement.mjs";
import { readFile } from "node:fs/promises";
const text = parts => parts.map(part => part.text).join("");

test("source summaries separate the conclusion from named parameters without elaboration artifacts", async () => {
  const source = await readFile(new URL("../archive/first-library/complex_deformation.cubist", import.meta.url), "utf8");
  const declaration = parse(source).declarations.find(d => d.name.text === "complex_deformation_at_one");
  const statement = sourceStatement(source, declaration, [{ start: declaration.params[0].name.start, binding: "local_F" }]);
  assert.equal(text(statement.conclusion), "complex_linear_deformation(F, addF, mulF, one, z, error) = complex_add(F, addF, z, error)");
  assert.equal(statement.parameters.length, 12);
  assert.equal(text(statement.parameters[3].type), "F -> F -> F");
  assert.equal(text(statement.parameters[8].type), "StrictOrder(F, lt)");
  assert.equal(statement.parameters[0].name[0].binding, "local_F");
});

test("statement fragments retain explicit equality and skip comments without hiding syntax", () => {
  const source = `def t(A : U0, x : A) : x // equality comment
    =[A] x { exact refl(x); }`;
  const statement = sourceStatement(source, parse(source).declarations[0]);
  assert.equal(text(statement.conclusion), "x =[A] x");
  assert.equal(sourceStatement("def a := 0;", parse("def a := 0;").declarations[0]), null);
});
