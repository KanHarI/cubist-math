import test from "node:test";
import assert from "node:assert/strict";
import { scan, numeralAt, numeralExpansion, projectionIndex, tokenStyle } from "../web/source-tokens.mjs";
import { tokenize } from "../web/cubist/parser.mjs";

test("parser and source views share complete operators, literals and projection boundaries", () => {
  const source = "x >= 6.02e-3; y <- 1/2; z := 0b101; p.2.1; // keep 2.5\r\n  5i";
  const scanned = [...scan(source)];
  assert.equal(scanned.map(token => token.text).join(""), source);
  for (const token of scanned) assert.equal(source.slice(token.start, token.end), token.text);
  const code = scanned.filter(token => !/^\s|^\/\//.test(token.text));
  assert.deepEqual(code.map(token => token.text),
    ["x", ">=", "6.02e-3", ";", "y", "<-", "1/2", ";", "z", ":=", "0b101", ";", "p", ".", "2", ".", "1", ";", "5i"]);
  assert.deepEqual(code, tokenize(source).slice(0, -1));
});

test("source scanning preserves incomplete or invalid input while parsing still rejects it", () => {
  const source = "def incomplete := 0b; \u03bb\n";
  assert.equal([...scan(source)].map(token => token.text).join(""), source);
  assert.throws(() => tokenize(source), error => error.offset === source.indexOf("\u03bb"));
});

test("only a newline ends a line comment, including in CRLF source", () => {
  const source = "// note\rdef hidden := 0;\r\ndef visible := 1;";
  assert.equal([...scan(source)][0].text, "// note\rdef hidden := 0;\r");
  assert.deepEqual(tokenize(source).map(token => token.text), ["def", "visible", ":=", "1", ";", "EOF"]);
});

test("numerals from 1 are notation for successors; 0 is the constructor itself", () => {
  assert.equal(numeralExpansion("3"), "succ(succ(succ(0)))");
  assert.equal(numeralExpansion("0"), null);
  assert.equal(numeralExpansion("257"), null);
  assert.equal(tokenStyle("3", numeralExpansion("3")), "macro");
  assert.equal(tokenStyle("0", numeralExpansion("0")), "");
  // A link whose expansion is the token itself is not notation either.
  assert.equal(tokenStyle("0", "0"), "");
  assert.equal(tokenStyle("(", "(1, (2, 3))"), "macro");
  assert.equal(tokenStyle("exact", null), "keyword");
});

test("a projection's index is not a numeral, and the removed have, show and suffices are ordinary names", () => {
  const source = "exact (p.1, q.2.1, 1);";
  const at = text => source.indexOf(text);
  assert.equal(projectionIndex(source, at("1,")), true);
  assert.equal(numeralAt(source, at("1,"), "1"), null);
  assert.equal(numeralAt(source, source.lastIndexOf("1"), "1"), "succ(0)");
  assert.equal(numeralAt(source, at("2."), "2"), null);
  // A quantifier's dot is followed by a space, so a numeral after it expands.
  assert.equal(numeralAt("forall n : Nat. 1 = n", 16, "1"), "succ(0)");
  for (const word of ["have", "show", "suffices"]) assert.equal(tokenStyle(word, null), tokenStyle("name", null), word);
  assert.equal(tokenStyle("let", null), "keyword");
});

test("keywords and generated members keep their style at every occurrence", () => {
  for (const word of ["theory", "extends", "set", "law", "notation", "section", "def", "model", "Hom", "map"])
    assert.equal(tokenStyle(word, null), "keyword", word);
  for (const word of ["deriving", "isomorphisms", "morphisms", "free", "initial", "limits", "additive", "abelian",
    "fold", "gen", "squash", "IsInitial", "IsTerminal"])
    assert.equal(tokenStyle(word, null), "keyword", word);
});

test("renamed bindings and ordinary library names retain the reference style", () => {
  for (const word of ["law_", "set_", "model_", "inverse_", "Nat", "zero", "succ"])
    assert.equal(tokenStyle(word, null), "", word);
});
