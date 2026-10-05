import test from "node:test";
import assert from "node:assert/strict";
import { numeralAt, numeralExpansion, projectionIndex, tokenStyle, keywordAt, linkedWord } from "../web/source-tokens.mjs";

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

test("a theory's words are keywords where they stand, and its fields zero and succ are names", () => {
  const source = `theory Field extends CommRing {
  sort P : prop;
  inv(x : R) : R notation x * y;
  law zero_ne_one : zero = one -> Void;
}

theory Ring extends additive : Group(one := zero) {
}

section (n : Nat) {
  def f(section : Nat, open : Nat) : Nat {
    open G;
    exact zero;
  }
}

def g(sort : Nat) := succ(zero);`;
  // The word's nth occurrence as a whole word.
  const style = (word, nth = 0) => {
    const at = [...source.matchAll(new RegExp(`\\b${word}\\b`, "g"))][nth].index;
    return tokenStyle(word, null, keywordAt(source, at, word));
  };
  for (const word of ["theory", "extends", "sort", "prop", "notation", "law", "section"]) assert.equal(style(word), "keyword", word);
  // Inside a theory, and in a parent's renaming, zero is a field.
  assert.equal(style("zero"), "");
  assert.equal(style("zero", 1), "");
  // Elsewhere, the words are names: a parameter named section, open or sort.
  assert.equal(style("section", 1), "");
  assert.equal(style("open"), "");
  assert.equal(style("open", 1), "keyword");
  assert.equal(style("sort", 1), "");
  // Outside a theory, zero and succ are Nat's constructors, unless they link
  // to a definition, as a ring's zero after open does.
  assert.equal(style("zero", 2), "keyword");
  assert.equal(style("succ"), "keyword");
  assert.equal(tokenStyle("zero", null, linkedWord("zero", { role: "definition" })), "");
  assert.equal(tokenStyle("zero", null, linkedWord("zero", { role: "local" })), "keyword");
});
