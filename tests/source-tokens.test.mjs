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
  const source = `theory Field(U < UU0) extends CommRing {
  P : prop U;
  inv(x : R) : R notation x * y;
  law zero_ne_one : zero = one -> Void;
}

theory Ring extends additive : Group(one := zero) {
}

section (n : Nat) {
  def f(section : Nat) : Nat {
    use G;
    exact zero;
  }
}

def g(sort : Nat) := succ(zero);`;
  // The word's nth occurrence as a whole word.
  const style = (word, nth = 0) => {
    const at = [...source.matchAll(new RegExp(`\\b${word}\\b`, "g"))][nth].index;
    return tokenStyle(word, null, keywordAt(source, at, word));
  };
  for (const word of ["theory", "extends", "prop", "notation", "law", "section"]) assert.equal(style(word), "keyword", word);
  // Inside a theory, and in a parent's renaming, zero is a field.
  assert.equal(style("zero"), "");
  assert.equal(style("zero", 1), "");
  // Elsewhere, the words are names: a parameter named section or sort. open
  // is reserved, a keyword everywhere.
  assert.equal(style("section", 1), "");
  assert.equal(style("use"), "keyword");
  assert.equal(style("sort"), "");
  // Outside a theory, zero and succ are Nat's constructors, unless they link
  // to a definition, as a ring's zero after open does.
  assert.equal(style("zero", 2), "keyword");
  assert.equal(style("succ"), "keyword");
  assert.equal(tokenStyle("zero", null, linkedWord("zero", { role: "definition" })), "");
  assert.equal(tokenStyle("zero", null, linkedWord("zero", { role: "local" })), "keyword");
});

test("a theory's words keep their roles past comments and nested braces, and are names where the parser reads names", () => {
  const source = `import nat;
import hlevels;
theory Ring(U < UU0) {
  // Carrier
  R : set U;
  zero : R;
  // Identity }
  law identity(x : R) : x = x;
  law trivial : (match 0 return R { zero => zero; succ(k) => zero; }) = zero;
  add(x, y : R) : R notation x + y;
  law sum(notation : R) : notation + zero = notation + zero;
}
theory T(U < UU0) { M : set U; law : M; sort : M; notation : M; }
def f(A : Ring(U0)) : A.R {
  // Select model
  use A;
  exact zero;
}`;
  // The word's nth occurrence as a whole word, outside comments.
  const code = source.replace(/\/\/.*/g, line => " ".repeat(line.length));
  const style = (word, nth = 0) => {
    const at = [...code.matchAll(new RegExp(`\\b${word}\\b`, "g"))][nth].index;
    return tokenStyle(word, null, keywordAt(source, at, word));
  };
  // A comment before a field or a statement, and a brace in one, change nothing.
  assert.equal(style("set"), "keyword");
  assert.equal(style("law"), "keyword");
  assert.equal(style("use"), "keyword");
  // A match's braces in a law are not the theory's: the fields after it are
  // still fields, zero among them.
  assert.equal(style("law", 2), "keyword");
  for (let nth = 0; nth < 7; nth++) assert.equal(style("zero", nth), "", `zero ${nth}`);
  assert.equal(style("notation"), "keyword");
  // A field or a parameter named law, sort or notation is a name.
  for (let nth = 1; nth < 5; nth++) assert.equal(style("notation", nth), "", `notation ${nth}`);
  assert.equal(style("law", 3), "");
  assert.equal(style("sort"), "");
  assert.equal(style("set", 1), "keyword");
  // After the theories, zero is Nat's constructor, unless it links to a
  // definition, as the ring's zero after open A does.
  assert.equal(style("zero", 7), "keyword");
});

test("a theory's header comes before extends, and a carrier's h-level is a keyword (L2.4c)", () => {
  const source = `theory Ring(U < UU0) extends additive : Group(one := zero) {
  R : set U;
  P : prop U;
  L : U;
  set : U;
  point : set;
  law l(x : R) : x = x;
}
def f(set : Nat, prop : Nat) := set;`;
  const style = (word, nth = 0) => {
    const at = [...source.matchAll(new RegExp(`\\b${word}\\b`, "g"))][nth].index;
    return tokenStyle(word, null, keywordAt(source, at, word));
  };
  assert.equal(style("extends"), "keyword");
  assert.equal(style("zero"), "");
  assert.equal(style("set"), "keyword");
  assert.equal(style("prop"), "keyword");
  assert.equal(style("law"), "keyword");
  // A field named set, a type written set, and parameters named set and prop are names.
  for (let nth = 1; nth < 5; nth++) assert.equal(style("set", nth), "", `set ${nth}`);
  assert.equal(style("prop", 1), "");
});

test("notation declares a named notation where an item starts, and use selects one (L2.10a)", () => {
  const source = `notation nat {
  x + y := add(x, y);
}
def f(notation, use : Nat) : Nat {
  use nat;
  exact notation;
}`;
  const style = (word, nth = 0) => {
    const at = [...source.matchAll(new RegExp(`\\b${word}\\b`, "g"))][nth].index;
    return tokenStyle(word, null, keywordAt(source, at, word));
  };
  assert.equal(style("notation"), "keyword");
  assert.equal(style("notation", 1), "");
  assert.equal(style("use"), "");
  assert.equal(style("use", 1), "keyword");
});
