// Operator grouping against the reference's precedence table
// (web/reference/terms.html#precedence), which is its specification: each
// level lists its operators and how they group. Every operator the parser
// knows must be in the table, and every pair and triple of operators, with
// prefix operators and qualified operators x v.(op) y, must group as the
// table says. The expected grouping comes from a reader of the table's own,
// not from the parser's numbers, so a level the parser misreads is caught:
// once ^ bound looser than * on its right, and 2 * 3 ^ 2 read (2 * 3) ^ 2.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { parse, notationOperators } from "../web/cubist/parser.mjs";

const html = readFileSync(new URL("../web/reference/terms.html", import.meta.url), "utf8");
const section = html.slice(html.indexOf('<section id="precedence">'), html.indexOf("</section>", html.indexOf('<section id="precedence">')));
const unescape = text => text.replaceAll("&lt;", "<").replaceAll("&gt;", ">").replaceAll("&amp;", "&");
// Tightest first: a level's rank is higher the tighter it binds.
const table = [...section.matchAll(/<li data-operators="([^"]+)" data-group="(left|right|prefix)"/g)]
  .map(([, operators, group], k, all) => ({ operators: unescape(operators).split(" "), group, rank: all.length - k }));
const binary = new Map(), prefix = new Map();
for (const level of table) for (const operator of level.operators) (level.group === "prefix" ? prefix : binary).set(operator, level);
const binaries = [...binary.keys()];

// The grouping the table gives a flat list of operands and operators, by
// precedence climbing over the table's ranks.
function expected(tokens) {
  let i = 0;
  const operand = () => {
    const token = tokens[i++];
    if (prefix.has(token) && i < tokens.length) return `(${token}${climb(prefix.get(token).rank)})`;
    return token;
  };
  const climb = minimum => {
    let left = operand();
    while (i < tokens.length) {
      const level = binary.get(tokens[i]);
      if (level.rank < minimum) break;
      const operator = tokens[i++];
      const right = climb(level.group === "right" ? level.rank : level.rank + 1);
      left = `(${left} ${operator} ${right})`;
    }
    return left;
  };
  const result = climb(0);
  assert.equal(i, tokens.length);
  return result;
}

// The grouping the parser gives, in the same shape; a qualified operator is
// shown as its operator.
function grouping(source) {
  const shown = node => {
    if (node.kind === "binary") return `(${shown(node.left)} ${node.operator} ${shown(node.right)})`;
    if (node.kind === "pathApply") return `(${shown(node.left)} @ ${shown(node.right)})`;
    if (node.kind === "negation") return `(-${shown(node.operand)})`;
    if (node.kind === "unary") return `(${node.operator}${shown(node.operand)})`;
    if (node.kind === "name") return node.name;
    throw Error(`unexpected ${node.kind} in ${source}`);
  };
  const declaration = parse(`def t := ${source};`).declarations[0];
  return shown(declaration.body?.[0]?.value ?? declaration.value);
}

// Operands a, b, c, d between the operators, with an optional prefix
// before each operand.
const spelled = (operators, prefixes = []) => {
  const tokens = [];
  operators.forEach((operator, k) => { if (prefixes[k]) tokens.push(prefixes[k]); tokens.push("abcd"[k], operator); });
  if (prefixes[operators.length]) tokens.push(prefixes[operators.length]);
  tokens.push("abcd"[operators.length]);
  return tokens;
};
const check = (tokens, source = tokens.join(" ")) => assert.equal(grouping(source), expected(tokens), source);

test("the precedence table lists every operator the parser reads", () => {
  for (const operator of [...notationOperators, "->", "and", "or", "=", ">", ">=", "++", "@", "|", "&"])
    assert.ok(binary.has(operator), `${operator} is in the reference's precedence table`);
  assert.deepEqual([...prefix.keys()].sort(), ["-", "~"]);
});

test("every pair and triple of operators groups as the table says", () => {
  for (const first of binaries) for (const second of binaries) {
    check(spelled([first, second]));
    for (const third of binaries) check(spelled([first, second, third]));
  }
});

test("prefix operators group as the table says", () => {
  for (const operator of binaries) for (const sign of prefix.keys()) {
    check(spelled([operator], [sign]));
    check(spelled([operator], [null, sign]));
    for (const second of binaries) check(spelled([operator, second], [null, sign]));
  }
});

test("a qualified operator groups as the operator does", () => {
  const arithmetic = notationOperators.filter(operator => binary.has(operator));
  for (const first of arithmetic) for (const second of arithmetic) for (const third of arithmetic) {
    const tokens = spelled([first, second, third]);
    // Each choice of operators to qualify.
    for (let mask = 1; mask < 8; mask++) {
      let k = 0;
      const source = tokens.map(token => binary.has(token) ? (mask >> k++ & 1 ? `v.(${token})` : token) : token).join(" ");
      check(tokens, source);
    }
  }
});

test("the documented examples group as stated", () => {
  assert.equal(grouping("x * x ^ n"), "(x * (x ^ n))");
  assert.equal(grouping("x / y ^ n"), "(x / (y ^ n))");
  assert.equal(grouping("x v.(^) y v.(^) z"), "(x ^ (y ^ z))");
  assert.equal(grouping("-x ^ y * z"), "((-(x ^ y)) * z)");
});
