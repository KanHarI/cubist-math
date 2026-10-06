// Arithmetic as written means what it computes (L2.10b): seeded random
// expressions over +, * and ^ on the natural numbers, written with only the
// parentheses the precedence table needs (web/reference/terms.html), in a
// selected notation and with qualified operators, are checked and evaluated
// by the kernel and compared with BigInt arithmetic. Parsing, selection and
// evaluation are tested together, as a user meets them: a misread grouping
// is a wrong number here, not only a different tree.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// A seeded generator, so that a failure reproduces.
let seed = 20261006;
const random = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; };

// The operators, loosest first, as the table orders them; ^ groups to the
// right and the others to the left.
const operators = [
  { operator: "+", rank: 1, apply: (a, b) => a + b },
  { operator: "*", rank: 2, apply: (a, b) => a * b },
  { operator: "^", rank: 3, right: true, apply: (a, b) => a ** b },
];
const valueOf = tree => tree.literal ?? tree.apply(valueOf(tree.left), valueOf(tree.right));
// A tree of up to `depth` operators, with small literals and exponents.
function tree(depth) {
  if (depth === 0 || random(4) === 0) return { literal: BigInt(random(4)) };
  const { operator, rank, right, apply } = operators[random(3)];
  return { operator, rank, right, apply, left: tree(depth - 1), right: operator === "^" ? { literal: BigInt(random(3)) } : tree(depth - 1),
    ...(right ? { rightAssociative: true } : {}) };
}
// The tree written with only the parentheses its grouping needs; each
// operator qualified, x arith.(op) y, where `qualify` says.
function written(node, qualify) {
  if (node.literal !== undefined) return `nat.(${node.literal})`;
  const side = (child, isRight) => {
    const text = written(child, qualify);
    if (child.literal !== undefined) return text;
    const needs = child.rank < node.rank || child.rank === node.rank && (node.rightAssociative ? !isRight : isRight);
    return needs ? `(${text})` : text;
  };
  const operator = qualify() ? `arith.(${node.operator})` : node.operator;
  return `${side(node.left, false)} ${operator} ${side(node.right, true)}`;
}

test("random arithmetic evaluates as BigInt does, in a selection and qualified", async t => {
  const cases = [];
  while (cases.length < 40) {
    const expression = tree(3), value = valueOf(expression);
    if (expression.literal !== undefined || value > 200n) continue;
    const qualified = cases.length % 2 === 1;
    const text = written(expression, () => qualified);
    cases.push({ source: qualified ? text : `arith.(${text})`, value });
  }
  // The examples that once went wrong: ^ inside *, and a qualified ^,
  // which groups to the right (left, it would be 8). Values stay small:
  // a numeral is unary in the kernel.
  cases.push({ source: "arith.(nat.(2) * nat.(3) ^ nat.(2))", value: 18n });
  cases.push({ source: "nat.(2) arith.(^) nat.(1) arith.(^) nat.(3)", value: 2n });
  const source = `import nat;

def power(x, n : Nat) : Nat := induction n return Nat { zero => succ(zero); succ h => mul(x, h); };

notation arith {
  x + y := add(x, y);
  x * y := mul(x, y);
  x ^ y := power(x, y);
}

${cases.map(({ source }) => `print(evaluate(${source}));`).join("\n")}
`;
  const program = new CubicalProgram(await createCubical(), sourceReader());
  t.after(() => program.dispose());
  const result = await program.check(source, "arithmetic");
  assert.deepEqual(result.gaps ?? [], []);
  assert.equal(result.prints.length, cases.length);
  result.prints.forEach((print, k) => assert.equal(print.text, String(cases[k].value), cases[k].source));
});
