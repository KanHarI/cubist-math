import { parse, tokenize } from "./parser.mjs";

// Source coordinates and notation do not belong to the expanded syntax tree.
export function expandedSyntax(tree) {
  return JSON.stringify(tree, (key, value) => [
    "start", "end", "operatorStart", "operatorEnd", "definitionStart", "modifierStart", "valueStart", "valueEnd",
    "tupleStart", "tupleEnd", "syntheticTuplePair",
  ].includes(key) ? undefined : value);
}

// Remove only parentheses enclosing a pair in another pair's right component.
// Names, comments, left-nested pairs and function argument lists stay in place.
// The parser already expands tuple notation, allowing a structural safety check.
export function linearizeTuples(source) {
  const tokens = tokenize(source);
  if (tokens[0].text === "construction") return { source, count: 0 };
  const syntax = parse(source), starts = new Map(), ends = new Map(), matching = new Map(), stack = [];
  tokens.forEach((token, index) => {
    starts.set(token.start, index); ends.set(token.end, index);
    if (token.text === "(") stack.push(index);
    if (token.text === ")") matching.set(stack.pop(), index);
  });
  const remove = new Set(), visited = new Set();
  let count = 0;
  function visit(node) {
    if (!node || typeof node !== "object" || visited.has(node)) return;
    visited.add(node);
    if (node.kind === "pair" && node.right.kind === "pair" && !node.right.syntheticTuplePair) {
      let left = starts.get(node.right.start), right = ends.get(node.right.end);
      if (left === undefined || right === undefined || matching.get(left) !== right)
        throw new Error("Cannot locate a right-hand pair's enclosing parentheses.");
      // Grouping parentheses may wrap the binary pair more than once.
      while (tokens[left]?.text === "(" && matching.get(left) === right) {
        if (!remove.has(tokens[left].start)) count++;
        remove.add(tokens[left++].start); remove.add(tokens[right--].start);
      }
    }
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) value.forEach(visit);
      else if (value && typeof value === "object") visit(value);
    }
  }
  visit(syntax);
  if (!count) return { source, count };
  const rewritten = source.split("").filter((_, index) => !remove.has(index)).join("");
  if (expandedSyntax(parse(rewritten)) !== expandedSyntax(syntax))
    throw new Error("Tuple linearization changed the expanded syntax tree.");
  return { source: rewritten, count };
}
