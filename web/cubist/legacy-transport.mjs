import { parse, tokenize, languageKeywords } from "./parser.mjs";

// Read a retired transport spelling only when migrating historical sources.
// The current language accepts `transport value along path in family`.
export function currentTransportSyntax(source) {
  if (!/\balong\b/.test(source)) return source;
  const tokens = tokenize(source), indices = new Map(tokens.map((token, index) => [token.start, index]));
  if (!["along", "by", "from"].every(word => tokens.some(token => token.text === word))) return source;
  // Already-current source can bind `along` as an ordinary name.
  try { parse(source, false, { bindable: languageKeywords }); return source; } catch { /* Try the retired spelling. */ }
  const syntax = parse(source, false, { bindable: languageKeywords, historicalTransport: true });
  const groupEnds = new Map(), opens = [];
  for (const token of tokens) {
    if (token.text === "(") opens.push(token.start);
    else if (token.text === ")") groupEnds.set(opens.pop(), token.end);
  }
  const edits = [], seen = new Set();
  function visit(node) {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    if (node.kind === "transport") {
      const keyword = tokens[indices.get(node.family.start) - 1];
      if (keyword?.text === "along") {
        const by = tokens[indices.get(node.path.start) - 1], from = tokens[indices.get(node.value.start) - 1];
        if (by?.text !== "by" || from?.text !== "from") throw Error("Cannot locate historical transport operands.");
        edits.push({ start: keyword.start, end: node.value.end, node, keyword, by, from });
      }
    }
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) value.forEach(visit);
      else visit(value);
    }
  }
  visit(syntax);
  edits.sort((a, b) => a.start - b.start || b.end - a.end);
  function render(start, end) {
    let result = "", cursor = start;
    for (const edit of edits) {
      if (edit.start < cursor || edit.end > end) continue;
      const { node, keyword, by, from } = edit;
      // Move each operand together with its comments. Parentheses preserve
      // precedence, including when the value is another transport.
      const operand = (node, before, after = node.end) => {
        const text = source.slice(before, node.start) + render(node.start, node.end) + source.slice(node.end, after);
        const simple = ["name", "number", "binaryNumber", "projection"].includes(node.kind)
          || node.kind === "call" && !(node.fn.kind === "name" && node.fn.name === "transport");
        if ((simple || groupEnds.get(node.start) === node.end) && !text.includes("//")) return text.trim();
        return `(${text.trim()}${/\/\/[^\n]*$/.test(text.trim()) ? "\n" : ""})`;
      };
      result += source.slice(cursor, edit.start)
        + `transport ${operand(node.value, from.end)} along ${operand(node.path, by.end, from.start)} in ${operand(node.family, keyword.end, by.start)}`;
      cursor = edit.end;
    }
    return result + source.slice(cursor, end);
  }
  return edits.length ? render(0, source.length) : source;
}
