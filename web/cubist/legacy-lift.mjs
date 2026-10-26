import { parse, tokenize, languageKeywords } from "./parser.mjs";

// The archived over statements all closed with one exact expression. Read
// those historical proofs as lift expressions, preserving their comments.
// Normal checking never opts into the retired statement grammar.
// `bindable` lists the words the source's revision did not reserve
// (legacy-syntax.mjs, historicalKeywords).
export function currentLiftSyntax(source, bindable = languageKeywords) {
  if (!/\bover\b/.test(source)) return source;
  const tokens = tokenize(source);
  if (!tokens.some(token => token.text === "over")) return source;
  const syntax = parse(source, false, { bindable, historicalOver: true });
  const indices = new Map(tokens.map((token, index) => [token.start, index]));
  const edits = [], seen = new Set();
  const visit = node => {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    if (node.kind === "over") {
      if (node.body.length !== 1 || node.body[0].kind !== "exact")
        throw Error("Historical over migration requires a single exact expression.");
      const first = tokens[indices.get(node.family.start) - 1];
      const along = tokens[indices.get(node.path.start) - 1];
      const by = tokens.find(token => token.start >= node.path.end && token.text === "by");
      const openIndex = indices.get(by.start) + 1, proof = node.body[0];
      const exactIndex = indices.get(proof.start);
      // Proof statements end after their semicolon, not at a token's start.
      const endIndex = tokens.findIndex(token => token.end === proof.end);
      const closeIndex = tokens.findIndex(token => token.end === node.end);
      const grouped = text => `(${text.trim()}${/\/\/[^\n]*$/.test(text.trim()) ? "\n" : ""})`;
      const family = grouped(source.slice(first.end, along.start));
      const path = grouped(source.slice(along.end, by.start));
      const value = grouped(source.slice(by.end, tokens[openIndex].start)
        + source.slice(tokens[openIndex].end, tokens[exactIndex].start)
        + source.slice(tokens[exactIndex].end, tokens[endIndex].start)
        + source.slice(tokens[endIndex].end, tokens[closeIndex].start));
      edits.push({ start: first.start, end: node.end, text: `exact lift ${value} along ${path} in ${family};` });
      return;
    }
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) value.forEach(visit);
      else visit(value);
    }
  };
  visit(syntax);
  for (const edit of edits.sort((a, b) => b.start - a.start))
    source = source.slice(0, edit.start) + edit.text + source.slice(edit.end);
  return source;
}
