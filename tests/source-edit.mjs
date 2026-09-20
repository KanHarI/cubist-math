import assert from "node:assert/strict";
import { tokenize } from "../web/mathscript/parser.mjs";

export const replaceAllSyntax = (source, needle, replacement) => replaceSyntax(source, needle, replacement, true);

// Mutation tests target syntax, so source formatting cannot disable a mutation.
export function replaceSyntax(source, needle, replacement, all = false) {
  const tokens = tokenize(source).slice(0, -1), wanted = tokenize(needle).slice(0, -1);
  assert.ok(wanted.length, "A source mutation needs nonempty syntax");
  const matches = [];
  for (let i = 0; i <= tokens.length - wanted.length; i++)
    if (wanted.every((token, j) => tokens[i + j].text === token.text)) matches.push(i);
  assert.ok(matches.length, `Missing mutation target: ${needle}`);
  for (const start of (all ? matches : matches.slice(0, 1)).reverse()) {
    const end = start + wanted.length - 1;
    source = source.slice(0, tokens[start].start) + replacement + source.slice(tokens[end].end);
  }
  return source;
}
