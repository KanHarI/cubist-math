// Token classes of the source view, shared by the proof workspace and the
// language reference so that both highlight source the same way.
import { languageKeywords, builtinNames } from "./cubist/parser.mjs";

export const keywords = languageKeywords;
// Language-provided forms share the keyword palette; ordinary library and
// user-defined functions retain the green reference style.
export const builtinForms = new Set([...builtinNames, "Unit", "Void", "tt"]);

// One source token: a comment, an operator, a binary literal, a name, a
// numeral, whitespace, or any other single character.
export const tokenPattern = /\/\/.*|(?:<=|->|=>|:=|\+\+)|0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[+*<=>&|]|\s+|./g;
// A numeral is notation for repeated successors; 0 is the constructor itself.
export const numeralExpansion = text => /^[0-9]+$/.test(text) && Number(text) >= 1 && Number(text) <= 256
  ? "succ(".repeat(Number(text)) + "0" + ")".repeat(Number(text)) : null;
// The index of a projection p.1 is not a numeral: it follows a dot that is
// tight on both sides, as the parser requires.
export const projectionIndex = (source, start) => source[start - 1] === "." && /\S/.test(source[start - 2] ?? " ");
// The expansion of the numeral at `start` in `source`, if it is one.
export const numeralAt = (source, start, text) => projectionIndex(source, start) ? null : numeralExpansion(text);
// Keywords keep their style wherever written. Notation uses the macro
// palette unless it expands to itself.
export const tokenStyle = (text, expansion) =>
  keywords.has(text) || builtinForms.has(text) || /^U+[0-9]+$/.test(text) ? "keyword"
    : expansion && expansion !== text ? "macro" : "";
