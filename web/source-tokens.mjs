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
// Keywords and language-provided forms share one palette; notation is a
// macro, unless it stands for itself. `here` is what keywordAt says of the
// word where it stands: true, a keyword there; false, a name there; otherwise
// the word's usual style.
export const tokenStyle = (text, expansion, here) =>
  here === true || here !== false && (keywords.has(text) || builtinForms.has(text) || /^U+[0-9]+$/.test(text)) ? "keyword"
    : expansion && expansion !== text ? "macro" : "";
// Keywords keep their style wherever written, including invalid attempts
// to use one as a name. Library names are styled through their references.
export const keywordAt = (source, start, text) => languageKeywords.has(text) || undefined;
