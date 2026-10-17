// Token classes of the source view, shared by the proof workspace and the
// language reference so that both highlight source the same way.
import { reservedNames, isUniverseConstant } from "./cubist/parser.mjs";
export { scan } from "./cubist/parser.mjs";
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
  reservedNames.has(text) || isUniverseConstant(text) ? "keyword"
    : expansion && expansion !== text ? "macro" : "";
