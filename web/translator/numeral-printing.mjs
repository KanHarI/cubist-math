// Literal recognition shared by the source and mathematical printers.
// These functions only inspect checked syntax; they never admit a numeral.
import {numeralValue} from "./numerals.mjs";
import {tokenize} from "../cubist/parser.mjs";

// A lexeme's marks, by their constructors, as characters (L2.10c).
const glyphs = { period: ".", slash: "/", underscore: "_", plus: "+", minus: "-" };
// A constructor of the declared type `signature`, applied to `arity`
// arguments: its name and arguments, or null.
const constructed = (t, signature, arity) => {
  const args = [];
  while (t?.tag === "App" && args.length < arity) { args.unshift(t.arg); t = t.fn; }
  return t?.tag === "Con" && t.sort?.tag === "Sort" && t.sort.signature === signature && args.length === arity ? { name: t.name, args } : null;
};
// A lexeme's text, from its constructors: a list of lexemes' glyphs, each a
// digit, a letter or a mark. Null where any part is no such constructor, or
// the text would not read back as one numeric token, so that only a whole
// literal prints as one.
export const lexemeText = t => {
  let text = "";
  for (;;) {
    if (constructed(t, "lists__List", 0)?.name === "nil") break;
    const cell = constructed(t, "lists__List", 2);
    if (cell?.name !== "cons") return null;
    const [glyph, rest] = cell.args, mark = constructed(glyph, "lexemes__Glyph", 0), valued = constructed(glyph, "lexemes__Glyph", 1);
    const value = valued && numeralValue(valued.args[0]);
    const character = mark ? glyphs[mark.name]
      : valued?.name === "digit" && value !== null && value < 10 ? String(value)
      : ["lower", "upper"].includes(valued?.name) && value !== null && value < 26 ? String.fromCharCode((valued.name === "lower" ? 97 : 65) + value)
      : undefined;
    if (character === undefined) return null;
    text += character;
    t = rest;
  }
  try { const tokens = tokenize(text); return tokens.length === 2 && tokens[0].text === text && /^[0-9]/.test(text) ? text : null; }
  catch { return null; }
};

// A binary natural of the library's bnat, in normal form, as its digits:
// b_zero is 0b0, and b_positive(p) holds bp_even and bp_odd digits, 0 and 1,
// the last digit outermost, around the leading bp_one. The printers show the
// value in decimal.
const constructorOf = (t, signature) => {
  const head = t?.tag === "App" ? t.fn : t;
  return head?.tag === "Con" && head.sort?.tag === "Sort" && head.sort.signature === signature ? head.index : null;
};
export const binaryDigits = t => {
  const natural = constructorOf(t, "bnat__BNat");
  if (natural === 0 && t.tag === "Con") return "0b0";
  if (natural !== 1 || t.tag !== "App") return null;
  let digits = "", p = t.arg;
  for (;;) {
    const index = constructorOf(p, "bnat__BPositive");
    if (index === 0 && p.tag === "Con") return `0b1${digits}`;
    if ((index !== 1 && index !== 2) || p.tag !== "App") return null;
    digits = (index === 1 ? "0" : "1") + digits;
    p = p.arg;
  }
};

export function parsedLiteral(term, symbols = {}, selection = null) {
  let head = term;
  const args = [];
  while (head?.tag === "App" || head?.tag === "LApp") {
    if (head.tag === "App") args.unshift(head.arg);
    head = head.fn;
  }
  if (head?.tag !== "DefRef" || head.name !== "lexemes__parsed_value" || args.length < 2) return null;
  let parser = args.at(-2);
  const parsed = [];
  while (parser?.tag === "App") { parsed.unshift(parser.arg); parser = parser.fn; }
  const readings = (parser?.tag === "DefRef" ? symbols[parser.name]?.printing : undefined)?.filter(entry => entry.literal) ?? [];
  const reading = readings.find(entry => entry.notation === selection) ?? readings[0];
  if (!reading || !parsed.length) return null;
  const text = lexemeText(parsed.at(-1));
  return text === null ? null : {text, reading, readings};
}
