// Token classes of the source view, shared by the proof workspace and the
// language reference so that both highlight source the same way.
export const keywords = new Set([
  "import",
  "def",
  "inductive",
  "forall",
  "exists",
  "and",
  "or",
  "let",
  "obtain",
  "intro",
  "left",
  "right",
  "exact",
  "rfl", "calc", "rw", "simp", "simpa", "hlevel", "simp_rule", "simp_set", "priority", "only", "without", "using", "by", "occurrence", "ext", "over", "along", "from",
  "private",
  "export",
  "verify",
  "with",
  "unfolding",
  "computable",
  "evaluate",
  "expecting",
  "print",
  "typeof",
  "inspect",
  "axioms",
  "allow",
  "none",
  "intro",
  "induction",
  "zero",
  "succ",
  "fun",
  "match",
  "return",
  "as",
]);
// Language-provided forms share the keyword palette; ordinary library and
// user-defined functions retain the green reference style.
export const builtinForms = new Set([
  "Interval", "path", "PathP", "at", "comp", "face", "flip", "meet", "join", "Glue", "glue", "unglue",
  "Nat", "Unit", "Void", "next", "max", "tt", "succ", "refl", "absurd",
  "sym", "trans", "cong", "transport", "apd", "apd_path", "Eq", "typed",
  "induct", "unpack", "pair_induction", "unit_induction", "path_induction",
  "Choice", "LEM", "FunExt", "Truncate",
  "TruncateIntro", "TruncateProp", "TruncateElim", "Univalence", "UnivalenceBeta", "UnivalenceEta", "ua", "idtoequiv",
]);

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
// zero and succ that link to a definition, such as a ring's zero after
// `open A;`, are names; Nat's constructors link to no definition.
export const linkedWord = (text, link) => ["zero", "succ"].includes(text) && link?.role === "definition" ? false : undefined;
// Each theory's header, from its name to its body's brace, and its body, to
// the closing brace (L2.4): a body has no braces of its own. Found once per
// source.
let regionsOf = { source: null, regions: [] };
function theoryRegions(source) {
  if (regionsOf.source !== source) {
    const regions = [];
    for (const match of source.matchAll(/(?:^|\n)\s*theory\s+[A-Za-z_][A-Za-z_0-9]*/g)) {
      const open = source.indexOf("{", match.index + match[0].length);
      const close = open < 0 ? -1 : source.indexOf("}", open);
      regions.push({ header: [match.index + match[0].length, open < 0 ? source.length : open],
        body: open < 0 ? [0, 0] : [open + 1, close < 0 ? source.length : close] });
    }
    regionsOf = { source, regions };
  }
  return regionsOf.regions;
}
const within = ([from, to], at) => from <= at && at < to;
const inTheoryBody = (source, at) => theoryRegions(source).some(region => within(region.body, at));
const inTheoryHeader = (source, at) => theoryRegions(source).some(region => within(region.header, at));
// Words that are keywords only where they stand: an inductive header's
// h-level, and a theory's; theory and section starting an item; extends in
// a theory's header; law and sort starting a theory's field; notation in a
// theory; and open starting a statement. Inside a theory, zero and succ name
// its fields, not Nat's constructors.
export function keywordAt(source, start, text) {
  // The text just before the word, up to the line before it.
  const lead = () => source.slice(Math.max(0, source.lastIndexOf("\n", start - 1)), start);
  const previous = () => source.slice(0, start).match(/\S\s*$/)?.[0][0];
  if (["type", "set", "prop", "trunc"].includes(text)) {
    if (headerWordAt(source, start, text)) return true;
    return ["set", "prop"].includes(text) && inTheoryBody(source, start)
      && /\bsort\s+[A-Za-z_][A-Za-z_0-9]*\s*:\s*$/.test(lead()) ? true : undefined;
  }
  switch (text) {
    case "theory": case "section": return /^\n?\s*$/.test(lead()) || undefined;
    case "extends": return inTheoryHeader(source, start) || undefined;
    case "law": case "sort": return inTheoryBody(source, start) && ["{", ";"].includes(previous()) || undefined;
    case "notation": return inTheoryBody(source, start) || inTheoryHeader(source, start) || undefined;
    case "open": return ["{", ";"].includes(previous()) || undefined;
    case "zero": case "succ": return inTheoryBody(source, start) || inTheoryHeader(source, start) ? false : undefined;
    default: return undefined;
  }
}
// type, set, prop and trunc are h-level keywords only as the first word of an
// inductive header's result position, after its colon, and names elsewhere.
export function headerWordAt(source, start, text) {
  if (!["type", "set", "prop", "trunc"].includes(text)) return false;
  const before = source.slice(0, start), header = before.search(/\binductive\b[^{};]*$/);
  if (header < 0 || !/:\s*$/.test(before)) return false;
  // The colon must be the header's own, outside its parameters' parentheses.
  let depth = 0;
  for (const character of before.slice(header)) depth += character === "(" ? 1 : character === ")" ? -1 : 0;
  return depth === 0;
}

