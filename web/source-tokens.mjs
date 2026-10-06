// Token classes of the source view, shared by the proof workspace and the
// language reference so that both highlight source the same way.
import { notationOperators } from "./cubist/parser.mjs";

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
  "open",
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
// The words a theory gives a role, by offset, found once per source from its
// tokens, so that comments and nested braces do not move them (L2.4). In a
// theory's header, extends after its name and universe, and notation in a
// parent's renaming; in its body, law starting a field and followed by its
// name, a carrier's h-level, as set in M : set U;, and notation after an
// operation's type, followed by x + y. Each of these is a keyword, and the
// words are names elsewhere, as the parser reads them: a field may be named
// law, set or notation. zero and succ in a theory name its fields, not
// Nat's constructors.
let rolesOf = { source: null, roles: new Map() };
function theoryRoles(source) {
  if (rolesOf.source === source) return rolesOf.roles;
  const tokens = [...source.matchAll(tokenPattern)].filter(([text]) => !/^\s/.test(text) && !text.startsWith("//"))
    .map(match => ({ text: match[0], start: match.index }));
  const roles = new Map(), text = at => tokens[at]?.text;
  const isWord = at => /^[A-Za-z_]/.test(text(at) ?? "");
  const notationAt = at => text(at) === "notation" && isWord(at + 1) && notationOperators.includes(text(at + 2)) && isWord(at + 3);
  const fieldWord = at => { if (["zero", "succ"].includes(text(at))) roles.set(tokens[at].start, false); };
  for (let at = 0; at < tokens.length; at++) {
    if (text(at) !== "theory" || !startsLine(source, tokens[at].start) || !isWord(at + 1)) continue;
    let next = at + 2;
    // The header, theory T(U < UU0), comes before extends.
    if (text(next) === "(") for (let depth = 0; next < tokens.length; next++) {
      depth += text(next) === "(" ? 1 : text(next) === ")" ? -1 : 0;
      if (depth === 0) { next++; break; }
    }
    if (text(next) === "extends") roles.set(tokens[next].start, true);
    for (; next < tokens.length && !["{", ";", "}"].includes(text(next)); next++) {
      if (notationAt(next)) roles.set(tokens[next].start, true);
      fieldWord(next);
    }
    if (text(next) !== "{") { at = next; continue; }
    // The body, to its own closing brace: a field's type may hold braces.
    let depth = 0, field = next + 1, law = false;
    for (next++; next < tokens.length; next++) {
      const word = text(next);
      if (depth === 0 && word === "}") break;
      depth = Math.max(0, depth + (["{", "("].includes(word) ? 1 : ["}", ")"].includes(word) ? -1 : 0));
      fieldWord(next);
      if (depth === 0 && word === ";") { field = next + 1; law = false; continue; }
      if (next !== field) {
        if (depth === 0 && !law && notationAt(next)) roles.set(tokens[next].start, true);
        continue;
      }
      if (word === "law" && isWord(next + 1)) { roles.set(tokens[next].start, true); law = true; }
      // A carrier's h-level: M : set U; and P : prop U;.
      if (isWord(next) && text(next + 1) === ":" && ["set", "prop"].includes(text(next + 2)) && isWord(next + 3)
        && text(next + 4) === ";") roles.set(tokens[next + 2].start, true);
    }
    at = next;
  }
  rolesOf = { source, roles };
  return roles;
}
// theory and section start an item on a line of their own.
const startsLine = (source, start) => /^\n?\s*$/.test(source.slice(Math.max(0, source.lastIndexOf("\n", start - 1)), start));
// Words that are keywords only where they stand: an inductive header's
// h-level; theory and section starting an item; and a theory's words, above.
export function keywordAt(source, start, text) {
  if (headerWordAt(source, start, text)) return true;
  // use selects a model, use m; (L2.4c), and is a name elsewhere.
  if (text === "use") return /^\s+[A-Za-z_][A-Za-z_0-9.]*\s*;/.test(source.slice(start + 3)) || undefined;
  const role = theoryRoles(source).get(start);
  if (role !== undefined) return role;
  return ["theory", "section"].includes(text) && startsLine(source, start) || undefined;
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

