// Token classes of the source view, shared by the proof workspace and the
// language reference so that both highlight source the same way.
export const keywords = new Set([
  "import",
  "def",
  "forall",
  "exists",
  "and",
  "or",
  "let",
  "obtain",
  "intro",
  "have",
  "cases",
  "left",
  "right",
  "exact",
  "rfl", "calc", "rw", "simp", "simpa", "simp_rule", "simp_set", "priority", "only", "without", "using", "by", "occurrence", "ext", "over", "along", "from",
  "private",
  "export",
  "verify",
  "with",
  "unfolding",
  "computable",
  "evaluate",
  "expecting",
  "opaque",
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
  "W", "sup", "wrec",
  "Interval", "path", "PathP", "at", "comp", "face", "flip", "meet", "join",
  "Pushout", "push_left", "push_right", "push_path", "pushout_induction",
  "Nat", "Unit", "Void", "Universe", "tt", "succ", "refl", "absurd",
  "sym", "trans", "cong", "transport", "apd", "apd_path", "Eq", "typed",
  "induct", "unpack", "pair_induction", "unit_induction", "path_induction",
  "Choice", "LEM", "FunExt", "Truncate",
  "TruncateIntro", "TruncateProp", "TruncateElim", "Univalence", "UnivalenceBeta", "UnivalenceEta", "ua", "idtoequiv",
]);

// One source token: a comment, an operator, a binary literal, a name, a
// numeral, whitespace, or any other single character.
export const tokenPattern = /\/\/.*|(?:<=|->|=>|:=)|0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[+*<=>]|\s+|./g;
// A numeral is notation for repeated successors; 0 is the constructor itself.
export const numeralExpansion = text => /^[0-9]+$/.test(text) && Number(text) >= 1 && Number(text) <= 256
  ? "succ(".repeat(Number(text)) + "0" + ")".repeat(Number(text)) : null;
// Keywords and language-provided forms share one palette; notation is a
// macro, unless it stands for itself.
export const tokenStyle = (text, expansion) =>
  keywords.has(text) || builtinForms.has(text) || /^U[0-9]+$/.test(text) ? "keyword"
    : expansion && expansion !== text ? "macro" : "";

