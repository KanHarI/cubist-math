import { tokenize } from "./parser.mjs";

// Sources written before 2026-09-30 may use `have`, which `let` replaced with
// the same forms: have name : T := term; and have name : T { … } elaborate as
// let does. A historical source, such as a migration baseline read from an
// earlier revision, is read in today's syntax through this rewrite. show and
// suffices, removed the same day, never occurred in the library or the
// archive, so no historical source needs them.
//
// Sources written before 2026-10-04 may use `cases v { left a => { … } right
// b => { … } }`, which the match statement on a sum replaced. It takes the
// clauses as cases wrote them, and where neither the goal nor a hypothesis
// depends on v it elaborates to cases' term: the goal itself is the motive.
// Every cases statement of the archive was such a one: its migration
// (1118c1a), checked while cases still parsed, kept every term identical.
//
// Sources written before 2026-10-06 declare a theory's carriers as sorts,
// theory T { sort M : set; }, and name its type of models T.Model. They are
// read as theory T(U < UU0) { M : set U; } and T, which elaborate the same
// (L2.4c): U is the theory's universe, which no field of those theories took.
export const currentSyntax = source => source
  .replace(/(?<![A-Za-z0-9_'])have(\s+[A-Za-z_][A-Za-z0-9_]*\s*:)/g, "let$1")
  .replace(/(?<![A-Za-z0-9_'])cases(?=\s+[^{};]*\{\s*left\s+[A-Za-z_][A-Za-z0-9_']*\s*=>)/g, "match")
  .replace(/(?<![A-Za-z0-9_'.])(theory\s+[A-Z][A-Za-z0-9_]*)(?=\s+(?:extends\b|\{))/g, "$1(U < UU0)")
  .replace(/(?<![A-Za-z0-9_'.])sort\s+([A-Za-z_][A-Za-z0-9_]*\s*:\s*)(set|prop)(\s*;)/g, "$1$2 U$3")
  .replace(/(?<![A-Za-z0-9_'.])([A-Z][A-Za-z0-9_]*)\.Model(?![A-Za-z0-9_])/g, "$1");

// Until 2026-10-06 prefix - reversed, as ~ does now: -p a path and -i a
// coordinate. A revision of that time (minusReverses) is read with ~ for each
// prefix -; trunc(-1)'s minus is a level's sign and stays. Arithmetic - is to
// return (notation roadmap, L2.10b), so a later revision is read as it is.
const reversalsAsTilde = source => {
  let tokens;
  try { tokens = tokenize(source); } catch { return source; }
  const starts = tokens.filter((token, k) => token.text === "-"
    && !(tokens[k - 1]?.text === "(" && tokens[k - 2]?.text === "trunc")).map(token => token.start);
  let text = source;
  for (const start of starts.reverse()) text = `${text.slice(0, start)}~${text.slice(start + 1)}`;
  return text;
};

// Before 2026-10-05 every module imported nat without asking. A module of
// a revision that did so (implicitNat), read in today's syntax, imports it,
// unless it is nat or already does: so a baseline sees the names it saw then.
export const historicalSource = (source, module, { implicitNat = true, minusReverses = true } = {}) => {
  const rewritten = currentSyntax(source), text = minusReverses ? reversalsAsTilde(rewritten) : rewritten;
  if (!implicitNat || module === "nat" || /(?:^|\n)\s*import\s+(?:[^;]*,\s*)?nat\s*[;,]/.test(text)) return text;
  return `import nat;\n${text}`;
};
