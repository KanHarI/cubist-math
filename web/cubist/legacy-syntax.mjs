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
export const currentSyntax = source => source
  .replace(/(?<![A-Za-z0-9_'])have(\s+[A-Za-z_][A-Za-z0-9_]*\s*:)/g, "let$1")
  .replace(/(?<![A-Za-z0-9_'])cases(?=\s+[^{};]*\{\s*left\s+[A-Za-z_][A-Za-z0-9_']*\s*=>)/g, "match");
