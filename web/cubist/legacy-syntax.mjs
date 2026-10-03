// Sources written before 2026-09-30 may use `have`, which `let` replaced with
// the same forms: have name : T := term; and have name : T { … } elaborate as
// let does. A historical source, such as a migration baseline read from an
// earlier revision, is read in today's syntax through this rewrite. show and
// suffices, removed the same day, never occurred in the library or the
// archive, so no historical source needs them.
export const currentSyntax = source =>
  source.replace(/(?<![A-Za-z0-9_'])have(\s+[A-Za-z_][A-Za-z0-9_]*\s*:)/g, "let$1");
