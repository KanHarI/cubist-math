import { tokenize, parse } from "./parser.mjs";

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
// Before 2026-10-06 a block selected a model with open m;, now use m;.
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
  .replace(/(?<![A-Za-z0-9_'.])([A-Z][A-Za-z0-9_]*)\.Model(?![A-Za-z0-9_])/g, "$1")
  .replace(/(?<![A-Za-z0-9_'.])open(\s+[A-Za-z_][A-Za-z0-9_.]*\s*;)/g, "use$1");

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

// Until L2.10a (2026-10-06) nat declared no notation: + and numerals read
// add and Nat by name, until L2.10j. A revision's nat without one is read
// with the notation it had in effect, so that a module of today that imports
// it can select it with use nat; it adds no declaration. The revision's own
// modules keep reading by name (the Translator's nameBased, which
// tools/verify-proof-migration.mjs sets for a base before L2.10j).
const withNatNotation = text => /(?:^|\n)\s*notation\s+nat\b/.test(text) ? text : `${text.replace(/\s*$/, "\n")}
notation nat {
  x + y := add(x, y);
  x * y := mul(x, y);
  x <= y := le(x, y);
  x < y := ${/\bdef\s+isLt\b/.test(text) ? "isLt(x, y)" : "le(succ(x), y)"};
  numeral(n : Nat) := n;
}
`;

// Until 2026-10-06 left and right, a sum's injections, could be bound as
// names, and until 2026-10-07 typed, the ascription. A revision of that time
// is read with each binder named left, right or typed, and the references
// after it in its declaration, which it shadows, renamed left_, right_ and
// typed_; its sum patterns, injections and ascriptions stay. Bound names
// change no checked term.
const renamedReserved = { left: "left_", right: "right_", typed: "typed_" };
const reservedUnbound = source => {
  if (!/\b(left|right|typed)\b/.test(source)) return source;
  let ast;
  try { ast = parse(source, false, { bindable: Object.keys(renamedReserved) }); } catch { return source; }
  const edits = new Map();
  for (const item of ast.items ?? ast.declarations) {
    const binders = [], references = [], seen = new Set();
    const visit = (node, key = null, target = false) => {
      if (!node || typeof node !== "object" || seen.has(node)) return;
      seen.add(node);
      if (Array.isArray(node)) { node.forEach(child => visit(child, key, target)); return; }
      // A let's or an obtain's target binds its names.
      if (target && node.kind === "name" && renamedReserved[node.name]) {
        binders.push({ text: node.name, start: node.start, end: node.end });
        return;
      }
      // A binder's token; a clause's constructor is the injection's pattern.
      if (typeof node.text === "string" && renamedReserved[node.text] && !node.kind && key !== "constructor") binders.push(node);
      if (node.kind === "name" && renamedReserved[node.name]) references.push(node);
      for (const [child, value] of Object.entries(node)) if (child !== "uses") visit(value, child, target || child === "target");
    };
    visit(item);
    for (const binder of binders) {
      edits.set(binder.start, [binder.end, renamedReserved[binder.text]]);
      for (const reference of references)
        if (reference.name === binder.text && reference.start > binder.start && reference.end <= (item.end ?? Infinity))
          edits.set(reference.start, [reference.end, renamedReserved[reference.name]]);
    }
  }
  let text = source;
  for (const [start, [end, name]] of [...edits].sort((a, b) => b[0] - a[0])) text = text.slice(0, start) + name + text.slice(end);
  return text;
};

// Before 2026-10-05 every module imported nat without asking. A module of
// a revision that did so (implicitNat), read in today's syntax, imports it,
// unless it is nat or already does: so a baseline sees the names it saw then.
export const historicalSource = (source, module, { implicitNat = true, minusReverses = true } = {}) => {
  const rewritten = currentSyntax(source), text = reservedUnbound(minusReverses ? reversalsAsTilde(rewritten) : rewritten);
  if (module === "nat") return withNatNotation(text);
  if (!implicitNat || /(?:^|\n)\s*import\s+(?:[^;]*,\s*)?nat\s*[;,]/.test(text)) return text;
  return `import nat;\n${text}`;
};
