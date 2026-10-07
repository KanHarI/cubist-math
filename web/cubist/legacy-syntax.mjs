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
// names, and until 2026-10-07 typed, the ascription, and evaluate. A
// revision of that time is read with each binder named left, right, typed
// or evaluate renamed left_, right_, typed_ and evaluate_, and with it each
// reference in its scope, as the translator reads scopes: a parameter's is
// the rest of its declaration, a lambda's its body, a let's the statements
// after it but not its own value, a pattern's its clause, and a
// declaration's itself and the items after it. A name no such binder is in
// scope for is the builtin, an injection or an ascription, and stays, as
// sum patterns and evaluate directives do. A name read by its declaration
// rather than by scope, a parameter's in a named argument or a field's
// after a dot, is renamed wherever it is written, as each declaration of it
// is. A module reads only its own binders: a name another module declares
// so, called bare, is not followed. Bound names change no checked term.
const renamedReserved = { left: "left_", right: "right_", typed: "typed_", evaluate: "evaluate_" };
const reservedUnbound = source => {
  if (!/\b(left|right|typed|evaluate)\b/.test(source)) return source;
  let ast;
  try { ast = parse(source, false, { bindable: Object.keys(renamedReserved) }); } catch { return source; }
  const edits = new Map();
  const rename = (start, text) => { if (renamedReserved[text]) edits.set(start, [start + text.length, renamedReserved[text]]); };
  // Binder tokens: each is renamed, and the scope they open holds them.
  const bind = (scope, tokens) => {
    const named = tokens.filter(token => renamedReserved[token?.text]);
    for (const token of named) rename(token.start, token.text);
    return named.length ? new Set([...scope, ...named.map(token => token.text)]) : scope;
  };
  // A name, as its scope reads it, and each part after a dot, a field or a
  // module's member, wherever it is written.
  const reference = (token, scope) => {
    const [head, ...rest] = (token.name ?? token.text).split(".");
    if (scope.has(head)) rename(token.start, head);
    let at = token.start + head.length;
    for (const part of rest) { rename(at + 1, part); at += 1 + part.length; }
  };
  // A clause's variables: its arguments, its legacy binders, its
  // coordinates, and a bare name, which is a variable or a constructor
  // without arguments.
  const variables = head => [...(head.binders ?? []), ...(head.coordinates ?? []),
    ...(head.args ?? []).flatMap(arg => arg.kind === "pattern" ? variables(arg) : [arg]),
    ...(!head.args && !head.binders?.length && !head.coordinates?.length ? [head.constructor] : []),
    ...(head.more ?? []).flatMap(variables)];
  // A let's or an obtain's target: a name, or a tuple of them.
  const targets = node => node?.kind === "pair" ? [...targets(node.left), ...targets(node.right)]
    : node?.kind === "name" ? [{ text: node.name, start: node.start }] : [];
  // Parameters in order, each group's type read before its names hold.
  const telescope = (params, scope) => {
    for (let k = 0; k < params.length;) {
      const type = params[k].type ?? params[k].bound;
      let j = k;
      while (j < params.length && (params[j].type ?? params[j].bound) === type) j++;
      visit(type, scope);
      scope = bind(scope, params.slice(k, j).map(p => p.name));
      k = j;
    }
    return scope;
  };
  // A notation's pattern: its operands bind its right side, and a view
  // names a notation.
  const notation = (pattern, scope) => {
    for (const view of [pattern?.leftView, pattern?.rightView]) if (view) reference(view, scope);
    return bind(scope, [pattern?.left, pattern?.right]);
  };
  // A statement's binders hold in the statements after it.
  const statement = (node, scope) => {
    switch (node?.kind) {
      case "let": case "obtain":
        visit(node.type, scope); visit(node.value, scope); visit(node.body, scope);
        return bind(scope, targets(node.target));
      case "intro": return bind(scope, [node.name]);
      case "ext": return bind(scope, [node.variable]);
      case "simpOnly": case "simpaOnly":
        visit(node.rules, scope); visit(node.using, scope);
        for (const token of [...node.without, ...node.witnesses, ...(node.at ? [node.at] : [])]) reference(token, scope);
        return bind(scope, [node.as]);
    }
    visit(node, scope);
    return scope;
  };
  const visit = (node, scope) => {
    if (!node || typeof node !== "object") return;
    if (Array.isArray(node)) { node.reduce((inner, child) => statement(child, inner), scope); return; }
    switch (node.kind) {
      case "name": reference(node, scope); return;
      case "lambda": case "forall": case "exists": case "binderGroup":
        visit(node.domain, scope); visit(node.bound, scope);
        visit(node.body, bind(scope, node.names ?? [node.name]));
        return;
      case "pathLambda": visit(node.body, bind(scope, [node.dimension])); return;
      case "unpack":
        visit(node.value, scope); visit(node.type, scope);
        visit(node.body, bind(scope, [node.left, node.right]));
        return;
      case "match": case "induction": case "matchStatement":
        visit(node.values ?? node.value, scope);
        // induction n as k return C { zero => …; succ h => …; }: k names n in
        // C and its predecessor in the successor's clause.
        if ("index" in node) {
          visit(node.type, bind(scope, [node.index])); visit(node.base, scope);
          visit(node.step, bind(scope, [node.index, node.hypothesis]));
          return;
        }
        // The legacy match on a sum keeps its clauses unlisted.
        visit(node.type, bind(scope, [node.motiveName])); visit(node.clauses, scope);
        visit(node.obligations, scope); visit(node.obligationProof, scope);
        return;
      case "clause": visit(node.body, bind(scope, variables(node))); return;
      case "namedArgument": rename(node.name.start, node.name.text); visit(node.value, scope); return;
      case "member": rename(node.field.start, node.field.text); visit(node.value, scope); return;
      case "withUnfolding": for (const hint of node.hints) reference(hint, scope); visit(node.body, scope); return;
    }
    for (const [key, child] of Object.entries(node)) if (key !== "uses") visit(child, scope);
  };
  // Items in order: what one declares holds in it and after it.
  let module = new Set();
  for (const item of ast.items ?? ast.declarations) {
    if (item.kind === "def") {
      const scope = telescope(item.params, telescope(item.section?.params ?? [], bind(module, [item.name])));
      visit(item.type, scope); visit(item.body, scope); visit(item.value, scope);
    } else if (item.kind === "inductive") {
      const scope = telescope(item.params, bind(module, [item.name]));
      visit(item.result, scope);
      for (const constructor of item.constructors) visit(constructor.type, telescope(constructor.params, scope));
    } else if (item.kind === "theory") {
      // A field holds in the fields after it, a parent's label and its
      // renamed fields too; a field of the parent is read by name.
      let scope = telescope(item.params, bind(module, item.universes));
      for (const parent of item.parents) {
        reference(parent.name, module);
        for (const { from, to, notation: pattern } of parent.renaming) { rename(from.start, from.text); scope = bind(scope, [to]); notation(pattern, scope); }
        scope = bind(scope, [parent.label]);
      }
      for (const field of item.fields) {
        const inner = telescope(field.params, scope);
        if (field.universe) reference(field.universe, scope);
        visit(field.type, inner); visit(field.value, inner);
        notation(field.notation, scope);
        scope = bind(scope, [field.name]);
      }
    } else if (item.kind === "notation") {
      for (const rule of item.rules)
        if (rule.param) { visit(rule.type, module); visit(rule.value, bind(module, [rule.param])); }
        else visit(rule.value, notation(rule, module));
    } else if (["hlevel_rule", "simp_rule"].includes(item.kind)) reference(item.rule, module);
    else if (item.kind === "simp_set") for (const rule of item.rules) reference(rule, module);
    else visit(item, module);
    module = bind(module, [item.name, ...(item.constructors ?? []).map(constructor => constructor.name)]);
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
