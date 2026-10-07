import { tokenize, parse, languageKeywords, generatedNames } from "./parser.mjs";

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
// after it but not its own value, a pattern's its clause, a constructor's
// the constructors after it, and a declaration's itself and the items after
// it. A name no such binder is in scope for is the builtin, an injection or
// an ascription, and stays, as evaluate directives do. A name read by its
// declaration rather than by scope, a parameter's in a named argument, a
// field's after a dot or a constructor's in a clause, follows its
// declaration. When available, the matched value's type distinguishes a
// sum's injections and a generated squash from user constructors. Types
// come from telescopes, annotated locals, constructor calls and aliases.
// Callers migrating several modules supply a shared renaming plan and
// their imported declarations, so selections and calls retain their types.
// Bound names change no checked term.
// Contextual keywords could also be bound before all keywords were reserved.
const historicalRenaming = Object.fromEntries([...languageKeywords].map(word => [word, `${word}_`]));
// A migration across modules uses one plan for declarations, imported
// references and argument labels. Include every original source so a local
// spelling in an importer cannot capture a dependency's renamed export.
export const reservedBindingRenaming = (sources, preferred = historicalRenaming) => {
  const taken = new Set(sources.flatMap(source => tokenize(source).map(token => token.text)));
  return Object.fromEntries(Object.entries(preferred).map(([word, stem]) => {
    let name = stem;
    while (taken.has(name)) name += "_";
    taken.add(name);
    return [word, name];
  }));
};
// Used by the source migration as well as by the historical source reader.
// Only binders and their references change; grammar tokens keep their roles.
export const renameReservedBindings = (source, renamedReserved = historicalRenaming, { importedNames = [], importedDeclarations = [] } = {}) => {
  let ast, tokens;
  try {
    tokens = tokenize(source);
    if (!tokens.some(token => Object.hasOwn(renamedReserved, token.text))) return source;
    ast = parse(source, false, { bindable: Object.keys(renamedReserved) });
  } catch { return source; }
  // A replacement must not capture an existing name, even in an inner
  // scope. Use one fresh spelling throughout this source, including labels.
  renamedReserved = reservedBindingRenaming([source], renamedReserved);
  const edits = new Map();
  const items = ast.items ?? ast.declarations;
  const declarations = [...importedDeclarations, ...items];
  const theories = new Map(declarations.filter(item => item.kind === "theory").map(item => [item.name.text, item]));
  const userMembers = new Set(declarations.filter(item => item.kind === "theory")
    .flatMap(item => item.fields.map(field => field.name.text)));
  const types = new Map(declarations.filter(item => item.kind === "inductive").map(item => [item.name.text, item]));
  const aliases = new Map(declarations.filter(item => item.kind === "def")
    .map(item => [item.name.text, item.value ?? (item.body?.length === 1 ? item.body[0].value : null)]));
  const parentLabel = parent => parent.label?.text ?? parent.name.text.replace(/([a-z0-9])([A-Z])/g, "$1_$2").toLowerCase();
  const declarationType = item => (item.params ?? []).reduceRight((body, param) =>
    ({ kind: "forall", name: param.name, domain: param.type ?? param.bound, body, implicit: param.implicit }), item.type);
  const fieldsOf = (theory, seen = new Set()) => {
    if (!theory || seen.has(theory)) return new Map();
    const fields = new Map();
    for (const parent of theory.parents) {
      const renamed = new Map(parent.renaming.map(({ from, to }) => [from.text, to.text]));
      for (const [name, type] of fieldsOf(theories.get(parent.name.text), new Set([...seen, theory])))
        fields.set(renamed.get(name) ?? name, type);
      const label = parentLabel(parent);
      fields.set(label, { kind: "name", name: parent.name.text });
      userMembers.add(label);
    }
    for (const field of theory.fields) fields.set(field.name.text, declarationType(field));
    return fields;
  };
  const theoryFields = new Map([...theories].map(([name, theory]) => [name, fieldsOf(theory)]));
  const typeName = (type, seen = new Set()) => {
    if (type?.kind === "binary" && type.operator === "or") return "sum";
    const name = type?.kind === "name" ? type.name : type?.kind === "call" && type.fn.kind === "name" ? type.fn.name : null;
    if (aliases.has(name) && !seen.has(name)) return typeName(aliases.get(name), new Set([...seen, name])) ?? name;
    return name;
  };
  const valueType = (value, scope) => {
    if (value?.kind === "name") {
      if (scope.has(value.name)) return scope.get(value.name);
      const dot = value.name.lastIndexOf(".");
      if (dot > 0) return theoryFields.get(typeName(valueType({ kind: "name", name: value.name.slice(0, dot) }, scope)))?.get(value.name.slice(dot + 1));
    }
    if (value?.kind === "member") return theoryFields.get(typeName(valueType(value.value, scope)))?.get(value.field.text);
    if (value?.kind === "call") {
      if (value.fn.name === "typed" && !scope.has("typed")) return value.args[0];
      const made = value.fn.name?.match(/^(.+)\.make$/)?.[1];
      if (theories.has(made)) return { kind: "name", name: made };
      const owner = [...types.values()].find(type => type.constructors.some(c => c.name.text === value.fn.name));
      if (owner) return { kind: "name", name: owner.name.text };
      let type = valueType(value.fn, scope);
      for (const arg of value.implicitArgs ?? []) if (type?.implicit) type = type.body;
      for (const arg of value.args) {
        while (type?.implicit) type = type.body;
        type = type?.body ?? (type?.operator === "->" ? type.right : null);
      }
      return type;
    }
    return null;
  };
  const generatedOwner = (value, scope) => /\.(Hom|Iso)$/.test(typeName(valueType(value, scope)) ?? "");
  const rename = (start, text) => { if (Object.hasOwn(renamedReserved, text)) edits.set(start, [start + text.length, renamedReserved[text]]); };
  // Binder tokens: each is renamed, and the scope they open holds them.
  const bind = (scope, tokens, type = null) => {
    const named = tokens.filter(token => token?.text);
    for (const token of named) rename(token.start, token.text);
    return named.length ? new Map([...scope, ...named.map(token => [token.text, type])]) : scope;
  };
  // A name, as its scope reads it, and each part after a dot, a field or a
  // module's member, wherever it is written.
  const reference = (token, scope) => {
    const [head, ...rest] = (token.name ?? token.text).split(".");
    // Parentheses widen expression spans. Find the identifier tokens in
    // that span instead of replacing text at the expression's start.
    let lo = 0, hi = tokens.length;
    while (lo < hi) { const mid = (lo + hi) >>> 1; if (tokens[mid].start < token.start) lo = mid + 1; else hi = mid; }
    const next = text => {
      while (lo < tokens.length && tokens[lo].start < token.end) {
        const candidate = tokens[lo++];
        if (candidate.text === text) return candidate.start;
      }
      return null;
    };
    const start = next(head);
    if (start !== null && scope.has(head)) rename(start, head);
    for (const [k, part] of rest.entries()) {
      // Generated interfaces keep their public members. A user field or
      // an imported module member is renamed with its declaration.
      const owner = k ? rest[k - 1] : head;
      const ownerValue = { kind: "name", name: [head, ...rest.slice(0, k)].join(".") };
      const at = next(part);
      if (at !== null && (!generatedNames.has(part) || !["Hom", "Iso"].includes(owner)
          && !generatedOwner(ownerValue, scope) && (userMembers.has(part) || ast.imports.includes(head)))) rename(at, part);
    }
  };
  // A clause's constructors, nested and in each of its columns, but a sum's
  // injections: left x, and left(…) where this module has declared no
  // constructor left so far. A bare left is renamed as variables binds it.
  const declared = new Set(importedDeclarations.flatMap(item => (item.constructors ?? []).map(c => c.name.text)));
  const constructors = (head, matched = []) => {
    const { constructor } = head;
    const owner = typeName(matched[0]), declaration = types.get(owner);
    const own = declaration?.constructors.find(c => c.name.text === constructor.text);
    const sum = owner === "sum" && ["left", "right"].includes(constructor.text);
    const generated = ["gen", "squash"].includes(constructor.text) && (owner ? !own : !declared.has(constructor.text));
    if (!sum && !generated && !(["left", "right"].includes(constructor.text) && !head.coordinates?.length
        && (!head.args || !declared.has(constructor.text)))) rename(constructor.start, constructor.text);
    for (const [k, arg] of (head.args ?? []).entries()) if (arg.kind === "pattern") constructors(arg, [own?.params[k]?.type]);
    for (const [k, column] of (head.more ?? []).entries()) constructors(column, [matched[k + 1]]);
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
      scope = bind(scope, params.slice(k, j).map(p => p.name), type);
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
      case "use":
        visit(node.model, scope);
        return new Map([...scope, ...(theoryFields.get(typeName(valueType(node.model, scope))) ?? [])]);
      case "let": case "obtain":
        visit(node.type, scope); visit(node.value, scope); visit(node.body, scope);
        return bind(scope, targets(node.target), node.type ?? valueType(node.value, scope));
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
  const visit = (node, scope, matched = []) => {
    if (!node || typeof node !== "object") return;
    if (Array.isArray(node)) { node.reduce((inner, child) => statement(child, inner), scope); return; }
    switch (node.kind) {
      case "name": reference(node, scope); return;
      case "lambda": case "forall": case "exists": case "binderGroup":
        visit(node.domain, scope); visit(node.bound, scope);
        visit(node.body, bind(scope, node.names ?? [node.name], node.domain));
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
        visit(node.type, bind(scope, [node.motiveName]));
        for (const clause of node.clauses ?? []) visit(clause, scope, (node.values ?? [node.value]).map(value => valueType(value, scope)));
        visit(node.obligations, scope); visit(node.obligationProof, scope);
        return;
      case "clause": constructors(node, matched); visit(node.body, bind(scope, variables(node))); return;
      case "call": {
        visit(node.fn, scope);
        // Named arguments refer to the callee's parameters. Only a call
        // to a generated interface keeps its fixed labels; a user's map
        // parameter must follow its declaration even in an unrelated theory.
        const generated = /^.+\.(Hom|Iso)\.[^.]+$/.test(node.fn.name ?? "");
        for (const arg of [...(node.implicitArgs ?? []), ...node.args]) {
          if (arg.kind === "namedArgument") {
            if (!generated || !generatedNames.has(arg.name.text)) rename(arg.name.start, arg.name.text);
            visit(arg.value, scope);
          } else visit(arg, scope);
        }
        return;
      }
      case "namedArgument":
        rename(node.name.start, node.name.text);
        visit(node.value, scope); return;
      case "member":
        if (!generatedNames.has(node.field.text) || !generatedOwner(node.value, scope) && userMembers.has(node.field.text))
          rename(node.field.start, node.field.text);
        visit(node.value, scope); return;
      case "withUnfolding": for (const hint of node.hints) reference(hint, scope); visit(node.body, scope); return;
    }
    for (const [key, child] of Object.entries(node)) if (key !== "uses") visit(child, scope);
  };
  // Items in order: what one declares holds in it and after it.
  for (let k = 1; k < tokens.length; k++) if (tokens[k - 1].text === "import") rename(tokens[k].start, tokens[k].text);
  let module = new Map([
    ...[...importedNames, ...ast.imports].map(name => [name, null]),
    ...importedDeclarations.flatMap(item => [[item.name.text, declarationType(item)],
      ...(item.constructors ?? []).map(c => [c.name.text, { kind: "name", name: item.name.text }])]),
  ]);
  for (const item of items) {
    if (item.kind === "def") {
      const scope = telescope(item.params, telescope(item.section?.params ?? [], bind(module, [item.name], declarationType(item))));
      visit(item.type, scope); visit(item.body, scope); visit(item.value, scope);
    } else if (item.kind === "inductive") {
      // A constructor holds in the constructors after it, as loop : base =
      // base reads base.
      let scope = telescope(item.params, bind(module, [item.name]));
      visit(item.result, scope);
      for (const constructor of item.constructors) {
        visit(constructor.type, telescope(constructor.params, scope));
        scope = bind(scope, [constructor.name]);
        if (Object.hasOwn(renamedReserved, constructor.name.text)) declared.add(constructor.name.text);
      }
    } else if (item.kind === "theory") {
      // A field holds in the fields after it, a parent's label and its
      // renamed fields too; a field of the parent is read by name.
      let scope = telescope(item.params, bind(module, item.universes));
      for (const parent of item.parents) {
        reference(parent.name, module);
        const label = parentLabel(parent);
        if (!parent.label && Object.hasOwn(renamedReserved, label)) {
          const at = parent.name.start, [end, text] = edits.get(at) ?? [at, ""];
          edits.set(at, [end, `${renamedReserved[label]} : ${text}`]);
        }
        scope = new Map([...scope, ...(theoryFields.get(parent.name.text) ?? []), [label, { kind: "name", name: parent.name.text }]]);
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
    else if (item.kind === "use") module = statement(item, module);
    else visit(item, module);
    module = bind(module, [item.name], declarationType(item));
    module = bind(module, (item.constructors ?? []).map(constructor => constructor.name));
  }
  let text = source;
  for (const [start, [end, name]] of [...edits].sort((a, b) => b[0] - a[0])) text = text.slice(0, start) + name + text.slice(end);
  return text;
};

// Before 2026-10-05 every module imported nat without asking. A module of
// a revision that did so (implicitNat), read in today's syntax, imports it,
// unless it is nat or already does: so a baseline sees the names it saw then.
export const historicalSource = (source, module, {
  implicitNat = true, minusReverses = true, importedNames = [], importedDeclarations = [], renaming = historicalRenaming,
} = {}) => {
  const rewritten = currentSyntax(source), text = renameReservedBindings(minusReverses ? reversalsAsTilde(rewritten) : rewritten,
    renaming, { importedNames, importedDeclarations });
  if (module === "nat") return withNatNotation(text);
  if (!implicitNat || /(?:^|\n)\s*import\s+(?:[^;]*,\s*)?nat\s*[;,]/.test(text)) return text;
  return `import nat;\n${text}`;
};
