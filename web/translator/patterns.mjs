// Pattern matching beyond one value and flat clauses (work plan L2.2a): a
// match on several values, `match x, y { nil, _ => …; … }`, and clauses
// whose patterns are nested, `cons(x, cons(y, rest))`, or a variable or _
// in a constructor's place. Compiled, as patterns usually are, value by
// value into matches on one value each, which match.mjs elaborates against
// the kernel's clause types: nothing here is trusted.
//
// The clauses are tried in order, the first that fits taking a case. A
// value whose patterns are all variables or _ is not taken apart: each
// variable names it. Otherwise the match takes it apart by its declared
// type's constructors, and each constructor's clause matches the rest: the
// constructor's arguments, then the other values, against the clauses that
// fit it, where a variable or _ fits every constructor and names it there.
// A constructor no clause fits is a missing case, and a clause that takes no
// case is never reached: both are refused. A bare name in a pattern is a
// constructor of the type matched there when it has one by that name without
// arguments, and otherwise a variable.

// The environment key of the declaration's own name (match.mjs, RECURSIVE).
const RECURSIVE = "\u0000recursive";

// A head of the parser with neither arguments, coordinates nor binders.
const bare = head => !head.args && !head.coordinates?.length && !head.binders?.length;

// Whether a match needs compiling: several values, a nested pattern, _, a
// constructor without arguments in an argument's place, a bare name that is
// no constructor of the value's type, or a constructor's clause twice. A
// legacy clause with names after its constructor, as `succ h =>`, is
// match.mjs's.
export function needsCompiling(n, constructorNames, scope) {
  if (n.values?.length > 1) return true;
  const heads = n.clauses ?? [];
  if (heads.some(head => head.binders?.length)) return false;
  const seen = new Set();
  for (const head of heads) {
    if (head.args?.some(arg => arg.kind === "pattern" || arg.text === "_" || constructorWithout(scope, arg.text))) return true;
    if (bare(head) && !constructorNames.has(head.constructor.text)) return true;
    if (seen.has(head.constructor.text)) return true;
    seen.add(head.constructor.text);
  }
  return false;
}

// A pattern: {kind: "name", token} or {kind: "constructor", token, args,
// coordinates}.
const pattern = head => head.kind === "pattern" || !bare(head)
  ? { kind: "constructor", token: head.constructor, args: (head.args ?? []).map(argument), coordinates: head.coordinates ?? [] }
  : { kind: "name", token: head.constructor };
const argument = arg => arg.kind === "pattern" ? pattern(arg) : { kind: "name", token: arg };
const wildcard = { kind: "name", token: { text: "_" } };

let serial = 0;
// A name no source spells, for an argument the compiled match binds.
const generatedToken = (stem, at) => ({ text: `${stem}'${++serial}`, start: at.start, end: at.end });

// Compile and elaborate the match `n`: an expression at its expected type,
// or a statement for its goal. `typeOf(value, scope)` gives the declared
// type of a value's term, {source, instance, constructors: [{name, arity,
// dims, fields}]}, without its generated constructor, or null.
export function compileMatch(t, n, scope, {statement, expected, goal, typeOf}) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const values = n.values ?? [n.value];
  // Each clause, with the names its patterns bind so far.
  const clauses = n.clauses.map(clause => ({ clause, used: false }));
  const rows = clauses.map(origin => {
    const patterns = [origin.clause, ...origin.clause.more ?? []].map(pattern);
    if (patterns.length !== values.length)
      throw locate(Error(`This clause has ${patterns.length} pattern${patterns.length === 1 ? "" : "s"}; the match takes apart ${values.length} value${values.length === 1 ? "" : "s"}.`), origin.clause.constructor);
    return { patterns, bindings: [], origin };
  });
  const columns = values.map(node => ({ node, describe: scope.unit.source.slice(node.start, node.end).trim() }));
  const context = { n, statement, typeOf, locate, top: true };
  const result = compile(t, scope, columns, rows, { ...context, expected, goal });
  const unreached = clauses.find(origin => !origin.used);
  if (unreached) throw locate(Error("This clause is never reached: the clauses before it take every case it would."), unreached.clause.constructor);
  return result;
}

function compile(t, scope, columns, rows, context) {
  const {statement, locate} = context;
  // Nothing left to take apart: the first clause that fits.
  if (!columns.length) {
    const [row] = rows;
    row.origin.used = true;
    let inner = scope;
    for (const [token, target] of row.bindings) inner = bind(t, inner, token, target);
    return statement ? t.block(row.origin.clause.body, context.goal.at(inner)) : t.term(row.origin.clause.body, inner, context.expected);
  }
  const [column, ...others] = columns;
  const value = t.term(column.node, scope, null), type = context.typeOf(value, scope);
  const byName = new Map((type?.constructors ?? []).map(constructor => [constructor.name, constructor]));
  // A bare name is a constructor of this type without arguments, if it has
  // one by that name, and otherwise a variable.
  const resolved = rows.map(row => {
    const [first, ...rest] = row.patterns;
    const nullary = first.kind === "name" && byName.get(first.token.text);
    const head = nullary && !nullary.arity && !nullary.dims || !type && first.kind === "name" && constructorWithout(scope, first.token.text)
      ? { kind: "constructor", token: first.token, args: [], coordinates: [] } : first;
    if (head.kind === "constructor" && !type)
      throw locate(Error(`${column.describe} is not of a declared type: its patterns are variables or _.`), head.token);
    if (head.kind === "constructor" && !byName.has(head.token.text))
      throw locate(Error(`${type.source} has no constructor ${head.token.text}: its constructors are ${type.constructors.map(c => c.name).join(", ")}.`), head.token);
    return { row, head, rest };
  });
  // No constructor here: each variable names the value.
  if (resolved.every(({head}) => head.kind === "name"))
    return compile(t, scope, others, resolved.map(({row, head, rest}) => ({ ...row, patterns: rest,
      bindings: head.token.text === "_" ? row.bindings : [...row.bindings, [head.token, { node: column.node }]] })), context);
  // Take the value apart: a clause per constructor, matching the rest.
  const clauses = [];
  for (const constructor of type.constructors) {
    const fitting = resolved.filter(({head}) => head.kind === "name" || head.token.text === constructor.name);
    if (!fitting.length) {
      // A path constructor no clause covers is match.mjs's to report, as
      // obligations may give it.
      if (constructor.dims) continue;
      throw locate(Error(`The match has no case for ${constructor.name}${constructor.arity ? "(…)" : ""} in ${column.describe}.`));
    }
    for (const {head} of fitting) if (head.kind === "constructor") {
      if (head.args.length !== constructor.arity)
        throw locate(Error(`${constructor.name} takes ${constructor.arity} argument${constructor.arity === 1 ? "" : "s"} here: ${constructor.name}(…) with ${constructor.arity} names.`), head.token);
      if (head.coordinates.length !== constructor.dims)
        throw locate(Error(constructor.dims ? `${constructor.name} is a path constructor: name its ${constructor.dims} dimension${constructor.dims === 1 ? "" : "s"} after its arguments.`
          : `${constructor.name} has no dimensions to name.`), head.token);
    }
    const first = fitting.find(({head}) => head.kind === "constructor")?.head, at = first?.token ?? column.node;
    // An argument is named as every clause that takes it apart names it, or
    // else by a name of its own, from the constructor's name for it. A name
    // that is a constructor without arguments is a pattern, which its own
    // type decides.
    const variable = arg => arg.kind === "name" && arg.token.text !== "_" && !constructorWithout(scope, arg.token.text);
    const args = Array.from({ length: constructor.arity }, (_, k) => {
      const names = new Set(fitting.map(({head}) => head.kind === "constructor" && variable(head.args[k]) ? head.args[k].token.text : null));
      const [only] = names;
      return names.size === 1 && only !== null ? first.args[k].token
        : generatedToken(constructor.fields?.[k] ?? "x", at);
    });
    const coordinates = Array.from({ length: constructor.dims }, (_, k) => first?.coordinates[k] ?? generatedToken("i", at));
    const specialized = fitting.map(({row, head, rest}) => {
      if (head.kind === "name") {
        // A variable names the constructor here; _ names nothing.
        const bindings = head.token.text === "_" ? row.bindings
          : [...row.bindings, [head.token, { constructor, args, coordinates, instance: type.instance }]];
        return { ...row, patterns: [...Array.from({ length: constructor.arity }, () => wildcard), ...rest], bindings };
      }
      // The clause's own arguments are matched next; its coordinates name
      // the clause's.
      const bindings = [...row.bindings];
      head.coordinates.forEach((coordinate, k) => {
        if (coordinate.text !== coordinates[k].text) bindings.push([coordinate, { dimension: coordinates[k] }]);
      });
      return { ...row, patterns: [...head.args.map((arg, k) => arg.kind === "name" && arg.token.text === args[k].text ? wildcard : arg), ...rest], bindings };
    });
    // A generated argument is described by the constructor's name for it.
    const argumentColumns = args.map((arg, k) => ({ node: { kind: "name", name: arg.text, start: arg.start, end: arg.end },
      describe: arg.text.includes("'") ? `the ${constructor.fields?.[k] ?? `argument ${k + 1}`} of ${column.describe}` : arg.text }));
    const rest = { kind: statement ? "patternMatchStatement" : "patternMatch", columns: [...argumentColumns, ...others],
      rows: specialized, context: { ...context, top: false }, start: column.node.start, end: column.node.end };
    clauses.push({ kind: "clause", constructor: { text: constructor.name, start: at.start, end: at.end }, args, binders: [], coordinates,
      body: statement ? [rest] : rest, start: at.start, end: at.end });
  }
  // The first value taken apart is matched by the declaration's own match,
  // so recursion follows it (match.mjs, recursionSite).
  const top = context.top ? context.n : null;
  const node = { kind: statement ? "matchStatement" : "match", value: column.node, clauses,
    ...(top?.type ? { type: top.type } : {}), ...(top ? obligationsOf(top) : {}), start: column.node.start, end: column.node.end };
  const recursive = scope.env.get(RECURSIVE), at = top && recursive?.site === top ? scope.alias(RECURSIVE, { ...recursive, site: node }) : scope;
  return statement ? t.block([node], context.goal.at(at)) : t.term(node, at, context.expected);
}

const obligationsOf = node => Object.fromEntries(["obligations", "obligationProof", "obligationsToken"]
  .filter(key => node[key] !== undefined).map(key => [key, node[key]]));

// Bind a clause's name to what it stands for: a value, a dimension, or a
// constructor at the clause's arguments and coordinates.
function bind(t, scope, token, target) {
  if (target.dimension) return scope.alias(token.text, scope.env.get(target.dimension.text));
  if (target.node) {
    // A value that is a name keeps its binding, so that recursion sees the
    // parameter it is.
    const {node} = target;
    return scope.alias(token.text, node.kind === "name" && scope.env.has(node.name) ? scope.env.get(node.name) : t.term(node, scope, null));
  }
  const {constructor, args, coordinates, instance} = target;
  let point = args.length ? { kind: "call", fn: { kind: "name", name: constructor.name }, args: args.map(arg => ({ kind: "name", name: arg.text })) }
    : { kind: "name", name: constructor.name };
  for (const coordinate of coordinates) point = { kind: "pathApply", left: point, right: { kind: "name", name: coordinate.text } };
  return scope.alias(token.text, t.term(point, scope, instance));
}

// Whether a name is, in scope, a constructor without arguments.
const constructorWithout = (scope, name) => {
  const bound = scope.env.get(name);
  return bound?.tag === "InductiveConstructor" && !bound.arity && !bound.dims;
};

// The rest of a compiled match, in a clause of the match it compiled to.
export function continueMatch(t, node, scope, {expected, goal}) {
  return compile(t, scope, node.columns, node.rows, { ...node.context, expected, goal });
}
