// `inductive` declarations (work plan L2.1; docs/roadmaps/h1-signature-
// specification.md, section 9): a declaration is lowered to a signature in
// normal form, admitted through the checker, and then used by name. This is
// untrusted elaboration: the kernel checks the normal form, positivity and
// universes, and derives every constructor type again.
import {T,freeNames,substituteTerm,substituteDimension,betaReduce} from "./core.mjs";
import {interval as I} from "./lattice.mjs";

export const INDUCTIVE_TAGS = new Set(["Inductive","InductiveSelf","InductiveConstructor"]);
// Words that are h-levels in a header's result position (section 9).
const MODIFIER_WORDS = new Set(["type","set","prop","trunc"]);
const finiteLevel = level => typeof level === "number" || level?.tag === "Var"
  || (level?.tag === "LConst" && level.tier === 0) || (level?.tag === "LSucc" && finiteLevel(level.level))
  || (level?.tag === "LMax" && finiteLevel(level.left) && finiteLevel(level.right));

// A parameter list's binder groups, in order: (a, b : A) is one group.
function groups(params) {
  const result = [];
  for (const p of params) {
    if (result.length && result.at(-1)[0].group === p.group) result.at(-1).push(p);
    else result.push([p]);
  }
  return result;
}
// The end of a type after its Π binders.
function codomainEnd(type) {
  while (type?.tag === "Pi") type = type.body;
  return type;
}

// Lower and admit a declaration. Returns the admitted record, the former type
// to display, the kernel extensions it carries, and the names it binds.
export function lowerInductive(translator, d, scope) {
  const checker = translator.checker, locate = (error, node) => scope.unit.locate(error, node);
  if (!checker.admitSignature) throw locate(Error("Declared types need the instruction kernel."), d.name);
  const tr = (node, at, expected = null) => translator.term(node, at, expected);
  // A type as the kernel checks it, then with its redexes contracted: the
  // reduction may drop a redex's argument, so the type is checked first.
  const reduced = (node, at) => {
    const type = tr(node, at, null);
    try { at.infer(type); } catch (error) { throw locate(error, node); }
    return betaReduce(type);
  };
  const binding = checker.bindingName?.(d.name.text) ?? d.name.text;
  // The header's parameters: universes as level parameters, then terms.
  let at = scope;
  const levels = [], parameters = [], slots = [];
  for (const group of groups(d.params)) {
    if (group[0].bound) {
      for (const p of group) {
        if (MODIFIER_WORDS.has(p.name.text))
          throw locate(Error(`A universe parameter cannot be named ${p.name.text}: in a declaration's result position that word is an h-level.`), p.name);
        const { name, inner } = translator.universeBinder(p.name, p.bound, at);
        at = inner;
        slots.push({ source: p.name.text, level: levels.length, name });
        levels.push({ source: p.name.text, name });
      }
      continue;
    }
    // A group's shared domain is elaborated once, before any of its names.
    const type = tr(group[0].type, at, null);
    for (const p of group) {
      const name = at.fresh(p.name.text);
      at = translator.sourceBinding(p.name, T.variable(name), at.bind(name, type));
      slots.push({ source: p.name.text, parameter: parameters.length, name });
      parameters.push({ source: p.name.text, name, type });
    }
  }
  const header = d.result?.modifier;
  const modifier = !header ? "type" : header.kind === "trunc" ? { trunc: header.level } : header.kind;
  const declared = d.result?.universe ? translator.levelOf(d.result.universe, at) : null;
  // The sort, a variable while its constructors are elaborated, at the
  // written universe or, without one, UU0, which only the elaborator sees:
  // no data type or arity mentions the sort, so none depends on its level.
  const sortName = at.fresh(d.name.text), sortVariable = T.variable(sortName);
  const placeholder = T.universe(declared ?? { tag: "LConst", tier: 1, value: 0 });
  let inner = at.bind(sortName, placeholder).alias(d.name.text,
    { tag: "InductiveSelf", source: d.name.text, sort: sortVariable, slots });
  const constructors = [], sizes = [];
  for (const c of d.constructors) {
    if (constructors.some(k => k.source === c.name.text))
      throw locate(Error(`${c.name.text} is already a constructor of ${d.name.text}.`), c.name);
    if (c.name.text === d.name.text) throw locate(Error(`A constructor cannot be named ${d.name.text}, as its type is.`), c.name);
    let cs = inner;
    const args = [];
    // Types are beta-reduced: a boundary must be a constructor expression,
    // and an argument is a position by what its type is, not by a redex that
    // mentions the sort (the specification's 1.4).
    for (const group of groups(c.params)) {
      const type = reduced(group[0].type, cs);
      for (const p of group) {
        const name = cs.fresh(p.name.text);
        cs = translator.sourceBinding(p.name, T.variable(name), cs.bind(name, type));
        args.push({ source: p.name.text, name, type, node: p.name });
      }
    }
    let result = c.type ? reduced(c.type, cs) : sortVariable;
    // Binders written in the result, as in s : Nat -> N, are arguments too.
    while (result.tag === "Pi") {
      const name = cs.fresh(result.name);
      cs = cs.bind(name, result.domain);
      args.push({ source: result.name, name, type: result.domain, node: c.name });
      result = substituteTerm(result.body, result.name, T.variable(name));
    }
    // An argument whose type mentions the sort or a position is a position;
    // the rest are data, which the normal form takes first, in source order.
    const positional = new Set([sortName]);
    for (const a of args)
      if ([...freeNames(a.type)].some(name => positional.has(name))) { a.position = true; positional.add(a.name); }
    // A position is an arity, which mentions neither the sort nor a position,
    // then a cube over the sort: the sort itself or a path of cubes.
    for (const a of args.filter(a => a.position)) {
      let t = a.type;
      for (; t?.tag === "Pi"; t = t.body)
        if ([...freeNames(t.domain)].some(name => positional.has(name)))
          throw locate(Error(`${d.name.text} occurs in a negative position: ${c.name.text}'s argument ${a.source} takes `
            + `an argument that mentions ${d.name.text} or another argument of ${c.name.text}.`), a.node);
      while (t?.tag === "Path") t = t.family;
      if (!(t?.tag === "Var" && t.name === sortName))
        throw locate(Error(`${c.name.text}'s argument ${a.source} mentions ${d.name.text} but is not one: in H1 an argument `
          + `is ${d.name.text} itself, a function into it, or a path in it.`), a.node);
    }
    const kernelOrder = [...args.filter(a => !a.position), ...args.filter(a => a.position)];
    let type = result;
    for (const a of [...kernelOrder].reverse()) type = T.pi(a.name, a.type, type);
    let dims = 0;
    for (let r = result; r?.tag === "Path"; r = r.family) dims++;
    // The universes the sort must contain: each data type's, and each
    // position's arity types', before the cube over the sort.
    const levelOf = (type, where, node) => {
      const universe = where.nf(where.infer(type).type);
      if (universe.tag !== "U") throw locate(Error(`The type of ${node.text} is not a type.`), node);
      return universe.level;
    };
    let where = inner;
    for (const a of args) {
      if (!a.position) sizes.push({ level: levelOf(a.type, where, a.node), argument: a.source, constructor: c.name.text });
      else {
        let t = a.type, arity = where;
        while (t?.tag === "Pi" && ![...freeNames(t.domain)].some(name => positional.has(name))) {
          sizes.push({ level: levelOf(t.domain, arity, a.node), argument: a.source, constructor: c.name.text });
          arity = arity.bind(t.name, t.domain);
          t = t.body;
        }
      }
      where = where.bind(a.name, a.type);
    }
    const name = inner.fresh(c.name.text), order = kernelOrder.map(a => args.indexOf(a));
    constructors.push({ source: c.name.text, name, type, order, arity: args.length, dims });
    inner = inner.bind(name, type).alias(c.name.text,
      { tag: "InductiveConstructor", source: c.name.text, head: T.variable(name), order, arity: args.length, dims });
  }
  // The sort's level: written, or the least one containing every data type
  // and arity (2.1); parameters count only through those.
  const level = declared ?? (sizes.length ? sizes.map(size => size.level)
    .reduce((left, right) => ({ tag: "LMax", left, right })) : 0);
  // A universe parameter is recorded when a constructor type mentions it, or
  // when no parameter's type ends in exactly it, so that no instance could
  // read it (1.1); otherwise it is erased.
  const recorded = levels.map(l => constructors.some(c => freeNames(c.type).has(l.name)) || !parameters.some(p => {
    const end = codomainEnd(p.type);
    return end?.tag === "U" && end.level?.tag === "Var" && end.level.name === l.name;
  }));
  const spec = { name: binding, sort: sortName, level, modifier,
    levels: levels.map((l, j) => ({ name: l.name, recorded: recorded[j] })),
    parameters: parameters.map(p => ({ name: p.name, type: p.type })),
    constructors: constructors.map(c => ({ name: c.name, type: c.type, display: c.source })) };
  let record;
  try { record = checker.admitSignature(spec); }
  catch (error) {
    // A declared universe below a data type's is lowering: name the argument.
    if (declared !== null && (error.kind === "mismatch" || /universe|cumulative|not included/i.test(error.message))) {
      const lowered = sizes.find(size => !checker.levelWithin?.(size.level, declared));
      if (lowered) throw locate(Object.assign(Error(`${lowered.constructor}'s argument ${lowered.argument} lives in a universe above ${d.name.text}'s declared one: a declared type cannot lower its data (K2.5).`), { kind: error.kind }), d.name);
    }
    const constructor = d.constructors.find(c => c.name.text === error.constructor);
    throw locate(error, constructor?.name ?? d.name);
  }
  const inductive = { tag: "Inductive", source: d.name.text, binding, record, slots,
    levels: levels.map((l, j) => ({ name: l.name, recorded: recorded[j] })), parameters,
    // Each user constructor's argument order, arity and dimensions, for match.
    constructors: constructors.map(c => ({ order: c.order, arity: c.arity, dims: c.dims })) };
  // Registered by signature, for a match whose type's name is shadowed.
  checker.inductives?.set(binding, inductive);
  // A truncated sort's generated constructor is T.squash (section 9): its
  // positions, the pairs of parallel cells, in the kernel's order.
  const entries = [[d.name.text, inductive], ...constructors.map((c, index) => [c.source,
    { tag: "InductiveConstructor", source: c.source, inductive, index, order: c.order, arity: c.arity, dims: c.dims }])];
  const generated = checker.kernel?.signature(record.index).constructors.at(-1);
  if (generated?.generated) {
    const arity = generated.data + generated.positions;
    entries.push([`${d.name.text}.squash`, { tag: "InductiveConstructor", source: `${d.name.text}.squash`, inductive,
      index: constructors.length, order: Array.from({ length: arity }, (_, i) => i), arity, dims: generated.dimensions }]);
  }
  return { record, former: checker.signatureFormer?.(record) ?? null, extensions: checker.signatureExtensions?.(record) ?? [], entries };
}

const identity = order => order.every((position, index) => position === index);
// Several names substituted at once: each first becomes a placeholder that no
// term can spell, so a value that mentions another of the names, as an
// importer's variable may, is never substituted into.
function substituteAll(term, pairs) {
  const placeholders = pairs.map((_, index) => `\u0000slot${index}`);
  const renamed = pairs.reduce((t, [name], index) => substituteTerm(t, name, T.variable(placeholders[index])), term);
  return pairs.reduce((t, [, value], index) => substituteTerm(t, placeholders[index], value), renamed);
}

// A declared name used as a term: the sort, alone or applied to its
// arguments, inside its declaration or after it, or a constructor, applied to
// its arguments in the order the source wrote them.
export function resolveInductive(translator, node, value, args, scope, expected) {
  const locate = error => scope.unit.locate(error, node);
  const shown = term => translator.shown(term);
  const reference = term => { translator.reference(scope, node, term); return term; };
  if (value.tag === "InductiveSelf") {
    const names = value.slots.map(slot => slot.source).join(", ");
    if (!value.slots.length && !args) return reference(value.sort);
    // The parameters are uniform: inside its declaration, the sort is applied
    // to exactly its own parameters, as they are bound there.
    const own = args?.length === value.slots.length && args.every((arg, index) => {
      const slot = value.slots[index], bound = arg.kind === "name" && scope.env.get(arg.name);
      return slot.level !== undefined ? bound?.tag === "U" && bound.level?.tag === "Var" && bound.level.name === slot.name
        : bound?.tag === "Var" && bound.name === slot.name;
    });
    if (!own) throw locate(Error(value.slots.length
      ? `Inside its declaration, ${value.source} is applied to its own parameters, ${value.source}(${names}): another argument would be an index, which H1 does not admit.`
      : `${value.source} takes no arguments.`));
    return reference(value.sort);
  }
  if (value.tag === "Inductive") {
    const names = value.slots.map(slot => slot.source).join(", ");
    if (!args) {
      if (!value.slots.length) return reference(T.sort(value.binding));
      // Used as a function, the type former is a lambda over its slots, as
      // fun (U < UU0) => Pointed(U): each slot's type at the earlier ones.
      const binders = [], parameters = [], levels = [];
      const substitution = [];
      for (const slot of value.slots) {
        const name = scope.fresh(slot.source), variable = T.variable(name);
        if (slot.level !== undefined) {
          binders.push({ level: true, name });
          if (value.levels[slot.level].recorded) levels.push(variable);
        } else {
          binders.push({ name, type: substituteAll(value.parameters[slot.parameter].type, substitution) });
          parameters.push(variable);
        }
        substitution.push([slot.name, variable]);
      }
      let body = T.sort(value.binding, parameters, levels);
      for (const binder of binders.reverse()) body = binder.level ? T.levelLambda(binder.name, body) : T.lam(binder.name, binder.type, body);
      return reference(body);
    }
    if (args.length !== value.slots.length)
      throw locate(Error(`${value.source} takes ${value.slots.length} argument${value.slots.length === 1 ? "" : "s"}: ${value.source}(${names}).`));
    // Each argument is checked against the telescope, at the levels and the
    // parameters before it. A recorded level is kept; an erased one only
    // checks, as instances read it from their parameters.
    const substitution = [], parameters = [], levels = [];
    const instantiate = type => substituteAll(type, substitution);
    value.slots.forEach((slot, index) => {
      const arg = args[index];
      if (slot.level !== undefined) {
        const level = translator.levelOf(arg, scope);
        if (!finiteLevel(level))
          throw scope.unit.locate(Error("A universe argument must lie below UU0: U0, U1, … or a universe variable."), arg);
        substitution.push([slot.name, level]);
        if (value.levels[slot.level].recorded) levels.push(level);
        return;
      }
      const type = instantiate(value.parameters[slot.parameter].type);
      const term = translator.term(arg, scope, type);
      scope.check(term, type);
      substitution.push([slot.name, term]);
      parameters.push(term);
    });
    return reference(T.sort(value.binding, parameters, levels));
  }
  // A constructor. Inside its declaration it is a variable; after it, its
  // instance is the only one there is, or the expected type's.
  let head = value.head;
  if (!head) {
    const inductive = value.inductive;
    let instance = inductive.slots.length ? null : T.sort(inductive.binding);
    // Without an expected type, an argument of this type names the instance:
    // only a position can have it, and positions are at the instance.
    if (!instance && !expected && args) {
      const quiet = scope.withUnit(scope.unit.with({ references: null }));
      for (const arg of args) {
        try {
          const type = scope.nf(scope.infer(translator.term(arg, quiet, null)).type);
          if (type.tag === "Sort" && type.signature === inductive.binding) { instance = type; break; }
        } catch { /* Not inferable alone: the next argument may be. */ }
      }
    }
    if (!instance) {
      if (!expected) throw locate(Error(`${value.source} needs an expected type, to know which ${inductive.source}(…) it builds: `
        + `write typed(${inductive.source}(…), ${value.source}${value.arity ? "(…)" : ""}).`));
      let type = scope.nf(expected);
      for (let missing = value.arity - (args?.length ?? 0); missing > 0; missing--) {
        if (type.tag !== "Pi") break;
        type = scope.nf(type.body);
      }
      // The instance does not vary along the constructor's dimensions: each
      // path's family is read at an endpoint, where it names no dimension.
      for (let d = 0; d < value.dims && type.tag === "Path"; d++) type = scope.nf(substituteDimension(type.family, type.dim, I.zero));
      if (type.tag !== "Sort" || type.signature !== inductive.binding)
        throw locate(Error(`${value.source} builds ${inductive.source}(…), but ${shown(type)} is expected here.`));
      instance = type;
    }
    head = T.constructor(value.index, instance, value.source);
  }
  if (!args) {
    if (!identity(value.order))
      throw locate(Error(`Apply ${value.source} to its ${value.arity} arguments: the kernel takes its data before its positions.`));
    return reference(head);
  }
  if (args.length > value.arity)
    throw locate(Error(`${value.source} takes ${value.arity} argument${value.arity === 1 ? "" : "s"}; apply a path constructor at a coordinate with @.`));
  if (args.length < value.arity && !identity(value.order))
    throw locate(Error(`Apply ${value.source} to all its ${value.arity} arguments: the kernel takes its data before its positions.`));
  const ordered = args.length === value.arity ? value.order.map(index => args[index]) : args;
  let fn = reference(head);
  for (const arg of ordered) {
    const pi = scope.nf(scope.infer(fn).type);
    if (pi.tag !== "Pi") throw locate(Error(`${value.source} takes fewer arguments.`));
    fn = T.app(fn, translator.term(arg, scope, pi.domain));
  }
  return fn;
}
