// Homomorphisms and isomorphisms of a theory's models (L2.4, the fourth
// slice of docs/roadmaps/core-theories.md): the source of their
// declarations, from the theory's record (theories.mjs), which parses it.
//
//   T.Hom(A, B)            a map for each carrier, map_S : A.S -> B.S (map
//                          when there is one), for a family at each index,
//                          map_F : forall i. A.F(i) -> B.F(i'), and for each
//                          operation and constant f that the maps preserve
//                          it, map_f;
//   T.Hom.make, f.map …    its constructor and projections;
//   T.Hom.id(A), T.Hom.compose(g, f), and f.p, the homomorphism of each
//                          parent's models;
//   T.Iso(A, B)            a homomorphism each way, to and from, inverse on
//                          each carrier and on each family of sets at each
//                          index: from_to and to_from;
//   T.Iso.make, f.to …     its constructor and projections;
//   T.Iso.id(A), T.Iso.compose(g, f), T.Iso.inverse(f).
//
// An operation's preservation relates its inputs in A to its inputs in B,
// by where the carriers sit in each input's type (L2.4c): an input with no
// carrier is the same value on both sides; a covariant one, with carriers
// right of every arrow, is pushed forward along the maps, A's to B's; a
// contravariant one, with carriers left of an arrow, is pulled back, B's to
// A's. Its result is pushed forward:
//   forall x : A.X, k : B.X -> Real. push(A.f(x, pull(k))) = B.f(push(x), k).
// Pushing and pulling follow the type's arrows and pairs, so along a
// composite they are the two maps in turn, and preservation composes. An
// input with carriers on both sides of an arrow, as g : M -> M, would need
// a hypothesis relating A's and B's values, and such homomorphisms need not
// compose: a theory with one has none. Laws need no field, being
// propositions about sets.
//
// A family's member, F(i…), is a carrier whose indices are the operation's
// own arguments; its map at those indices pushes it, and an index that is
// an element of a carrier is pushed too: a homomorphism of preorders maps
// le(x, y) to le(map(x), map(y)). An argument's type may name an earlier
// argument that is the same on both sides or pushed forward, as a monad's
// m : F(A) names A.

// The names a type mentions free; a qualified name, R.R, by its root.
function freeNames(node, bound = new Set(), out = new Set()) {
  if (Array.isArray(node)) { for (const item of node) freeNames(item, bound, out); return out; }
  if (!node || typeof node !== "object") return out;
  if (node.kind === "name") {
    const root = node.name.split(".")[0];
    if (!bound.has(root)) out.add(root);
    return out;
  }
  const binders = node.kind === "binderGroup" ? node.names.map(n => n.text)
    : ["forall", "exists", "lambda"].includes(node.kind) && node.name?.text ? [node.name.text] : [];
  for (const [key, value] of Object.entries(node)) {
    if (!value || typeof value !== "object") continue;
    freeNames(value, binders.length && key === "body" ? new Set([...bound, ...binders]) : bound, out);
  }
  return out;
}

// How a type is mapped: "fixed" when it mentions no carrier; a carrier, or
// a family's member, whose index that is an element of a carrier is a name
// the operation binds and whose other indices are terms over its
// arguments, as V(m + n); an arrow or a pair of shapes; or another form,
// which the maps do not follow.
function shapeOf(type, context) {
  const { carriers, families, fields } = context;
  if (![...freeNames(type)].some(name => carriers.has(name))) return { kind: "fixed", type };
  if (type.kind === "name" && carriers.has(type.name) && !families.has(type.name)) return { kind: "carrier", sort: type.name, type };
  const indices = type.kind === "call" && type.fn.kind === "name" ? families.get(type.fn.name) : null;
  if (indices && type.args.length === indices.length && type.args.every((arg, k) => indices[k].shape.kind === "carrier"
    ? arg.kind === "name" && !fields.has(arg.name) : ![...freeNames(arg)].some(name => fields.has(name))))
    return { kind: "carrier", sort: type.fn.name, args: type.args, type };
  if (type.kind === "binary" && type.operator === "->")
    return { kind: "arrow", from: shapeOf(type.left, context), to: shapeOf(type.right, context), type };
  if (type.kind === "forall" && !freeNames(type.body).has(type.name.text))
    return { kind: "arrow", from: shapeOf(type.domain, context), to: shapeOf(type.body, context), type };
  if (type.kind === "binary" && type.operator === "and")
    return { kind: "pair", left: shapeOf(type.left, context), right: shapeOf(type.right, context), type };
  return { kind: "other", type };
}
// Where carriers occur in a shape: positively, negatively, or in a form
// the maps do not follow.
function occurrences(shape, positive = true, out = new Set()) {
  if (shape.kind === "carrier") out.add(positive ? "+" : "-");
  if (shape.kind === "other") out.add("other");
  if (shape.kind === "arrow") { occurrences(shape.from, !positive, out); occurrences(shape.to, positive, out); }
  if (shape.kind === "pair") { occurrences(shape.left, positive, out); occurrences(shape.right, positive, out); }
  return out;
}
// A field's binders, from its type's foralls, and the type under them.
function binders(type) {
  const list = [];
  while (type.kind === "forall") { list.push({ name: type.name.text, type: type.domain }); type = type.body; }
  return { list, body: type };
}
// An operation's inputs and result, each with its shape and way, "fixed",
// "push" or "pull"; or, as `why`, why its homomorphisms are not generated.
function operationShape(field, context) {
  const { list: inputs, body: type } = binders(field.type);
  const way = (shape, place) => {
    const where = occurrences(shape);
    if (where.has("other")) return { why: `its ${field.name}'s ${place} has a type that the maps do not follow` };
    if (where.has("+") && where.has("-"))
      return { why: `its ${field.name}'s ${place} mentions a carrier on both sides of an arrow, and such homomorphisms need not compose` };
    return { way: where.has("+") ? "push" : where.has("-") ? "pull" : "fixed" };
  };
  for (const input of inputs) {
    input.shape = shapeOf(input.type, context);
    const { why, way: inputWay } = way(input.shape, `argument ${input.name}`);
    if (why) return { why };
    input.way = inputWay;
  }
  const result = { type, shape: shapeOf(type, context) };
  const { why, way: resultWay } = way(result.shape, "result");
  if (why) return { why };
  if (resultWay === "pull")
    return { why: `its ${field.name}'s result mentions a carrier left of an arrow, which a homomorphism cannot carry forward` };
  result.way = resultWay;
  // A part of a type that is the same on both sides, a family's index
  // among them, cannot name an input that is pushed forward: on B's side
  // that input is another value.
  const fixedParts = (shape, out = []) => {
    if (shape.kind === "fixed") out.push(shape.type);
    if (shape.kind === "carrier" && shape.args)
      shape.args.forEach((arg, k) => { if (context.families.get(shape.sort)[k].shape.kind === "fixed") out.push(arg); });
    if (shape.kind === "arrow") { fixedParts(shape.from, out); fixedParts(shape.to, out); }
    if (shape.kind === "pair") { fixedParts(shape.left, out); fixedParts(shape.right, out); }
    return out;
  };
  const pushed = new Set(inputs.filter(input => input.way === "push").map(input => input.name));
  for (const part of [...inputs, result].flatMap(item => fixedParts(item.shape)))
    if ([...freeNames(part)].some(name => pushed.has(name)))
      return { why: `a type in its ${field.name} names an argument that is pushed forward, on B's side another value` };
  // A pulled input is B's: no type may name it, and its own names none.
  for (const [k, input] of inputs.entries()) {
    const later = [...inputs.slice(k + 1).map(other => other.type), type];
    if (input.way === "pull" && (later.some(t => freeNames(t).has(input.name))
      || inputs.slice(0, k).some(earlier => freeNames(input.type).has(earlier.name))))
      return { why: `its ${field.name}'s argument ${input.name} is pulled back and depends on, or is named by, another argument` };
  }
  return { inputs, result };
}

// A parameter's type stands in a homomorphism's source as a marker, which
// the expansion replaces by the type (theories.mjs).
const parameterMarker = k => `__theory_parameter_${k}`;

// The declarations of T's homomorphisms and isomorphisms, each {name,
// source, role}, or, as `missing`, why T's models have none. `isTheory`
// says whether a name is a theory in scope. `universes` are the models'
// universes, or the first model's, in which a parameter's type is written.
export function morphismSource(record, isTheory = () => false) {
  const T = record.name, hom = `${T}.Hom`, iso = `${T}.Iso`;
  // The source's models, A, B and C, and homomorphisms, f and g. A theory's
  // name begins its qualified names, as A.M, which a binder of that name
  // would not shadow, so each avoids every theory in scope, T included, and
  // every name the fields' types bind, which the source keeps.
  // Every model of a theory with parameters shares them, and its universes:
  // a homomorphism keeps them fixed (L2.4c). Otherwise each model has its
  // own universes, as many as the theory's header binds.
  const params = record.params ?? [], count = Math.max(1, record.universes?.length ?? 0);
  const taken = new Set([...params.map(p => p.name), ...record.fields.flatMap(field => binders(field.type).list.map(b => b.name))]);
  const own = stem => {
    let name = stem;
    for (let k = 1; name === T || isTheory(name) || taken.has(name); k++) name = `${stem}${k}`;
    taken.add(name);
    return name;
  };
  const A = own("A"), B = own("B"), C = own("C"), f = own("f"), g = own("g"), X = own("x"), Y = own("y");
  const carrierFields = record.fields.filter(field => field.kind === "sort"), sorts = carrierFields.map(field => field.name);
  if (!sorts.length) return { missing: `${T} has no sorts` };
  // A carrier with no h-level has paths that are data: its homomorphisms
  // would need coherence fields, which are not specified (L2.4c).
  const levelOf = sort => record.fields.find(field => field.kind === "evidence" && field.of === sort)?.evidence ?? null;
  const untruncated = sorts.find(sort => !levelOf(sort));
  if (untruncated) return { missing: `its carrier ${untruncated} has no h-level, and homomorphisms of such a carrier need coherences that are not generated` };
  const carriers = new Set(sorts), fields = new Set(record.fields.map(field => field.name));
  // A family's indices, each the same on both sides or an element of a
  // carrier, pushed forward.
  const families = new Map();
  for (const field of carrierFields.filter(field => field.family)) {
    const indices = binders(field.type).list;
    for (const index of indices) {
      index.shape = shapeOf(index.type, { carriers, families, fields });
      if (!["fixed", "carrier"].includes(index.shape.kind) || index.shape.args)
        return { missing: `its family ${field.name}'s index ${index.name} is neither the same on both sides nor an element of a carrier` };
    }
    families.set(field.name, indices);
  }
  const context = { carriers, families, fields }, operations = new Map();
  for (const field of record.fields.filter(field => field.kind === "operation")) {
    const shape = operationShape(field, context);
    if (shape.why) return { missing: shape.why };
    operations.set(field.name, { name: field.name, ...shape });
  }
  // A type that names the theory's universe, as an index A : U does, is
  // the same on both sides only in one universe: such a theory's
  // homomorphisms relate models in the same universes, as a parameter's
  // do, and lie one universe up.
  const universal = [...[...operations.values()].flatMap(op => [...op.inputs.map(i => i.type), op.result.type]),
    ...[...families.values()].flat().map(index => index.type)]
    .some(type => [...freeNames(type)].some(name => name.startsWith("\u0000universe")));
  // Each model's universes: U, V and W, or U_1, U_2, … when there are
  // several (U1 is a universe constant); the shared ones are U's.
  const universesOf = letter => count === 1 ? [own(letter)] : Array.from({ length: count }, (_, k) => own(`${letter}_${k + 1}`));
  const [uA, uB, uC] = params.length || universal ? Array(3).fill(universesOf("U")) : [universesOf("U"), universesOf("V"), universesOf("W")];
  const map = sort => sorts.length === 1 ? "map" : `map_${sort}`;
  // A homomorphism's fields, in the theory's order: a map for each carrier,
  // and that the maps preserve each operation and constant.
  const homFields = record.fields.flatMap(field => field.kind === "sort" ? [{ name: map(field.name), sort: field.name }]
    : field.kind === "operation" ? [{ name: `map_${field.name}`, operation: operations.get(field.name) }] : []);
  if (new Set(homFields.map(field => field.name)).size !== homFields.length)
    return { missing: "two of its homomorphisms' fields would have one name" };
  const applied = (fn, args) => args.length ? `${fn}(${args.join(", ")})` : fn;
  // A type written in a model, as a marker that the expansion replaces by
  // the type, its fields that model's and its universes the model's.
  const typeMarkers = new Map();
  const typeIn = (type, model) => {
    const marker = `__theory_type_${typeMarkers.size}`;
    typeMarkers.set(marker, { type, model, universes: model === A ? uA : model === B ? uB : uC });
    return marker;
  };
  // A side of a homomorphism, or of a composite: its model, and how an
  // index named by an operation reads there, the maps that brought it.
  const side = (model, maps = []) => ({ model, maps });
  const along = (from, to, mapOf) => ({ from, to: side(to.model ?? to, [...from.maps, mapOf]), mapOf });
  // The k-th index of a family F, `arg` read at a side: an element of a
  // carrier, a name, is carried along each map that brought it there, and
  // another index is the same term on every side.
  const indexAt = (F, k, arg, at) => {
    const index = families.get(F)[k];
    if (typeof arg !== "string" && arg.kind !== "name") return typeIn(arg, at.model);
    const name = typeof arg === "string" ? arg : arg.name;
    return index.shape.kind === "carrier" ? at.maps.reduce((term, mapOf) => `${mapOf(index.shape.sort)}(${term})`, name) : name;
  };
  // A shape's type at a side.
  const typeAt = (shape, at) => {
    if (shape.kind === "fixed") return typeIn(shape.type, at.model);
    if (shape.kind === "carrier") return shape.args ? `${at.model}.${shape.sort}(${shape.args.map((a, k) => indexAt(shape.sort, k, a, at)).join(", ")})` : `${at.model}.${shape.sort}`;
    if (shape.kind === "arrow") return `(${typeAt(shape.from, at)}) -> ${typeAt(shape.to, at)}`;
    return `(${typeAt(shape.left, at)}) and (${typeAt(shape.right, at)})`;
  };
  // Pushing a value of a shape along a step, from one side to the next, and
  // pulling one back; each lambda's binder is fresh.
  let locals = 0;
  const local = () => own(`v${++locals}`);
  const push = (shape, term, step) => {
    if (shape.kind === "fixed") return term;
    if (shape.kind === "carrier")
      return `${step.mapOf(shape.sort)}(${[...(shape.args ?? []).map((a, k) => indexAt(shape.sort, k, a, step.from)), term].join(", ")})`;
    // A pair is typed, since an equation's side is elaborated before its type is known.
    if (shape.kind === "pair")
      return `typed(${typeAt(shape, step.to)}, (${push(shape.left, `(${term}).1`, step)}, ${push(shape.right, `(${term}).2`, step)}))`;
    const v = local();
    return `fun (${v} : ${typeAt(shape.from, step.to)}) => ${push(shape.to, `(${term})(${pull(shape.from, v, step)})`, step)}`;
  };
  const pull = (shape, term, step) => {
    if (shape.kind === "fixed") return term;
    if (shape.kind === "pair")
      return `typed(${typeAt(shape, step.from)}, (${pull(shape.left, `(${term}).1`, step)}, ${pull(shape.right, `(${term}).2`, step)}))`;
    const v = local();
    return `fun (${v} : ${typeAt(shape.from, step.from)}) => ${pull(shape.to, `(${term})(${push(shape.from, v, step)})`, step)}`;
  };
  // An input's binder over a step: a pulled input ranges over the step's
  // end, the others over its start.
  const binder = (input, step) => `${input.name} : ${input.way === "pull" ? typeAt(input.shape, step.to) : typeAt(input.shape, step.from)}`;
  const quantified = (items, body) => items.map(item => `forall ${item}. `).join("") + body;
  // A homomorphism's map of a carrier, as a function: T.Hom.map(h).
  const mapping = (h, sort) => `${hom}.${map(sort)}(${h})`;
  // That `step` preserves an operation.
  const preservation = (operation, step) => {
    const { name, inputs, result } = operation;
    const left = applied(`${step.from.model}.${name}`, inputs.map(input => input.way === "pull" ? pull(input.shape, input.name, step) : input.name));
    const right = applied(`${step.to.model}.${name}`, inputs.map(input => input.way === "push" ? push(input.shape, input.name, step) : input.name));
    return quantified(inputs.map(input => binder(input, step)), `${push(result.shape, left, step)} = ${right}`);
  };
  // A family's map: at each index, read at the step's start, its members
  // carried to the members at the indices carried along.
  const familyMap = (sort, step) => {
    const indices = families.get(sort), member = { kind: "carrier", sort, args: indices.map(index => index.name) };
    return quantified(indices.map(index => `${index.name} : ${typeAt(index.shape, step.from)}`), `${typeAt(member, step.from)} -> ${typeAt(member, step.to)}`);
  };
  // The type of a homomorphism field over A and B, `mapOf(sort)` the maps.
  const fieldType = (field, mapOf) => {
    const step = along(side(A), side(B), mapOf);
    if (field.sort) return families.has(field.sort) ? familyMap(field.sort, step) : `${A}.${field.sort} -> ${B}.${field.sort}`;
    return preservation(field.operation, step);
  };
  // A Σ of fields, the last one bare; a tuple of values.
  const sigma = (fields, typeOf) => fields.map((field, k) => k === fields.length - 1 ? typeOf(field)
    : `exists ${field.name} : (${typeOf(field)}). `).join("");
  const tuple = values => values.length === 1 ? values[0] : `(${values.join(", ")})`;
  const headerBinders = (...lists) => {
    const universes = [...new Set(lists.flat())];
    return [`${universes.join(", ")} < UU0`, ...params.map((p, k) => `${p.name} : ${parameterMarker(k)}`)].join(", ");
  };
  const modelOf = universes => `${T}(${[...universes, ...params.map(p => p.name)].join(", ")})`;
  const largest = list => list.length === 1 ? list[0] : `max(${list[0]}, ${largest(list.slice(1))})`;
  const homUniverse = universal ? `next(${largest(uA)})` : largest([...new Set([...uA, ...uB])]);
  const models = more => `{{${headerBinders(uA, uB)}}}(${[`${A} : ${modelOf(uA)}`, `${B} : ${modelOf(uB)}`, ...more].join(", ")})`;
  const implicitModels = `{{${headerBinders(uA, uB)}, ${A} : ${modelOf(uA)}, ${B} : ${modelOf(uB)}}}`;
  const threeModels = `{{${headerBinders(uA, uB, uC)}, ${A} : ${modelOf(uA)}, ${B} : ${modelOf(uB)}, ${C} : ${modelOf(uC)}}}`;
  const oneModel = `{{${headerBinders(uA)}}}(${A} : ${modelOf(uA)})`;
  const declarations = [];
  const declare = (name, source, role, extra = {}) => declarations.push({ name, source: `def ${name}${source}`, role, ...extra });
  // The projections of a record type, each typed over the earlier ones.
  const projections = (owner, fields, typeOf) => fields.forEach((field, k) => {
    let value = f;
    for (let j = 0; j < k; j++) value += ".2";
    if (k < fields.length - 1) value += ".1";
    declare(`${owner}.${field.name}`, `${implicitModels}(${f} : ${owner}(${A}, ${B})) : ${typeOf(field)} := ${value};`, "projection",
      { field: field.name });
  });
  const record_ = (name, fields, parents = []) => ({ name, model: name, make: `${name}.make`,
    fields: fields.map(field => ({ name: field.name, kind: "morphism", projection: `${name}.${field.name}` })),
    notations: {}, parents: parents.map(label => ({ label, projection: `${name}.${label}` })) });
  // A carrier's or a family's values, bound at a side: (x : A.M), or a
  // family's indices and then its member.
  const memberBinders = (sort, at, x) => families.has(sort)
    ? [...families.get(sort).map(index => `${index.name} : ${typeAt(index.shape, at)}`), `${x} : ${typeAt({ kind: "carrier", sort, args: families.get(sort).map(i => i.name) }, at)}`]
    : [`${x} : ${at.model}.${sort}`];
  // A carrier's or a family's map applied: map(x), or map(i…, x).
  const mapped = (fn, sort, at, x) => families.has(sort) ? `${fn}(${[...families.get(sort).map((index, k) => indexAt(sort, k, index.name, at)), x].join(", ")})` : `${fn}(${x})`;

  // T.Hom(A, B), its constructor and its fields.
  const ownType = field => fieldType(field, sort => map(sort));
  declare(hom, `${models([])} : ${homUniverse} := ${sigma(homFields, ownType)};`, "hom",
    { record: record_(hom, homFields, record.parents.map(parent => parent.label)) });
  declare(`${hom}.make`, `${models(homFields.map(field => `${field.name} : ${ownType(field)}`))} : ${hom}(${A}, ${B}) := ${
    tuple(homFields.map(field => field.name))};`, "make");
  projections(hom, homFields, field => fieldType(field, sort => mapping(f, sort)));
  // The identity: each map the identity, preserving by reflexivity.
  declare(`${hom}.id`, `${oneModel} : ${hom}(${A}, ${A}) := ${hom}.make(${A}, ${A}, ${homFields.map(field => {
    if (field.sort) return `fun (${memberBinders(field.sort, side(A), X).join(", ")}) => ${X}`;
    const { name, inputs } = field.operation, value = `refl(${applied(`${A}.${name}`, inputs.map(input => input.name))})`;
    const step = along(side(A), side(A), () => "");
    return inputs.length ? `fun (${inputs.map(input => binder(input, step)).join(", ")}) => ${value}` : value;
  }).join(", ")});`, "id");
  // Composition: g after f, preserving by f's preservation carried along
  // g's map, then g's.
  declare(`${hom}.compose`, `${threeModels}(${g} : ${hom}(${B}, ${C}), ${f} : ${hom}(${A}, ${B})) : ${hom}(${A}, ${C}) := ${hom}.make(${A}, ${C}, ${homFields.map(field => {
    const viaF = sort => `${f}.${map(sort)}`, viaG = sort => `${g}.${map(sort)}`;
    const first = along(side(A), side(B), viaF), second = along(first.to, side(C), viaG), whole = along(side(A), side(C), viaF);
    if (field.sort)
      return `fun (${memberBinders(field.sort, side(A), X).join(", ")}) => ${mapped(`${g}.${field.name}`, field.sort, first.to, mapped(`${f}.${field.name}`, field.sort, side(A), X))}`;
    const { inputs, result } = field.operation;
    // f's preservation at the inputs g pulls back, carried along g's map of
    // the result; then g's at the inputs f pushes forward.
    const pulledBack = along(side(B), side(C), viaG);
    const fAt = applied(`${f}.${field.name}`, inputs.map(input => input.way === "pull" ? pull(input.shape, input.name, pulledBack) : input.name));
    const gAt = applied(`${g}.${field.name}`, inputs.map(input => input.way === "push" ? push(input.shape, input.name, first) : input.name));
    const image = own("image");
    const carried = result.way === "fixed" ? fAt
      : `cong(fun (${image} : ${typeAt(result.shape, first.to)}) => ${push(result.shape, image, second)}, ${fAt})`;
    const proof = `trans(${carried}, ${gAt})`;
    const outer = { from: side(A), to: side(C) };
    return inputs.length ? `fun (${inputs.map(input => binder(input, outer)).join(", ")}) => ${proof}` : proof;
  }).join(", ")});`, "compose");
  // A parent's homomorphism: its fields are the child's fields its carriers
  // and operations became, in its order.
  for (const parent of record.parents) {
    const fields = parent.fields.flatMap((child, k) => parent.kinds[k] === "sort" ? [map(child)]
      : parent.kinds[k] === "operation" ? [`map_${child}`] : []);
    declare(`${hom}.${parent.label}`, `${implicitModels}(${f} : ${hom}(${A}, ${B})) : ${parent.theory}.Hom(${A}.${parent.label}, ${B}.${parent.label}) := ${
      parent.theory}.Hom.make(${A}.${parent.label}, ${B}.${parent.label}${fields.map(field => `, ${f}.${field}`).join("")});`, "projection",
    { field: parent.label });
  }

  // T.Iso(A, B): a homomorphism each way, inverse on each carrier and on
  // each family of sets at each index. A family of propositions needs no
  // round trip; one of sets indexed by a carrier would need its round trip
  // after a transport along the carrier's, which is not generated, so such
  // a theory has no isomorphisms (L2.4c).
  const indexedSet = carrierFields.find(field => families.has(field.name) && levelOf(field.name) === "IsSet"
    && families.get(field.name).some(index => index.shape.kind === "carrier"));
  if (indexedSet)
    return { declarations, universes: uA, parameterMarker, typeMarkers,
      missingIso: `its family of sets ${indexedSet.name} is indexed by a carrier, and its round trips would need a transport that is not generated` };
  const tripped = sorts.filter(sort => !(families.has(sort) && levelOf(sort) === "IsProp"));
  const single = sorts.length === 1;
  const isoFields = [{ name: "to" }, { name: "from" },
    ...tripped.map(sort => ({ name: single ? "from_to" : `from_to_${sort}`, sort, way: "from_to" })),
    ...tripped.map(sort => ({ name: single ? "to_from" : `to_from_${sort}`, sort, way: "to_from" }))];
  const other = field => isoFields.find(f => f.sort === field.sort && f.way !== field.way).name;
  // A round trip's type, `to` and `from` the two homomorphisms.
  const isoType = (field, to, from) => {
    if (field.name === "to") return `${hom}(${A}, ${B})`;
    if (field.name === "from") return `${hom}(${B}, ${A})`;
    const [start, x] = field.way === "from_to" ? [side(A), X] : [side(B), Y];
    const [first, second] = field.way === "from_to" ? [to, from] : [from, to];
    return quantified(memberBinders(field.sort, start, x),
      `${mapped(mapping(second, field.sort), field.sort, start, mapped(mapping(first, field.sort), field.sort, start, x))} = ${x}`);
  };
  declare(iso, `${models([])} : ${homUniverse} := ${sigma(isoFields, field => isoType(field, "to", "from"))};`, "iso",
    { record: record_(iso, isoFields) });
  declare(`${iso}.make`, `${models(isoFields.map(field => `${field.name} : ${isoType(field, "to", "from")}`))} : ${iso}(${A}, ${B}) := ${
    tuple(isoFields.map(field => field.name))};`, "make");
  projections(iso, isoFields, field => isoType(field, `${iso}.to(${f})`, `${iso}.from(${f})`));
  declare(`${iso}.id`, `${oneModel} : ${iso}(${A}, ${A}) := ${iso}.make(${A}, ${A}, ${hom}.id(${A}), ${hom}.id(${A})${
    isoFields.slice(2).map(field => `, fun (${memberBinders(field.sort, side(A), X).join(", ")}) => refl(${X})`).join("")});`, "id");
  // Composition: each way, the composite of the two homomorphisms; their
  // round trips, the inner one carried along the outer map, then the outer.
  const roundTrip = field => {
    const [start, middle, x, inner, outer] = field.way === "from_to" ? [side(A), side(B), X, g, f] : [side(C), side(B), Y, f, g];
    const [there, back] = field.way === "from_to" ? ["to", "from"] : ["from", "to"];
    const image = own("image");
    const member = families.has(field.sort) ? `${middle.model}.${field.sort}(${families.get(field.sort).map(i => i.name).join(", ")})` : `${middle.model}.${field.sort}`;
    const inside = mapped(`${outer}.${there}.${map(field.sort)}`, field.sort, start, x);
    const innerTrip = families.has(field.sort) ? `${inner}.${field.name}(${[...families.get(field.sort).map(i => i.name), inside].join(", ")})` : `${inner}.${field.name}(${inside})`;
    const outerTrip = families.has(field.sort) ? `${outer}.${field.name}(${[...families.get(field.sort).map(i => i.name), x].join(", ")})` : `${outer}.${field.name}(${x})`;
    return `, fun (${memberBinders(field.sort, start, x).join(", ")}) => trans(cong(fun (${image} : ${member}) => ${
      mapped(`${outer}.${back}.${map(field.sort)}`, field.sort, start, image)}, ${innerTrip}), ${outerTrip})`;
  };
  declare(`${iso}.compose`, `${threeModels}(${g} : ${iso}(${B}, ${C}), ${f} : ${iso}(${A}, ${B})) : ${iso}(${A}, ${C}) := ${iso}.make(${A}, ${C}, ${
    hom}.compose(${g}.to, ${f}.to), ${hom}.compose(${f}.from, ${g}.from)${isoFields.slice(2).map(roundTrip).join("")});`,
  "compose");
  // The inverse: the two homomorphisms and the two round trips swapped.
  declare(`${iso}.inverse`, `${implicitModels}(${f} : ${iso}(${A}, ${B})) : ${iso}(${B}, ${A}) := ${iso}.make(${B}, ${A}, ${f}.from, ${f}.to${
    isoFields.slice(2).map(field => `, ${f}.${other(field)}`).join("")});`, "inverse");
  return { declarations, universes: uA, parameterMarker, typeMarkers };
}
