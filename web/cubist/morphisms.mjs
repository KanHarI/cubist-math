// Homomorphisms and isomorphisms of a theory's models (L2.4, the fourth
// slice of docs/roadmaps/core-theories.md): the source of their
// declarations, from the theory's record (theories.mjs), which parses it.
//
//   T.Hom(A, B)            a map for each sort, map_S : A.S -> B.S (map when
//                          there is one sort), and for each operation and
//                          constant f that the maps preserve it, map_f;
//   T.Hom.make, f.map …    its constructor and projections;
//   T.Hom.id(A), T.Hom.compose(g, f), and f.p, the homomorphism of each
//                          parent's models;
//   T.Iso(A, B)            a homomorphism each way, to and from, inverse on
//                          each sort: from_to and to_from;
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

// How a type is mapped: "fixed" when it mentions no carrier; a carrier; an
// arrow or a pair of shapes; or another form, which the maps do not follow.
function shapeOf(type, carriers) {
  if (![...freeNames(type)].some(name => carriers.has(name))) return { kind: "fixed", type };
  if (type.kind === "name" && carriers.has(type.name)) return { kind: "carrier", sort: type.name, type };
  if (type.kind === "binary" && type.operator === "->")
    return { kind: "arrow", from: shapeOf(type.left, carriers), to: shapeOf(type.right, carriers), type };
  if (type.kind === "forall" && !freeNames(type.body).has(type.name.text))
    return { kind: "arrow", from: shapeOf(type.domain, carriers), to: shapeOf(type.body, carriers), type };
  if (type.kind === "binary" && type.operator === "and")
    return { kind: "pair", left: shapeOf(type.left, carriers), right: shapeOf(type.right, carriers), type };
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
// An operation's inputs and result, each with its shape and way, "fixed",
// "push" or "pull"; or, as `why`, why its homomorphisms are not generated.
function operationShape(field, carriers) {
  const inputs = [];
  let type = field.type;
  while (type.kind === "forall") {
    inputs.push({ name: type.name.text, type: type.domain });
    type = type.body;
  }
  const names = new Set(inputs.map(input => input.name));
  for (const [k, input] of inputs.entries())
    if (inputs.slice(0, k).some(earlier => freeNames(input.type).has(earlier.name)))
      return { why: `its ${field.name}'s argument ${input.name} has a type that depends on an earlier argument` };
  if ([...freeNames(type)].some(name => names.has(name)))
    return { why: `its ${field.name}'s result has a type that depends on its arguments` };
  const way = (shape, place) => {
    const where = occurrences(shape);
    if (where.has("other")) return { why: `its ${field.name}'s ${place} has a type that the maps do not follow` };
    if (where.has("+") && where.has("-"))
      return { why: `its ${field.name}'s ${place} mentions a carrier on both sides of an arrow, and such homomorphisms need not compose` };
    return { way: where.has("+") ? "push" : where.has("-") ? "pull" : "fixed" };
  };
  for (const input of inputs) {
    input.shape = shapeOf(input.type, carriers);
    const { why, way: inputWay } = way(input.shape, `argument ${input.name}`);
    if (why) return { why };
    input.way = inputWay;
  }
  const result = { type, shape: shapeOf(type, carriers) };
  const { why, way: resultWay } = way(result.shape, "result");
  if (why) return { why };
  if (resultWay === "pull")
    return { why: `its ${field.name}'s result mentions a carrier left of an arrow, which a homomorphism cannot carry forward` };
  result.way = resultWay;
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
  // would not shadow, so each avoids every theory in scope, T included.
  // Every model of a theory with parameters shares them, and its universes:
  // a homomorphism keeps them fixed (L2.4c). Otherwise each model has its
  // own universes, as many as the theory's header binds.
  const params = record.params ?? [], count = Math.max(1, record.universes?.length ?? 0);
  // Every binder the source introduces is fresh: none captures a parameter
  // or a name that an operation's type mentions, which the source writes
  // as it is, apart from the carriers, which it writes as A.M; and none is
  // a universe constant, so a taken U is followed by U_1, not U1.
  const carrierNames = new Set(record.fields.filter(field => field.kind === "sort").map(field => field.name));
  const taken = new Set([...params.map(p => p.name),
    ...record.fields.flatMap(field => [...freeNames(field.type)]).filter(name => !carrierNames.has(name))]);
  const numbered = (stem, k) => /^U+$/.test(stem) || /[0-9]$/.test(stem) ? `${stem}_${k}` : `${stem}${k}`;
  const own = stem => {
    let name = stem;
    for (let k = 1; name === T || isTheory(name) || taken.has(name); k++) name = numbered(stem, k);
    taken.add(name);
    return name;
  };
  const A = own("A"), B = own("B"), C = own("C"), f = own("f"), g = own("g");
  const sorts = record.fields.filter(field => field.kind === "sort").map(field => field.name);
  if (!sorts.length) return { missing: `${T} has no sorts` };
  // A carrier with no h-level has paths that are data: its homomorphisms
  // would need coherence fields, which are not specified (L2.4c).
  const untruncated = sorts.find(sort => !record.fields.some(field => field.kind === "evidence" && field.of === sort));
  if (untruncated) return { missing: `its carrier ${untruncated} has no h-level, and homomorphisms of such a carrier need coherences that are not generated` };
  const sortSet = new Set(sorts), operations = new Map();
  for (const field of record.fields.filter(field => field.kind === "operation")) {
    const shape = operationShape(field, sortSet);
    if (shape.why) return { missing: shape.why };
    operations.set(field.name, { name: field.name, ...shape });
  }
  // An operation whose type names the theory's universe, as an argument
  // A : U does, is the same value on both sides only in one universe: such a
  // theory's homomorphisms relate models in the same universes, as a
  // parameter's do, and lie one universe up.
  const universal = [...operations.values()].some(op => [...freeNames([op.inputs.map(i => i.type), op.result.type])]
    .some(name => name.startsWith("\u0000universe")));
  // Each model's universes: U, V and W, or U_1, U_2, … when there are
  // several (U1 is a universe constant); the shared ones are U's.
  const universesOf = letter => count === 1 ? [own(letter)] : Array.from({ length: count }, (_, k) => own(`${letter}_${k + 1}`));
  const [uA, uB, uC] = params.length || universal ? Array(3).fill(universesOf("U")) : [universesOf("U"), universesOf("V"), universesOf("W")];
  const map = sort => sorts.length === 1 ? "map" : `map_${sort}`;
  // A homomorphism's fields, in the theory's order: a map for each sort, and
  // that the maps preserve each operation and constant.
  const homFields = record.fields.flatMap(field => field.kind === "sort" ? [{ name: map(field.name), sort: field.name }]
    : field.kind === "operation" ? [{ name: `map_${field.name}`, operation: operations.get(field.name) }] : []);
  if (new Set(homFields.map(field => field.name)).size !== homFields.length)
    return { missing: "two of its homomorphisms' fields would have one name" };
  // An operation's arguments: x, y, z, then x4, x5, …, each fresh.
  const argumentNames = [];
  const argument = k => argumentNames[k] ??= own(["x", "y", "z"][k] ?? `x${k + 1}`);
  const applied = (fn, args) => args.length ? `${fn}(${args.join(", ")})` : fn;
  // A type written in a model, as a marker that the expansion replaces by
  // the type, its carriers that model's and its universes the model's.
  const typeMarkers = new Map();
  const typeIn = (type, model) => {
    const marker = `__theory_type_${typeMarkers.size}`;
    typeMarkers.set(marker, { type, model, universes: model === A ? uA : model === B ? uB : uC });
    return marker;
  };
  // Pushing a value of shape `shape` from model `from` to model `to`, along
  // `mapOf(sort)`, and pulling one back; each lambda's binder is fresh.
  let locals = 0;
  const local = () => own(`v${++locals}`);
  const push = (shape, term, from, to, mapOf) => {
    if (shape.kind === "fixed") return term;
    if (shape.kind === "carrier") return `${mapOf(shape.sort)}(${term})`;
    // A pair is typed, since an equation's side is elaborated before its type is known.
    if (shape.kind === "pair")
      return `typed(${typeIn(shape.type, to)}, (${push(shape.left, `(${term}).1`, from, to, mapOf)}, ${push(shape.right, `(${term}).2`, from, to, mapOf)}))`;
    const v = local();
    return `fun (${v} : ${typeIn(shape.from.type, to)}) => ${push(shape.to, `(${term})(${pull(shape.from, v, from, to, mapOf)})`, from, to, mapOf)}`;
  };
  const pull = (shape, term, from, to, mapOf) => {
    if (shape.kind === "fixed") return term;
    if (shape.kind === "pair")
      return `typed(${typeIn(shape.type, from)}, (${pull(shape.left, `(${term}).1`, from, to, mapOf)}, ${pull(shape.right, `(${term}).2`, from, to, mapOf)}))`;
    const v = local();
    return `fun (${v} : ${typeIn(shape.from.type, from)}) => ${pull(shape.to, `(${term})(${push(shape.from, v, from, to, mapOf)})`, from, to, mapOf)}`;
  };
  // An input's binder over models `from` and `to`: pulled inputs range over
  // `to`'s values, the others over `from`'s.
  const binder = (input, k, from, to) => `${argument(k)} : ${typeIn(input.type, input.way === "pull" ? to : from)}`;
  const quantified = (inputs, from, to, body) => inputs.map((input, k) => `forall ${binder(input, k, from, to)}. `).join("") + body;
  // A homomorphism's map of a sort, as a function: T.Hom.map(h).
  const mapping = (h, sort) => `${hom}.${map(sort)}(${h})`;
  // That `mapOf` preserves an operation from `from` to `to`.
  const preservation = (operation, from, to, mapOf) => {
    const { name, inputs, result } = operation;
    const left = applied(`${from}.${name}`, inputs.map((input, k) => input.way === "pull" ? pull(input.shape, argument(k), from, to, mapOf) : argument(k)));
    const right = applied(`${to}.${name}`, inputs.map((input, k) => input.way === "push" ? push(input.shape, argument(k), from, to, mapOf) : argument(k)));
    return quantified(inputs, from, to, `${push(result.shape, left, from, to, mapOf)} = ${right}`);
  };
  // The type of a homomorphism field over A and B, `mapOf(sort)` the maps.
  const fieldType = (field, mapOf) => field.sort ? `${A}.${field.sort} -> ${B}.${field.sort}` : preservation(field.operation, A, B, mapOf);
  // A field's binder in its record's Σ and in its constructor: its name,
  // unless a parameter has that name. A constructor's parameter keeps the
  // field's name as its label, by which a call names it.
  const fieldBinders = new Map();
  const bound = field => fieldBinders.get(field.name) ?? fieldBinders.set(field.name, own(field.name)).get(field.name);
  const labels = fields => Object.fromEntries(fields.filter(field => bound(field) !== field.name).map(field => [bound(field), field.name]));
  // A Σ of fields, the last one bare; a tuple of values.
  const sigma = (fields, typeOf) => fields.map((field, k) => k === fields.length - 1 ? typeOf(field)
    : `exists ${bound(field)} : (${typeOf(field)}). `).join("");
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

  // T.Hom(A, B), its constructor and its fields.
  const ownType = field => fieldType(field, sort => bound({ name: map(sort) }));
  declare(hom, `${models([])} : ${homUniverse} := ${sigma(homFields, ownType)};`, "hom",
    { record: record_(hom, homFields, record.parents.map(parent => parent.label)) });
  declare(`${hom}.make`, `${models(homFields.map(field => `${bound(field)} : ${ownType(field)}`))} : ${hom}(${A}, ${B}) := ${
    tuple(homFields.map(bound))};`, "make", { labels: labels(homFields) });
  projections(hom, homFields, field => fieldType(field, sort => mapping(f, sort)));
  // The identity: each map the identity, preserving by reflexivity.
  declare(`${hom}.id`, `${oneModel} : ${hom}(${A}, ${A}) := ${hom}.make(${A}, ${A}, ${homFields.map(field => {
    if (field.sort) return `fun (x : ${A}.${field.sort}) => x`;
    const { name, inputs } = field.operation, value = `refl(${applied(`${A}.${name}`, inputs.map((_, k) => argument(k)))})`;
    return inputs.length ? `fun (${inputs.map((input, k) => binder(input, k, A, A)).join(", ")}) => ${value}` : value;
  }).join(", ")});`, "id");
  // Composition: g after f, preserving by f's preservation carried along
  // g's map, then g's.
  declare(`${hom}.compose`, `${threeModels}(${g} : ${hom}(${B}, ${C}), ${f} : ${hom}(${A}, ${B})) : ${hom}(${A}, ${C}) := ${hom}.make(${A}, ${C}, ${homFields.map(field => {
    if (field.sort) return `fun (x : ${A}.${field.sort}) => ${g}.${field.name}(${f}.${field.name}(x))`;
    const { inputs, result } = field.operation;
    const viaF = sort => `${f}.${map(sort)}`, viaG = sort => `${g}.${map(sort)}`;
    // f's preservation at the inputs g pulls back, carried along g's map of
    // the result; then g's at the inputs f pushes forward.
    const first = applied(`${f}.${field.name}`, inputs.map((input, k) => input.way === "pull" ? pull(input.shape, argument(k), B, C, viaG) : argument(k)));
    const second = applied(`${g}.${field.name}`, inputs.map((input, k) => input.way === "push" ? push(input.shape, argument(k), A, B, viaF) : argument(k)));
    const image = own("image");
    const carried = result.way === "fixed" ? first
      : `cong(fun (${image} : ${typeIn(result.type, B)}) => ${push(result.shape, image, B, C, viaG)}, ${first})`;
    const proof = `trans(${carried}, ${second})`;
    return inputs.length ? `fun (${inputs.map((input, k) => binder(input, k, A, C)).join(", ")}) => ${proof}` : proof;
  }).join(", ")});`, "compose");
  // A parent's homomorphism: its fields are the child's fields its sorts
  // and operations became, in its order.
  for (const parent of record.parents) {
    const fields = parent.fields.flatMap((child, k) => parent.kinds[k] === "sort" ? [map(child)]
      : parent.kinds[k] === "operation" ? [`map_${child}`] : []);
    declare(`${hom}.${parent.label}`, `${implicitModels}(${f} : ${hom}(${A}, ${B})) : ${parent.theory}.Hom(${A}.${parent.label}, ${B}.${parent.label}) := ${
      parent.theory}.Hom.make(${A}.${parent.label}, ${B}.${parent.label}${fields.map(field => `, ${f}.${field}`).join("")});`, "projection",
    { field: parent.label });
  }

  // T.Iso(A, B): a homomorphism each way, inverse on each sort.
  const isoFields = [{ name: "to" }, { name: "from" },
    ...sorts.map(sort => ({ name: sorts.length === 1 ? "from_to" : `from_to_${sort}`, sort, way: "from_to" })),
    ...sorts.map(sort => ({ name: sorts.length === 1 ? "to_from" : `to_from_${sort}`, sort, way: "to_from" }))];
  const other = field => isoFields.find(f => f.sort === field.sort && f.way !== field.way).name;
  const isoType = (field, to, from) => field.name === "to" ? `${hom}(${A}, ${B})` : field.name === "from" ? `${hom}(${B}, ${A})`
    : field.way === "from_to" ? `forall x : ${A}.${field.sort}. ${mapping(from, field.sort)}(${mapping(to, field.sort)}(x)) = x`
      : `forall y : ${B}.${field.sort}. ${mapping(to, field.sort)}(${mapping(from, field.sort)}(y)) = y`;
  const [to, from] = isoFields.map(bound);
  declare(iso, `${models([])} : ${homUniverse} := ${sigma(isoFields, field => isoType(field, to, from))};`, "iso",
    { record: record_(iso, isoFields) });
  declare(`${iso}.make`, `${models(isoFields.map(field => `${bound(field)} : ${isoType(field, to, from)}`))} : ${iso}(${A}, ${B}) := ${
    tuple(isoFields.map(bound))};`, "make", { labels: labels(isoFields) });
  projections(iso, isoFields, field => isoType(field, `${iso}.to(${f})`, `${iso}.from(${f})`));
  declare(`${iso}.id`, `${oneModel} : ${iso}(${A}, ${A}) := ${iso}.make(${A}, ${A}, ${hom}.id(${A}), ${hom}.id(${A})${
    isoFields.slice(2).map(field => `, fun (x : ${A}.${field.sort}) => refl(x)`).join("")});`, "id");
  // Composition: each way, the composite of the two homomorphisms; their
  // round trips, the inner one carried along the outer map, then the outer.
  declare(`${iso}.compose`, `${threeModels}(${g} : ${iso}(${B}, ${C}), ${f} : ${iso}(${A}, ${B})) : ${iso}(${A}, ${C}) := ${iso}.make(${A}, ${C}, ${
    hom}.compose(${g}.to, ${f}.to), ${hom}.compose(${f}.from, ${g}.from)${isoFields.slice(2).map(field => field.way === "from_to"
    ? `, fun (x : ${A}.${field.sort}) => trans(cong(fun (image : ${B}.${field.sort}) => ${f}.from.${map(field.sort)}(image), ${g}.${field.name}(${f}.to.${map(field.sort)}(x))), ${f}.${field.name}(x))`
    : `, fun (y : ${C}.${field.sort}) => trans(cong(fun (image : ${B}.${field.sort}) => ${g}.to.${map(field.sort)}(image), ${f}.${field.name}(${g}.from.${map(field.sort)}(y))), ${g}.${field.name}(y))`).join("")});`,
  "compose");
  // The inverse: the two homomorphisms and the two round trips swapped.
  declare(`${iso}.inverse`, `${implicitModels}(${f} : ${iso}(${A}, ${B})) : ${iso}(${B}, ${A}) := ${iso}.make(${B}, ${A}, ${f}.from, ${f}.to${
    isoFields.slice(2).map(field => `, ${f}.${other(field)}`).join("")});`, "inverse");
  return { declarations, universes: uA, parameterMarker, typeMarkers };
}
