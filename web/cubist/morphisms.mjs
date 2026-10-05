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
// Every operation and constant must take and return sorts. Laws need no
// field, being propositions about sets.

// The sorts of a field's arguments and result, or null when one is not a
// sort.
function signature(field, sorts) {
  const args = [];
  let type = field.type;
  while (type.kind === "forall") {
    if (type.domain.kind !== "name" || !sorts.has(type.domain.name)) return null;
    args.push(type.domain.name);
    type = type.body;
  }
  return type.kind === "name" && sorts.has(type.name) ? { args, result: type.name } : null;
}

// The declarations of T's homomorphisms and isomorphisms, each {name,
// source, role}, or, as `missing`, why T's models have none.
export function morphismSource(record) {
  const T = record.name, hom = `${T}.Hom`, iso = `${T}.Iso`;
  const sorts = record.fields.filter(field => field.kind === "sort").map(field => field.name);
  if (!sorts.length) return { missing: `${T} has no sorts` };
  const sortSet = new Set(sorts), operations = new Map();
  for (const field of record.fields.filter(field => field.kind === "operation")) {
    const shape = signature(field, sortSet);
    if (!shape) return { missing: `its ${field.name} takes or returns something other than a sort` };
    operations.set(field.name, { name: field.name, ...shape });
  }
  const map = sort => sorts.length === 1 ? "map" : `map_${sort}`;
  // A homomorphism's fields, in the theory's order: a map for each sort, and
  // that the maps preserve each operation and constant.
  const homFields = record.fields.flatMap(field => field.kind === "sort" ? [{ name: map(field.name), sort: field.name }]
    : field.kind === "operation" ? [{ name: `map_${field.name}`, operation: operations.get(field.name) }] : []);
  if (new Set(homFields.map(field => field.name)).size !== homFields.length)
    return { missing: "two of its homomorphisms' fields would have one name" };
  // An operation's arguments: x, y, z, then x4, x5, ….
  const argument = k => ["x", "y", "z"][k] ?? `x${k + 1}`;
  const xs = n => Array.from({ length: n }, (_, k) => argument(k));
  const applied = (fn, args) => args.length ? `${fn}(${args.join(", ")})` : fn;
  // A lambda's binders, (x1 : A.M, x2 : A.M), and a forall's, nested.
  const binders = (args, model) => args.map((sort, k) => `${argument(k)} : ${model}.${sort}`).join(", ");
  const quantified = (args, model, body) => args.map((sort, k) => `forall ${argument(k)} : ${model}.${sort}. `).join("") + body;
  // A homomorphism's map of a sort, as a function: T.Hom.map(h).
  const mapping = (h, sort) => `${hom}.${map(sort)}(${h})`;
  // The type of a homomorphism field over A and B, `mapOf(sort)` the maps.
  const fieldType = (field, mapOf) => {
    if (field.sort) return `A.${field.sort} -> B.${field.sort}`;
    const { name, args, result } = field.operation;
    const statement = `${mapOf(result)}(${applied(`A.${name}`, xs(args.length))}) = ${
      applied(`B.${name}`, args.map((sort, k) => `${mapOf(sort)}(${argument(k)})`))}`;
    return quantified(args, "A", statement);
  };
  // A Σ of fields, the last one bare; a tuple of values.
  const sigma = (fields, typeOf) => fields.map((field, k) => k === fields.length - 1 ? typeOf(field)
    : `exists ${field.name} : (${typeOf(field)}). `).join("");
  const tuple = values => values.length === 1 ? values[0] : `(${values.join(", ")})`;
  const models = more => `{{U, V < UU0}}(${[`A : ${T}.Model(U)`, `B : ${T}.Model(V)`, ...more].join(", ")})`;
  const implicitModels = `{{U, V < UU0, A : ${T}.Model(U), B : ${T}.Model(V)}}`;
  const threeModels = `{{U, V, W < UU0, A : ${T}.Model(U), B : ${T}.Model(V), C : ${T}.Model(W)}}`;
  const declarations = [];
  const declare = (name, source, role, extra = {}) => declarations.push({ name, source: `def ${name}${source}`, role, ...extra });
  // The projections of a record type, each typed over the earlier ones.
  const projections = (owner, fields, typeOf) => fields.forEach((field, k) => {
    let value = "f";
    for (let j = 0; j < k; j++) value += ".2";
    if (k < fields.length - 1) value += ".1";
    declare(`${owner}.${field.name}`, `${implicitModels}(f : ${owner}(A, B)) : ${typeOf(field)} := ${value};`, "projection",
      { field: field.name });
  });
  const record_ = (name, fields, parents = []) => ({ name, model: name, make: `${name}.make`,
    fields: fields.map(field => ({ name: field.name, kind: "morphism", projection: `${name}.${field.name}` })),
    notations: {}, parents: parents.map(label => ({ label, projection: `${name}.${label}` })) });

  // T.Hom(A, B), its constructor and its fields.
  const ownType = field => fieldType(field, sort => map(sort));
  declare(hom, `${models([])} : max(U, V) := ${sigma(homFields, ownType)};`, "hom",
    { record: record_(hom, homFields, record.parents.map(parent => parent.label)) });
  declare(`${hom}.make`, `${models(homFields.map(field => `${field.name} : ${ownType(field)}`))} : ${hom}(A, B) := ${
    tuple(homFields.map(field => field.name))};`, "make");
  projections(hom, homFields, field => fieldType(field, sort => mapping("f", sort)));
  // The identity: each map the identity, preserving by reflexivity.
  declare(`${hom}.id`, `{{U < UU0}}(A : ${T}.Model(U)) : ${hom}(A, A) := ${hom}.make(A, A, ${homFields.map(field => {
    if (field.sort) return `fun (x : A.${field.sort}) => x`;
    const { name, args } = field.operation;
    return args.length ? `fun (${binders(args, "A")}) => refl(${applied(`A.${name}`, xs(args.length))})` : `refl(A.${name})`;
  }).join(", ")});`, "id");
  // Composition: g after f, preserving by f's preservation carried along
  // g's map, then g's.
  declare(`${hom}.compose`, `${threeModels}(g : ${hom}(B, C), f : ${hom}(A, B)) : ${hom}(A, C) := ${hom}.make(A, C, ${homFields.map(field => {
    if (field.sort) return `fun (x : A.${field.sort}) => g.${field.name}(f.${field.name}(x))`;
    const { args, result } = field.operation;
    const proof = `trans(cong(fun (image : B.${result}) => g.${map(result)}(image), ${applied(`f.${field.name}`, xs(args.length))}), ${
      applied(`g.${field.name}`, args.map((sort, k) => `f.${map(sort)}(${argument(k)})`))})`;
    return args.length ? `fun (${binders(args, "A")}) => ${proof}` : proof;
  }).join(", ")});`, "compose");
  // A parent's homomorphism: its fields are the child's fields its sorts
  // and operations became, in its order.
  for (const parent of record.parents) {
    const fields = parent.fields.flatMap((child, k) => parent.kinds[k] === "sort" ? [map(child)]
      : parent.kinds[k] === "operation" ? [`map_${child}`] : []);
    declare(`${hom}.${parent.label}`, `${implicitModels}(f : ${hom}(A, B)) : ${parent.theory}.Hom(A.${parent.label}, B.${parent.label}) := ${
      parent.theory}.Hom.make(A.${parent.label}, B.${parent.label}${fields.map(field => `, f.${field}`).join("")});`, "projection",
    { field: parent.label });
  }

  // T.Iso(A, B): a homomorphism each way, inverse on each sort.
  const isoFields = [{ name: "to" }, { name: "from" },
    ...sorts.map(sort => ({ name: sorts.length === 1 ? "from_to" : `from_to_${sort}`, sort, way: "from_to" })),
    ...sorts.map(sort => ({ name: sorts.length === 1 ? "to_from" : `to_from_${sort}`, sort, way: "to_from" }))];
  const other = field => isoFields.find(f => f.sort === field.sort && f.way !== field.way).name;
  const isoType = (field, to, from) => field.name === "to" ? `${hom}(A, B)` : field.name === "from" ? `${hom}(B, A)`
    : field.way === "from_to" ? `forall x : A.${field.sort}. ${mapping(from, field.sort)}(${mapping(to, field.sort)}(x)) = x`
      : `forall y : B.${field.sort}. ${mapping(to, field.sort)}(${mapping(from, field.sort)}(y)) = y`;
  declare(iso, `${models([])} : max(U, V) := ${sigma(isoFields, field => isoType(field, "to", "from"))};`, "iso",
    { record: record_(iso, isoFields) });
  declare(`${iso}.make`, `${models(isoFields.map(field => `${field.name} : ${isoType(field, "to", "from")}`))} : ${iso}(A, B) := ${
    tuple(isoFields.map(field => field.name))};`, "make");
  projections(iso, isoFields, field => isoType(field, `${iso}.to(f)`, `${iso}.from(f)`));
  declare(`${iso}.id`, `{{U < UU0}}(A : ${T}.Model(U)) : ${iso}(A, A) := ${iso}.make(A, A, ${hom}.id(A), ${hom}.id(A)${
    isoFields.slice(2).map(field => `, fun (x : A.${field.sort}) => refl(x)`).join("")});`, "id");
  // Composition: each way, the composite of the two homomorphisms; their
  // round trips, the inner one carried along the outer map, then the outer.
  declare(`${iso}.compose`, `${threeModels}(g : ${iso}(B, C), f : ${iso}(A, B)) : ${iso}(A, C) := ${iso}.make(A, C, ${
    hom}.compose(g.to, f.to), ${hom}.compose(f.from, g.from)${isoFields.slice(2).map(field => field.way === "from_to"
    ? `, fun (x : A.${field.sort}) => trans(cong(fun (image : B.${field.sort}) => f.from.${map(field.sort)}(image), g.${field.name}(f.to.${map(field.sort)}(x))), f.${field.name}(x))`
    : `, fun (y : C.${field.sort}) => trans(cong(fun (image : B.${field.sort}) => g.to.${map(field.sort)}(image), f.${field.name}(g.from.${map(field.sort)}(y))), g.${field.name}(y))`).join("")});`,
  "compose");
  // The inverse: the two homomorphisms and the two round trips swapped.
  declare(`${iso}.inverse`, `${implicitModels}(f : ${iso}(A, B)) : ${iso}(B, A) := ${iso}.make(B, A, f.from, f.to${
    isoFields.slice(2).map(field => `, f.${other(field)}`).join("")});`, "inverse");
  return { declarations };
}
