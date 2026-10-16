// Homomorphisms and isomorphisms of a theory's models (L2.4, the fourth
// slice of docs/roadmaps/core-theories.md): mapping and support plans
// from the retained interface. Artifact construction consumes these IDs
// directly; labels are only public names and diagnostic text.
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

import { allNames, freshName } from "./scopes.mjs";
import {bindingSyntaxView,bindingUses,unresolvedBindingUse} from "./binding-syntax.mjs";
import {DependencyAnalysis,dependencyUses} from "./dependencies.mjs";

const reference=node=>node?.kind==="bindingReference"&&node.resolution.tag==="binding"?node.resolution.id:null;

// How a type is mapped: "fixed" when it mentions no carrier; a carrier, or
// a family's member, whose index that is an element of a carrier is a name
// the operation binds and whose other indices are terms over its
// arguments, as V(m + n); an arrow or a pair of shapes; or another form,
// which the maps do not follow.
function shapeOf(type, context) {
  const { carriers, families, fields, identities } = context;
  if (![...identities(type)].some(id => carriers.has(id))) return { kind: "fixed", type };
  if (carriers.has(reference(type)) && !families.has(reference(type))) return { kind: "carrier", sort: reference(type), type };
  const indices = type.kind === "call" ? families.get(reference(type.fn)) : null;
  if (indices && type.args.length === indices.length && type.args.every((arg, k) => indices[k].shape.kind === "carrier"
    ? reference(arg)!==null && !fields.has(reference(arg)) : ![...identities(arg)].some(id => fields.has(id))))
    return { kind: "carrier", sort: reference(type.fn), args: type.args, type };
  if (type.kind === "binary" && type.operator === "->")
    return { kind: "arrow", from: shapeOf(type.left, context), to: shapeOf(type.right, context), type };
  if (type.kind === "forall" && !identities(type.body).has(type.name.bindingId))
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
function binders(type, parameters) {
  const list=[],taken=new Set([...allNames(type),...parameters]),bound=new Set(parameters);
  while(type.kind==="forall"||type.kind==="binderGroup"&&type.binderKind==="forall") {
    for(const token of type.kind==="forall"?[type.name]:type.names) {
      const label=token.label??token.text;
      const name=label==="_"||bound.has(label)?freshName(label,taken):label;
      const id=token.bindingId;
      if(!id)throw new TypeError("A retained morphism telescope needs binding identities.");
      list.push({name,label,id,type:type.domain});bound.add(name);
    }
    type=type.body;
  }
  return {list,body:type};
}
// An operation's inputs and result, each with its shape and way, "fixed",
// "push" or "pull"; or, as `why`, why its homomorphisms are not generated.
function operationShape(field, context) {
  const { list: inputs, body: type } = binders(field.type, context.parameters);
  for(const [tree,place] of [...inputs.map(input=>[input.type,`argument ${input.label}`]),[type,"result"]]) {
    const refusal=transportRefusal(field,tree,place,context);
    if(refusal)return refusal;
  }
  const way = (shape, place) => {
    const where = occurrences(shape);
    if (where.has("other")) return { why: `its ${field.name}'s ${place} has a type that the maps do not follow` };
    if (where.has("+") && where.has("-"))
      return { why: `its ${field.name}'s ${place} mentions a carrier on both sides of an arrow, and such homomorphisms need not compose` };
    return { way: where.has("+") ? "push" : where.has("-") ? "pull" : "fixed" };
  };
  for (const input of inputs) {
    input.shape = shapeOf(input.type, context);
    const { why, way: inputWay } = way(input.shape, `argument ${input.label}`);
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
  const pushed = new Set(inputs.filter(input => input.way === "push").map(input => input.id));
  for (const part of [...inputs, result].flatMap(item => fixedParts(item.shape)))
    if ([...context.identities(part)].some(id => pushed.has(id)))
      return { why: `a type in its ${field.name} names an argument that is pushed forward, on B's side another value` };
  // A pulled input is B's: no type may name it, and its own names none.
  for (const [k, input] of inputs.entries()) {
    const later = [...inputs.slice(k + 1).map(other => other.type), type];
    if (input.way === "pull" && (later.some(t => context.identities(t).has(input.id))
      || inputs.slice(0, k).some(earlier => context.identities(input.type).has(earlier.id))))
      return { why: `its ${field.name}'s argument ${input.label} is pulled back and depends on, or is named by, another argument` };
  }
  return { inputs, result };
}

function transportRefusal(field,type,place,context) {
  const dependency=context.dependencies.first(bindingSyntaxView(context.bindingSyntax,type),
    ["law","evidence","operation","helper","recursive-helper"],{conditional:true});
  if(!dependency)return null;
  const label=context.dependencies.byIdentity.get(dependency.id)?.label??dependency.spelling;
  return {why:`its ${field.name}'s ${place} depends on ${dependency.category} ${label}, whose transport and composition are not generated`,
    field:field.id,place,dependency,at:dependency.origin};
}

// Conditional support is not admission: the generated declarations still
// check their interfaces, universe levels, preservation and composition.
export function morphismPlan(record) {
  if(!record.bindingSyntax)throw new TypeError("Morphism planning needs retained binding interfaces.");
  const result=planMorphisms(record),origin=record.fields[0]?.binding?.origin;
  result.support=result.pending?{status:"pending",obligations:result.pending}
    :result.missing?{status:"unsupported",reason:result.missing,at:result.refusal?.at??origin,...result.refusal}
      :{status:"conditional",mapping:result.mapping,obligations:["interfaces","universes","preservation","identity","composition"]
        .map(kind=>({kind,family:`${record.name}.Hom`}))};
  result.isoSupport=result.pending||result.missing?result.support
    :result.missingIso?{status:"unsupported",reason:result.missingIso,at:origin}
      :{status:"conditional",mapping:result.mapping,obligations:["Hom","inverse","identity","composition"]
        .map(kind=>({kind,family:`${record.name}.Iso`}))};
  return result;
}

function planMorphisms(record) {
  const dependencies=new DependencyAnalysis([...record.fields,...record.derived??[]]);
  const identities=tree=>new Set(dependencyUses(bindingSyntaxView(record.bindingSyntax,tree))
    .filter(use=>use.kind==="binding").map(use=>use.id));
  for(const parent of record.parents??[]) {
    const support=parent.homSupport;
    if(support?.status==="unsupported")return {missing:`its parent ${parent.theory} has no homomorphisms: ${support.reason}`,
      refusal:{parent:parent.theory,at:support.at,cause:support}};
    if(support?.status==="pending"||!parent.homId||!parent.homMakeId)
      return {pending:[{kind:"parent-Hom",theory:parent.theory,obligations:support?.obligations??[]}]};
  }
  const pending=record.fields.flatMap(field=>dependencyUses(bindingSyntaxView(record.bindingSyntax,field.type))
    .filter(unresolvedBindingUse).map(use=>({field:field.id,...use})));
  if(pending.length)return {pending};
  const parameters=(record.params??[]).map(p=>p.name);
  const carrierFields=record.fields.filter(field=>field.kind==="sort");
  if(!carrierFields.length)return {missing:`${record.name} has no sorts`};
  const levelOf=id=>record.fields.find(field=>field.kind==="evidence"&&field.of===id)?.evidence??null;
  const untruncated=carrierFields.find(field=>!levelOf(field.id));
  if(untruncated)return {missing:`its carrier ${untruncated.name} has no h-level, and homomorphisms of such a carrier need coherences that are not generated`};
  const carriers=new Set(carrierFields.map(field=>field.id)),fields=new Set(record.fields.map(field=>field.id));
  const families=new Map(),operations=new Map();
  const context={carriers,families,fields,parameters,identities,dependencies,bindingSyntax:record.bindingSyntax};
  for(const field of carrierFields.filter(field=>field.family)) {
    const indices=binders(field.type,parameters).list;
    for(const index of indices) {
      const refusal=transportRefusal(field,index.type,`index ${index.label}`,context);
      if(refusal)return {missing:refusal.why,refusal};
      index.shape=shapeOf(index.type,context);
      if(!["fixed","carrier"].includes(index.shape.kind)||index.shape.args)
        return {missing:`its family ${field.name}'s index ${index.name} is neither the same on both sides nor an element of a carrier`};
    }
    families.set(field.id,indices);
  }
  for(const field of record.fields.filter(field=>field.kind==="operation")) {
    const shape=operationShape(field,context);
    if(shape.why)return {missing:shape.why,refusal:shape};
    operations.set(field.id,{id:field.id,name:field.name,...shape});
  }
  const mapping={carriers:carrierFields.map(field=>({id:field.id,name:field.name})),
    operations:[...operations.values()],families:[...families].map(([id,indices])=>({id,indices}))};
  const universal=[...[...operations.values()].flatMap(op=>[...op.inputs.map(i=>i.type),op.result.type]),
    ...[...families.values()].flat().map(index=>index.type)]
    .some(type=>[...identities(type)].some(id=>record.universeIds.includes(id)));
  const homFields=record.fields.flatMap(field=>field.kind==="sort"
    ?[{name:carrierFields.length===1?"map":`map_${field.name}`,sort:field.id}]
    :field.kind==="operation"?[{name:`map_${field.name}`,operation:operations.get(field.id)}]:[]);
  if(new Set(homFields.map(field=>field.name)).size!==homFields.length)
    return {missing:"two of its homomorphisms' fields would have one name"};
  const indexedSet=carrierFields.find(field=>families.has(field.id)&&levelOf(field.id)==="IsSet"
    &&families.get(field.id).some(index=>index.shape.kind==="carrier"));
  const tripped=carrierFields.filter(field=>!(families.has(field.id)&&levelOf(field.id)==="IsProp"));
  return {mapping,carrierFields,families,operations,homFields,tripped,
    sharedUniverses:parameters.length>0||universal,
    ...(indexedSet?{missingIso:`its family of sets ${indexedSet.name} is indexed by a carrier, and its round trips would need a transport that is not generated`}:{})};
}
