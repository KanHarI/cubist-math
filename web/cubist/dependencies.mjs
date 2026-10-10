// Dependency facts of a retained theory, before any construction strategy.
// Identities and open binders are explicit; a display spelling is never used
// to resolve an external reference. This analysis does not infer types.
import {rewritten} from "./scopes.mjs";
import {builtinNames} from "./parser.mjs";

const site = node => ({start:node.start,end:node.end});
const category = kind => kind === "sort" ? "carrier" : kind === "derived" ? "helper" : kind;

export class DependencyAnalysis {
  constructor(graph) {
    if (!graph) throw new TypeError("A generation strategy requires a retained dependency graph");
    this.graph = graph;
    this.byName = new Map([...graph.interface,...graph.fields].map(field=>[field.name,field]));
    this.byIdentity = new Map([...graph.interface,...graph.fields].map(field=>[field.identity,field]));
  }
  // Every free occurrence has a disposition, including unresolved source
  // names and holes that must still be diagnosed/solved by elaboration.
  references(syntax, bound = new Set()) {
    const uses = [];
    rewritten(syntax,(node,inner)=>{
      if(node.lexicalNotation)uses.push({identity:node.lexicalNotation,category:"external",
        role:"notation",name:node.operator??node.kind,at:site(node)});
      if(node.kind !== "name" && node.kind !== "reference")return node;
      const root = node.kind === "name" ? node.name.split(".")[0] : null;
      if(root && inner.has(root))return node;
      const known = node.kind === "reference" ? this.byIdentity.get(node.binding) : this.byName.get(root);
      const name = node.spelling ?? node.name;
      if(known)uses.push({identity:known.identity,category:known.category,name:known.name,at:site(node)});
      else if(node.kind === "reference")uses.push({identity:node.binding,category:"external",name,at:site(node)});
      else if(builtinNames.has(root)||["Unit","Void","tt"].includes(root)||/^U+\d+$/.test(root))
        uses.push({identity:`builtin:${root}`,category:"builtin",name,at:site(node)});
      else uses.push({identity:null,category:root === "_" ? "hole" : "unresolved",name,at:site(node)});
      return node;
    },bound);
    return uses;
  }
  // Follow field signatures and helper values, retaining a path of binding
  // identities from the written occurrence to its transitive dependency.
  dependencies(syntax, bound = new Set()) {
    const queue = this.references(syntax,bound).map(use=>({...use,via:[]}));
    const found = [], seen = new Set();
    while(queue.length) {
      const use = queue.shift(), key = use.identity ?? `${use.category}:${use.name}`;
      if(seen.has(key))continue;
      seen.add(key);found.push(use);
      const field = this.byIdentity.get(use.identity);
      if(!field)continue;
      for(const dependency of [...(field.typeUses??[]),...(field.valueUses??[])])
        queue.push({...dependency,at:use.at,via:[...use.via,use.identity]});
    }
    return found;
  }
  first(syntax, bound, categories) {
    return this.dependencies(syntax,bound).find(use=>categories.includes(use.category)) ?? null;
  }
}

// fields supply complete signature/value syntax. Inherited and renamed
// records build new graphs through their explicit field correspondence.
export function dependencyGraph(owner, parameters, fields) {
  const graph = {owner,interface:[],fields:fields.map(field=>({
    identity:field.identity,originIdentity:field.originIdentity??field.identity,
    name:field.name,category:category(field.kind),at:field.at,
  }))};
  // A header parameter's domain sees only the preceding interface. In
  // particular, it cannot accidentally acquire a same-spelled field.
  for(const parameter of parameters) {
    const preceding = new DependencyAnalysis({...graph,fields:[]});
    graph.interface.push({...parameter,typeUses:parameter.type ? preceding.references(parameter.type) : []});
  }
  const analysis = new DependencyAnalysis(graph);
  for(const [index,field] of fields.entries())Object.assign(graph.fields[index],{
    typeUses:analysis.references(field.signature),
    valueUses:field.value ? analysis.references(field.value) : [],
  });
  return graph;
}

export const unsupported = (reason, at, detail = {}) => ({status:"unsupported",reason,at,...detail});
// Admissible syntax still has obligations; the ordinary checker, rather
// than this graph, establishes universes and the generated witnesses.
export const conditional = (mapping, obligations) => ({status:"conditional",mapping,obligations});
