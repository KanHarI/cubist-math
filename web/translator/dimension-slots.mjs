// Free dimensions shared by core substitution and inert syntax transport,
// and transport alpha-renaming, not a typing rule. Dimension
// slots belong to live names, not every syntactic ancestor binder. Native
// checking separately accounts for dimensions hidden in local-variable types.
import {termChildren,dimensionScope} from './term-shape.mjs';
const cache=new WeakMap();
const add=(target,source)=>{for(const name of source)target.add(name);};
function formulaNames(formula) {
  const names=new Set();
  for(const clause of formula)for(const literal of clause) {
    if(typeof literal!=='string'||!/:[01]$/.test(literal))throw Error('Invalid dimension literal.');
    names.add(literal.slice(0,-2));
  }
  formula.forEach(Object.freeze);
  Object.freeze(formula);
  return names;
}
function boundNames(term) {
  const result=new Set();
  for(const key of dimensionScope.get(term.tag)) {
    if(key==='system')for(const piece of term.system)add(result,dimensionNames(piece.term));
    else add(result,dimensionNames(term[key]));
  }
  result.delete(term.dim);
  return result;
}
// The cached set is read-only to callers; the public liveness query copies it.
export function dimensionNames(term) {
  if(!term||typeof term!=='object')throw Error('Expected cubical syntax.');
  const cached=cache.get(term);
  if(cached)return cached;
  const result=new Set(),tag=term.tag;
  if(dimensionScope.has(tag)) {
    add(result,boundNames(term));
    if(tag==='Path') {
      add(result,dimensionNames(term.left));
      add(result,dimensionNames(term.right));
    }
    if(['Comp','HComp','Trans'].includes(tag))add(result,dimensionNames(term.base));
    if(tag==='HComp')add(result,dimensionNames(term.family));
    if(['Comp','HComp'].includes(tag))for(const piece of term.system)add(result,formulaNames(piece.face));
    if(tag==='Trans')add(result,formulaNames(term.face));
  } else if(['Glue','GlueTerm'].includes(tag)) {
    add(result,dimensionNames(term.base));
    if(tag==='GlueTerm')add(result,dimensionNames(term.as));
    for(const piece of term.system) {
      add(result,formulaNames(piece.face));
      for(const key of tag==='Glue'?['type','equiv']:['term'])add(result,dimensionNames(piece[key]));
    }
  } else {
    const children=termChildren[tag]??(tag==='Ref'?[]:null);
    if(!children)throw Error(`Unsupported cubical syntax: ${tag}`);
    for(const key of children) {
      const value=term[key];
      if(Array.isArray(value)) {
        for(const item of value)add(result,dimensionNames(item));
        Object.freeze(value);
      } else if(value)add(result,dimensionNames(value));
    }
    if(tag==='PApp')add(result,formulaNames(term.arg));
  }
  // Like the checked codec, this analysis consumes immutable syntax. Freeze
  // every inspected child before memoizing, so shared DAGs are visited once
  // without allowing later mutation to invalidate a liveness decision.
  if(term.system) {
    term.system.forEach(Object.freeze);
    Object.freeze(term.system);
  }
  Object.freeze(term);
  cache.set(term,result);
  return result;
}

export function freeDimensions(term) { return new Set(dimensionNames(term)); }

export function bindDimensions(term,dimensions=new Map()) {
  if(!dimensionScope.has(term.tag))throw Error('Expected a dimension binder.');
  const live=boundNames(term),inner=new Map();
  for(const [name,slot]of dimensions)if(live.has(name))inner.set(name,slot);
  const occupied=new Set(inner.values());
  let dim=0;
  while(occupied.has(dim))dim++;
  if(dim>=64)throw Error('Cubical prototype supports 64 simultaneously live dimensions.');
  inner.set(term.dim,dim);
  return {dim,inner};
}
