// Cubical syntax: term constructors, free names, substitution, and derived
// filling. Terms are inert JSON; building one certifies nothing, and the
// kernel checks every term elaboration produces.
import { interval as I, face as F } from "./lattice.mjs";

export const T = {
  universe: level => ({tag:"U",level}), variable: name => ({tag:"Var",name}),
  pi: (name,domain,body) => ({tag:"Pi",name,domain,body}),
  lam: (name,domain,body) => ({tag:"Lam",name,domain,body}),
  app: (fn,arg) => ({tag:"App",fn,arg}),
  sigma: (name,domain,body) => ({tag:"Sigma",name,domain,body}),
  pair: (as,first,second) => ({tag:"Pair",as,first,second}),
  first: pair => ({tag:"Fst",pair}), second: pair => ({tag:"Snd",pair}),
  path: (dim,family,left,right) => ({tag:"Path",dim,family,left,right}),
  line: (dim,family,body) => ({tag:"PLam",dim,family,body}),
  at: (path,arg) => ({tag:"PApp",path,arg}),
  comp: (dim,family,system,base) => ({tag:"Comp",dim,family,system,base}),
  hcomp: (dim,family,system,base) => ({tag:"HComp",dim,family,system,base}),
  trans: (dim,family,face,base) => ({tag:"Trans",dim,family,face,base}),
  // Level quantification (G0): Π (x < ω). B, λ (x < ω). t and f {ℓ}. A level
  // is a number (a tier-0 constant) or {tag:"LConst"|"LSucc"|"LMax"|"Var"};
  // a universe variable in a context has the bound {tag:"LBound",tier:1}.
  levelPi: (name,body) => ({tag:"LPi",name,body}),
  levelLambda: (name,body) => ({tag:"LLam",name,body}),
  levelApply: (fn,level) => ({tag:"LApp",fn,level}),
  bound: {tag:"LBound",tier:1},
  unit: {tag:"Unit"}, point: {tag:"Point"}, void: {tag:"Void"},
  abort: (as,impossible) => ({tag:"Abort",as,impossible}),
  sum: (left,right) => ({tag:"Sum",left,right}),
  inl: (as,value) => ({tag:"Inl",as,value}), inr: (as,value) => ({tag:"Inr",as,value}),
  sumrec: (motive,left,right,value) => ({tag:"SumRec",motive,left,right,value}),
  unitrec: (motive,point,value) => ({tag:"UnitRec",motive,point,value}),
  glueType: (base,system) => ({tag:"Glue",base,system}),
  glue: (as,base,system) => ({tag:"GlueTerm",as,base,system}),
  unglue: (as,value) => ({tag:"Unglue",as,value}),
  // Declared types (H1): an instance of a registered signature, constructor
  // number `index` of an instance, and an eliminator.
  sort: (signature,parameters=[],levels=[]) => ({tag:"Sort",signature,parameters,levels}),
  constructor: (index,sort,name) => ({tag:"Con",index,...(name?{name}:{}),sort}),
  eliminator: (signature,motive,clauses) => ({tag:"Elim",signature,motive,clauses}),
};
const fail = message => { throw new Error(message); };
const children = {
  U:[], Var:[], DefRef:[], Unit:[], Point:[],
  Pi:["domain","body"], Lam:["domain","body"], Sigma:["domain","body"],
  App:["fn","arg"], Pair:["as","first","second"], Fst:["pair"], Snd:["pair"],
  Path:["family","left","right"], PLam:["family","body"], PApp:["path","pathType"],
  Comp:["family","base"], HComp:["family","base"], Trans:["family","base"], Void:[], Abort:["as","impossible"],
  Sum:["left","right"], Inl:["as","value"], Inr:["as","value"],
  SumRec:["motive","left","right","value"], UnitRec:["motive","point","value"],
  Glue:["base"], GlueTerm:["as","base"], Unglue:["as","value"],
  LPi:["body"], LLam:["body"], LApp:["fn"], LBound:[],
  // Declared types (H1): an instance's parameters and an eliminator's
  // clauses are lists; an instance's recorded levels are levels.
  Sort:["parameters"], Con:["sort"], Elim:["motive","clauses"],
};
// The items of a child: one term, or a list of them.
const items = value => Array.isArray(value) ? value : [value];
const termBinder = t => ["Pi","Lam","Sigma","LPi","LLam"].includes(t.tag);
// The variables of a level: universe variables, bound like term variables.
export function levelNames(level, result = new Set()) {
  if (!level || typeof level !== "object") return result;
  if (level.tag === "Var") result.add(level.name);
  else if (level.tag === "LSucc") levelNames(level.level, result);
  else if (level.tag === "LMax") { levelNames(level.left, result); levelNames(level.right, result); }
  return result;
}
// Whether a level lies below ω, for every value of its variables: built from
// variables and finite constants by successors and maxima.
export function finiteLevel(level) {
  return typeof level === "number" || level?.tag === "Var"
    || (level?.tag === "LConst" && level.tier === 0) || (level?.tag === "LSucc" && finiteLevel(level.level))
    || (level?.tag === "LMax" && finiteLevel(level.left) && finiteLevel(level.right));
}
// A level with a universe variable replaced: by a level, or by a universe's.
function levelSubstitute(level, name, value) {
  if (!level || typeof level !== "object") return level;
  if (level.tag === "Var") {
    if (level.name !== name) return level;
    return value?.tag === "U" ? value.level : value;
  }
  if (level.tag === "LSucc") return {...level, level: levelSubstitute(level.level, name, value)};
  if (level.tag === "LMax") return {...level, left: levelSubstitute(level.left, name, value), right: levelSubstitute(level.right, name, value)};
  return level;
}
const levelShaped = value => typeof value === "number" || ["LConst","LSucc","LMax","Var","U"].includes(value?.tag);
// A level such as 2 or next(x) is not a term: it has no dimensions, and its
// variables are its names.
const plainLevel = value => typeof value === "number" || ["LConst","LSucc","LMax"].includes(value?.tag);
const dimBinder = t => ["Path","PLam","Comp","HComp","Trans"].includes(t.tag);
function free(t, dimension = false, result = new Set(), memo = new WeakMap()) {
  if (!t || !children[t.tag]) fail("Unknown term constructor.");
  const cached=memo.get(t);
  if(cached) {for(const name of cached)result.add(name);return result;}
  const local=new Set();
  if (dimension && t.tag === "PApp") for (const n of I.names(t.arg)) local.add(n);
  if(dimension&&t.tag==="Trans")for(const n of I.names(t.face))local.add(n);
  if (!dimension && t.tag === "Var") local.add(t.name);
  if (!dimension && t.tag === "U") levelNames(t.level, local);
  if (!dimension && t.tag === "LApp") levelNames(t.level, local);
  if (!dimension && t.tag === "Sort") for (const level of t.levels ?? []) levelNames(level, local);
  if(["Glue","GlueTerm"].includes(t.tag))for(const piece of t.system) {
    for(const key of t.tag==="Glue"?["type","equiv"]:["term"])
      for(const n of free(piece[key],dimension,new Set(),memo))local.add(n);
    if(dimension)for(const n of I.names(piece.face))local.add(n);
  }
  if(["Comp","HComp"].includes(t.tag))for(const piece of t.system) {
    const sub=free(piece.term,dimension,new Set(),memo);
    for(const n of sub)if(!dimension||n!==t.dim)local.add(n);
    if(dimension)for(const n of I.names(piece.face))local.add(n);
  }
  for (const key of children[t.tag]) if (t[key]) for (const item of items(t[key])) {
    const sub = free(item, dimension,new Set(),memo);
    for(const n of sub) {
      if(!dimension && termBinder(t) && key==="body" && n===t.name)continue;
      if(dimension && dimBinder(t) && t.tag!=="HComp" && ["family","body"].includes(key) && n===t.dim)continue;
      local.add(n);
    }
  }
  memo.set(t,local);
  for(const n of local)result.add(n);
  return result;
}
function fresh(n, avoid) { while (avoid.has(n)) n += "_"; return n; }
// The free term names of a term, universe variables included.
export function freeNames(t) { return free(t); }
// A term with its beta redexes contracted, within a budget of substitutions,
// keeping every name: syntax only, as for display or a normal form's shape.
export function betaReduce(term, budget = 256) {
  const reduced = new WeakMap();
  const beta = t => {
    if (!t || typeof t !== "object") return t;
    if (reduced.has(t)) return reduced.get(t);
    let result = Array.isArray(t) ? t.map(beta) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, beta(value)]));
    // A lambda applied, and a universe lambda instantiated at a level.
    for (; budget > 0; budget--) {
      if (result.tag === "App" && result.fn?.tag === "Lam") result = beta(substitute(result.fn.body, result.fn.name, result.arg));
      else if (result.tag === "LApp" && result.fn?.tag === "LLam") result = beta(substitute(result.fn.body, result.fn.name, result.level));
      // A path lambda at a point: its body with the point for its dimension.
      else if (result.tag === "PApp" && result.path?.tag === "PLam") result = beta(dsub(result.path.body, result.path.dim, result.arg));
      // A pair's projections.
      else if (result.tag === "Fst" && result.pair?.tag === "Pair") result = beta(result.pair.first);
      else if (result.tag === "Snd" && result.pair?.tag === "Pair") result = beta(result.pair.second);
      else break;
    }
    reduced.set(t, result);
    return result;
  };
  return beta(term);
}
function substitute(t, n, value, dimension = false, memo = new WeakMap()) {
  if(memo.has(t))return memo.get(t);
  if (!dimension && t.tag === "Var" && t.name === n) {memo.set(t,value);return value;}
  let result = {...t};
  // A term argument can contain free dimensions. Avoid capturing them under
  // Path/PLam/Comp binders even though this substitution targets a term name.
  if(!dimension&&dimBinder(t)&&!plainLevel(value)&&free(value,true).has(t.dim)) {
    const dim=fresh(t.dim,new Set([...free(t,true),...free(value,true),t.dim]));
    if(t.tag!=="HComp")result.family=dsub(result.family,t.dim,I.variable(dim));
    if(t.tag==="PLam")result.body=dsub(result.body,t.dim,I.variable(dim));
    if(["Comp","HComp"].includes(t.tag))result.system=result.system.map(p=>({...p,term:dsub(p.term,t.dim,I.variable(dim))}));
    result.dim=dim;
  }
  const isBinder = dimension ? dimBinder(t) : termBinder(t);
  const binderKey = dimension ? "dim" : "name";
  let binder = t[binderKey];
  const boundChildren = dimension ? (t.tag==="HComp"?[]:["family","body"]) : ["body"];
  const valueFree = new Set(dimension ? I.names(value) : plainLevel(value) ? levelNames(value) : free(value));
  if (isBinder && binder !== n && valueFree.has(binder)) {
    const replacement = fresh(binder, new Set([...free(t,dimension),...valueFree,n,binder]));
    for (const key of boundChildren) if (result[key]) result[key] = substitute(result[key], binder,
      dimension ? I.variable(replacement) : T.variable(replacement), dimension);
    if(dimension&&["Comp","HComp"].includes(t.tag))result.system=result.system.map(p=>({...p,term:dsub(p.term,binder,I.variable(replacement))}));
    binder = replacement; result[binderKey] = binder;
  }
  for (const key of children[t.tag]) if (result[key]) {
    if (isBinder && binder === n && boundChildren.includes(key)) continue;
    result[key] = Array.isArray(result[key]) ? result[key].map(item => substitute(item, n, value, dimension, memo))
      : substitute(result[key], n, value, dimension, memo);
  }
  // A universe variable occurs in levels: substituted by a level, or by the
  // universe a level names.
  if (!dimension && ["U","LApp"].includes(t.tag) && levelShaped(value) && levelNames(t.level).has(n))
    result.level = levelSubstitute(t.level, n, value);
  if (!dimension && t.tag === "Sort" && levelShaped(value) && (t.levels ?? []).some(level => levelNames(level).has(n)))
    result.levels = t.levels.map(level => levelSubstitute(level, n, value));
  if(dimension&&t.tag==="Trans")result.face=F.substitute(t.face,n,value);
  if (dimension && t.tag === "PApp") result.arg = I.substitute(t.arg,n,value);
  if(["Comp","HComp"].includes(t.tag))result.system=result.system.map(p=>({
    face:dimension?F.substitute(p.face,n,value):p.face,
    term:dimension&&binder===n?p.term:substitute(p.term,n,value,dimension,memo),
  }));
  if(["Glue","GlueTerm"].includes(t.tag))result.system=t.system.map(piece=>{
    const changed={...piece,face:dimension?F.substitute(piece.face,n,value):piece.face};
    for(const key of t.tag==="Glue"?["type","equiv"]:["term"])changed[key]=substitute(piece[key],n,value,dimension,memo);
    return changed;
  });
  memo.set(t,result);
  return result;
}
const dsub = (t,n,r) => substitute(t,n,r,true);
export {dsub as substituteDimension};
// Syntax manipulation only; callers must independently check the result.
// DefRef denotes a closed definition, so substitution does not enter its body.
export {substitute as substituteTerm};

// Derived filling, CCHM section 4.4. The added r=0 wall keeps the starting lid
// fixed. This is syntax built from comp, never an additional trusted axiom.
export function fill(dim,family,system,base,r) {
  const avoid=new Set([...free(family,true),...free(base,true),...I.names(r),dim]);
  for(const p of system)for(const n of [...free(p.term,true),...I.names(p.face)])avoid.add(n);
  const j=fresh("fill",avoid),along=I.meet(r,I.variable(j));
  return T.comp(j,dsub(family,dim,along),[
    ...system.map(p=>({...p,term:dsub(p.term,dim,along)})),
    {face:F.equalEndpoint(r,0),term:base},
  ],base);
}
