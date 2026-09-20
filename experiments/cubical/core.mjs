// Small bidirectional reference checker for the structural/path fragment of CCHM.
// NOT a complete cubical kernel: comp, Glue and HITs are deliberately absent.
// Input is inert JSON syntax; checking never executes user-supplied functions.
import { interval as I } from "./lattice.mjs";

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
  nat: {tag:"Nat"}, zero:{tag:"Zero"}, succ: value => ({tag:"Succ",value}),
  natrec: (motive,zero,step,value) => ({tag:"NatRec",motive,zero,step,value}),
  unit: {tag:"Unit"}, point: {tag:"Point"},
};
const fail = message => { throw new Error(message); };
const validName = n => typeof n === "string" && /^[A-Za-z_][A-Za-z_0-9]*$/.test(n);
const named = n => { if (!validName(n)) fail("Invalid variable name."); };
const children = {
  U:[], Var:[], Nat:[], Zero:[], Unit:[], Point:[], Succ:["value"],
  Pi:["domain","body"], Lam:["domain","body"], Sigma:["domain","body"],
  App:["fn","arg"], Pair:["as","first","second"], Fst:["pair"], Snd:["pair"],
  Path:["family","left","right"], PLam:["family","body"], PApp:["path","pathType"],
  NatRec:["motive","zero","step","value"],
};
const termBinder = t => ["Pi","Lam","Sigma"].includes(t.tag);
const dimBinder = t => ["Path","PLam"].includes(t.tag);
function free(t, dimension = false, result = new Set()) {
  if (!t || !children[t.tag]) fail("Unknown term constructor.");
  if (dimension && t.tag === "PApp") for (const n of I.names(t.arg)) result.add(n);
  if (!dimension && t.tag === "Var") result.add(t.name);
  for (const key of children[t.tag]) if (t[key]) {
    const sub = free(t[key], dimension);
    if (!dimension && termBinder(t) && key === "body") sub.delete(t.name);
    if (dimension && dimBinder(t) && ["family","body"].includes(key)) sub.delete(t.dim);
    for (const n of sub) result.add(n);
  }
  return result;
}
function fresh(n, avoid) { while (avoid.has(n)) n += "_"; return n; }
function substitute(t, n, value, dimension = false) {
  if (!dimension && t.tag === "Var" && t.name === n) return value;
  let result = {...t};
  const isBinder = dimension ? dimBinder(t) : termBinder(t);
  const binderKey = dimension ? "dim" : "name";
  let binder = t[binderKey];
  const boundChildren = dimension ? ["family","body"] : ["body"];
  const valueFree = new Set(dimension ? I.names(value) : free(value));
  if (isBinder && binder !== n && valueFree.has(binder)) {
    const replacement = fresh(binder, new Set([...free(t,dimension),...valueFree,n,binder]));
    for (const key of boundChildren) if (result[key]) result[key] = substitute(result[key], binder,
      dimension ? I.variable(replacement) : T.variable(replacement), dimension);
    binder = replacement; result[binderKey] = binder;
  }
  for (const key of children[t.tag]) if (result[key]) {
    if (isBinder && binder === n && boundChildren.includes(key)) continue;
    result[key] = substitute(result[key], n, value, dimension);
  }
  if (dimension && t.tag === "PApp") result.arg = I.substitute(t.arg,n,value);
  return result;
}
const dsub = (t,n,r) => substitute(t,n,r,true);

// Bound names disappear in comparison; free names remain names. Paths bind a
// dimension in their family, but their endpoints live in the outer context.
function alpha(t, vars = [], dims = []) {
  const child = (key,v=vars,d=dims) => alpha(t[key],v,d);
  if (t.tag === "Var") return ["Var",vars.includes(t.name) ? ["bound",vars.lastIndexOf(t.name)] : ["free",t.name]];
  if (t.tag === "U") return ["U",t.level];
  if (termBinder(t)) return [t.tag,child("domain"),child("body",[...vars,t.name])];
  if (dimBinder(t)) return t.tag === "Path"
    ? ["Path",child("family",vars,[...dims,t.dim]),child("left"),child("right")]
    : ["PLam",child("family",vars,[...dims,t.dim]),child("body",vars,[...dims,t.dim])];
  if (t.tag === "PApp") return ["PApp",child("path"),
    t.arg.map(c => c.map(x => [dims.includes(x.slice(0,-2)) ? ["bound",dims.lastIndexOf(x.slice(0,-2))] : ["free",x.slice(0,-2)],x.at(-1)]).sort()).sort()];
  return [t.tag,...children[t.tag].map(key => child(key))];
}

// Only elaborated, checked terms reach reduction. A path application retains its
// checked Path type so a neutral path computes at either endpoint too.
function normal(t, fuel) {
  if (--fuel.left < 0) fail("Experimental normalization limit reached.");
  let r = {...t};
  for (const key of children[t.tag]) if (t[key]) r[key] = normal(t[key],fuel);
  if (r.tag === "App" && r.fn.tag === "Lam") return normal(substitute(r.fn.body,r.fn.name,r.arg),fuel);
  if (r.tag === "Lam" && r.body.tag === "App" && r.body.arg.tag === "Var" && r.body.arg.name === r.name && !free(r.body.fn).has(r.name)) return r.body.fn;
  if (r.tag === "Fst" && r.pair.tag === "Pair") return r.pair.first;
  if (r.tag === "Snd" && r.pair.tag === "Pair") return r.pair.second;
  if (r.tag === "NatRec" && r.value.tag === "Zero") return r.zero;
  if (r.tag === "NatRec" && r.value.tag === "Succ") return normal(T.app(T.app(r.step,r.value.value),{...r,value:r.value.value}),fuel);
  if (r.tag === "PApp") {
    if (I.equal(r.arg,I.zero)) return normal(r.pathType.left,fuel);
    if (I.equal(r.arg,I.one)) return normal(r.pathType.right,fuel);
    if (r.path.tag === "PLam") return normal(dsub(r.path.body,r.path.dim,r.arg),fuel);
  }
  if (r.tag === "PLam" && r.body.tag === "PApp" && I.equal(r.body.arg,I.variable(r.dim)) && !free(r.body.path,true).has(r.dim)) return r.body.path;
  return r;
}

export class Checker {
  constructor({fuel=100000} = {}) { this.limit = fuel; this.steps = 0; }
  nf(t) { const budget={left:this.limit}; const result=normal(t,budget); this.steps += this.limit-budget.left; return result; }
  equal(a,b) { return JSON.stringify(alpha(this.nf(a))) === JSON.stringify(alpha(this.nf(b))); }
  expect(actual,expected) {
    if (this.equal(actual,expected)) return;
    const a=this.nf(actual), b=this.nf(expected);
    if (a.tag === "U" && b.tag === "U" && a.level <= b.level) return;
    fail(`Type mismatch: ${JSON.stringify(alpha(a))} versus ${JSON.stringify(alpha(b))}`);
  }
  type(t,ctx,dims) { const checked=this.infer(t,ctx,dims), u=this.nf(checked.type); if(u.tag!=="U") fail("Expected a universe-valued type."); return {...checked,level:u.level}; }
  check(t,expected,ctx,dims) { const checked=this.infer(t,ctx,dims); this.expect(checked.type,expected); return checked.term; }
  infer(t,ctx=new Map(),dims=new Set()) {
    if (!t || typeof t !== "object" || !children[t.tag]) fail("Unknown term constructor.");
    const infer=x=>this.infer(x,ctx,dims), type=x=>this.type(x,ctx,dims);
    const check=(x,a)=>this.check(x,a,ctx,dims);
    const result=(term,type)=>({term,type});
    switch(t.tag) {
      case "U": if(!Number.isSafeInteger(t.level)||t.level<0||t.level>=Number.MAX_SAFE_INTEGER) fail("Invalid universe level."); return result(T.universe(t.level),T.universe(t.level+1));
      case "Var": named(t.name); if(!ctx.has(t.name)) fail(`Unbound term variable ${t.name}.`); return result(T.variable(t.name),ctx.get(t.name));
      case "Nat": case "Unit": return result({tag:t.tag},T.universe(0));
      case "Zero": return result(T.zero,T.nat);
      case "Point": return result(T.point,T.unit);
      case "Succ": return result(T.succ(check(t.value,T.nat)),T.nat);
      case "NatRec": {
        const motive=infer(t.motive), mt=this.nf(motive.type);
        if(mt.tag!=="Pi"||!this.equal(mt.domain,T.nat)||this.nf(mt.body).tag!=="U") fail("Expected a natural-number type family.");
        const value=check(t.value,T.nat), zero=check(t.zero,T.app(motive.term,T.zero));
        const avoid=new Set([...ctx.keys(),...free(motive.term)]), n=fresh("pred",avoid);avoid.add(n);const h=fresh("ih",avoid);
        const step=check(t.step,T.pi(n,T.nat,T.pi(h,T.app(motive.term,T.variable(n)),T.app(motive.term,T.succ(T.variable(n))))));
        return result(T.natrec(motive.term,zero,step,value),T.app(motive.term,value));
      }
      case "Pi": case "Sigma": case "Lam": {
        named(t.name);
        if(ctx.has(t.name)) {
          const name=fresh(t.name,new Set([...ctx.keys(),...free(t)]));
          t={...t,name,body:substitute(t.body,t.name,T.variable(name))};
        }
        const domain=type(t.domain), inner=new Map(ctx).set(t.name,domain.term);
        if(t.tag==="Lam") { const body=this.infer(t.body,inner,dims); return result(T.lam(t.name,domain.term,body.term),T.pi(t.name,domain.term,body.type)); }
        const body=this.type(t.body,inner,dims);
        return result({...t,domain:domain.term,body:body.term},T.universe(Math.max(domain.level,body.level)));
      }
      case "App": {
        const fn=infer(t.fn), pi=this.nf(fn.type); if(pi.tag!=="Pi") fail("Expected a function.");
        const arg=check(t.arg,pi.domain); return result(T.app(fn.term,arg),substitute(pi.body,pi.name,arg));
      }
      case "Pair": {
        const as=type(t.as).term, sigma=this.nf(as); if(sigma.tag!=="Sigma") fail("Expected a dependent pair type.");
        const first=check(t.first,sigma.domain), second=check(t.second,substitute(sigma.body,sigma.name,first));
        return result(T.pair(as,first,second),as);
      }
      case "Fst": case "Snd": {
        const pair=infer(t.pair), sigma=this.nf(pair.type); if(sigma.tag!=="Sigma") fail("Expected a dependent pair.");
        return result({tag:t.tag,pair:pair.term},t.tag==="Fst"?sigma.domain:substitute(sigma.body,sigma.name,T.first(pair.term)));
      }
      case "Path": case "PLam": {
        named(t.dim);
        if(dims.has(t.dim)) {
          const dim=fresh(t.dim,new Set([...dims,...free(t,true)]));
          t={...t,dim,family:dsub(t.family,t.dim,I.variable(dim)),
            ...(t.tag==="PLam"?{body:dsub(t.body,t.dim,I.variable(dim))}:{})};
        }
        const inner=new Set(dims).add(t.dim), family=this.type(t.family,ctx,inner);
        if(t.tag==="Path") {
          const left=check(t.left,dsub(family.term,t.dim,I.zero)),right=check(t.right,dsub(family.term,t.dim,I.one));
          return result(T.path(t.dim,family.term,left,right),T.universe(family.level));
        }
        const body=this.check(t.body,family.term,ctx,inner);
        return result(T.line(t.dim,family.term,body),T.path(t.dim,family.term,dsub(body,t.dim,I.zero),dsub(body,t.dim,I.one)));
      }
      case "PApp": {
        const path=infer(t.path), pt=this.nf(path.type); if(pt.tag!=="Path") fail("Expected a path.");
        const arg=I.normalize(t.arg); for(const n of I.names(arg)) if(!dims.has(n)) fail(`Unbound dimension ${n}.`);
        return result({...T.at(path.term,arg),pathType:pt},dsub(pt.family,pt.dim,arg));
      }
    }
    fail("Unsupported term.");
  }
  // Public entry checks assumptions in telescope order. A raw Map cannot inject
  // an unchecked type into the public verification result.
  verify(term, expected=null, assumptions=[]) {
    const ctx=new Map();
    for(const [name,rawType] of assumptions) {
      named(name); if(ctx.has(name)) fail("Duplicate assumption.");
      ctx.set(name,this.type(rawType,ctx,new Set()).term);
    }
    const checked=this.infer(term,ctx,new Set());
    if(expected) this.expect(checked.type,this.type(expected,ctx,new Set()).term);
    return {term:checked.term,type:this.nf(checked.type),normal:this.nf(checked.term),assumptions:[...ctx.keys()],normalizationVisits:this.steps};
  }
}
