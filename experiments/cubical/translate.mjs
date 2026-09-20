// Partial source translator. Unsupported syntax/foundations are explicit errors;
// no fallback axiom, old-kernel handle, or unchecked term enters this checker.
import {parse} from "../../web/mathscript/parser.mjs";
import {Checker,T} from "./core.mjs";
import {interval as I} from "./lattice.mjs";

export class Translator {
  constructor() { this.checker=new Checker();this.serial=0; }
  fresh(prefix="b") {return `${prefix}${++this.serial}`;}
  translate(source, imported=new Map()) {
    const ast=parse(source),env=new Map(imported),declarations=[];
    for(const d of ast.declarations) {
      try {
        if(d.kind==="axiom") throw Error("Axiom declarations require an explicit assumption policy; not translated.");
        let expression=d.value;
        if(!expression) {
          expression={kind:"proof",type:d.type,statements:d.body};
          for(const p of [...d.params].reverse()) expression={kind:"lambda",name:p.name,domain:p.type,body:expression};
        }
        const term=this.term(expression,new Map(),env);
        const checked=this.checker.verify(term);
        env.set(d.name.text,checked.term);
        declarations.push({name:d.name.text,status:"checked-cubical-fragment",term:checked.term,type:checked.type,normal:checked.normal});
      } catch(error) {
        // Remove a same-named imported symbol: a failed local declaration must
        // never silently refer to that other declaration in subsequent proofs.
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,reason:error.message});
        declarations.push({name:d.name.text,status:"not-translated",reason:error.message});
      }
    }
    return {declarations,env,normalizationVisits:this.checker.steps};
  }
  term(n,ctx,env,expected=null) {
    if(!n) throw Error("Missing source expression.");
    const tr=(x,e=expected)=>this.term(x,ctx,env,e);
    const inferred=t=>this.checker.infer(t,ctx,new Set());
    switch(n.kind) {
      case "name": {
        if(env.has(n.name)) {
          const value=env.get(n.name);
          if(value.tag==="Untranslated") throw Error(`Untranslated dependency: ${n.name}`);
          return value;
        }
        if(/^U[0-9]+$/.test(n.name))return T.universe(Number(n.name.slice(1)));
        const builtin={Nat:T.nat,Unit:T.unit,tt:T.point};
        if(builtin[n.name])return builtin[n.name];
        throw Error(`Untranslated name: ${n.name}`);
      }
      case "number": {let t=T.zero;for(let i=0;i<n.value;i++)t=T.succ(t);return t;}
      case "lambda": case "forall": case "exists": {
        const domain=tr(n.domain,null),name=this.fresh(),inner=new Map(ctx).set(name,domain),scope=new Map(env).set(n.name.text,T.variable(name));
        const body=this.term(n.body,inner,scope,null);
        return (n.kind==="lambda"?T.lam:n.kind==="forall"?T.pi:T.sigma)(name,domain,body);
      }
      case "binary": {
        const left=tr(n.left,null);
        if(["->","and"].includes(n.operator)) return (n.operator==="->"?T.pi:T.sigma)(this.fresh(),left,tr(n.right,null));
        if(n.operator==="=") {
          const type=n.carrier?tr(n.carrier,null):inferred(left).type;
          return T.path(this.fresh("i"),type,left,tr(n.right,type));
        }
        throw Error(`Untranslated operator: ${n.operator}`);
      }
      case "pair": {
        if(!expected)throw Error("Pair requires an expected type.");
        const sigma=this.checker.nf(expected);if(sigma.tag!=="Sigma")throw Error("Expected a Sigma type for pair.");
        const first=tr(n.left,sigma.domain), family=T.lam(sigma.name,sigma.domain,sigma.body);
        return T.pair(expected,first,tr(n.right,T.app(family,first)));
      }
      case "call": {
        const builtin=n.fn.kind==="name"&&!env.has(n.fn.name)?n.fn.name:null;
        if(builtin==="typed"&&n.args.length===2) {
          const type=tr(n.args[0],null),term=tr(n.args[1],type);
          this.checker.check(term,type,ctx,new Set());return term;
        }
        if(builtin==="succ"&&n.args.length===1)return T.succ(tr(n.args[0],T.nat));
        if(builtin==="refl"&&n.args.length===1) {
          const value=tr(n.args[0],null);return T.line(this.fresh("i"),inferred(value).type,value);
        }
        if(builtin==="sym"&&n.args.length===1) {
          const p=tr(n.args[0],null),type=this.checker.nf(inferred(p).type);
          if(type.tag!=="Path")throw Error("sym requires a path.");
          // MathScript equality has a constant carrier (dependent Path reversal
          // is checked by the core directly, rather than silently approximated).
          const i=this.fresh("i");return T.line(i,type.family,T.at(p,I.reverse(I.variable(i))));
        }
        let fn=tr(n.fn,null);
        for(const arg of n.args) {
          const pi=this.checker.nf(inferred(fn).type);if(pi.tag!=="Pi")throw Error("Source application is not a function.");
          fn=T.app(fn,tr(arg,pi.domain));
        }
        return fn;
      }
      case "induction": {
        const value=tr(n.value,T.nat),k=this.fresh(),ih=this.fresh();
        const stepCtx=new Map(ctx).set(k,T.nat), scope=new Map(env).set(n.index.text,T.variable(k));
        const motiveBody=this.term(n.type,stepCtx,scope,null),motive=T.lam(k,T.nat,motiveBody);
        const zero=tr(n.base,T.app(motive,T.zero));
        stepCtx.set(ih,motiveBody);scope.set(n.hypothesis.text,T.variable(ih));
        const step=T.lam(k,T.nat,T.lam(ih,motiveBody,this.term(n.step,stepCtx,scope,T.app(motive,T.succ(T.variable(k))))));
        return T.natrec(motive,zero,step,value);
      }
      case "proof": {
        const type=tr(n.type,null);
        if(n.statements.length!==1||n.statements[0].kind!=="exact")throw Error("Proof block tactics not yet translated.");
        const term=tr(n.statements[0].value,type);this.checker.check(term,type,ctx,new Set());return term;
      }
      default:throw Error(`Untranslated syntax: ${n.kind}`);
    }
  }
}
