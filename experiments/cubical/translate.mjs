// Partial source translator. Unsupported syntax/foundations are explicit errors;
// no fallback axiom, old-kernel handle, or unchecked term enters this checker.
import {parse} from "../../web/mathscript/parser.mjs";
import {binaryLiteralSyntax} from "../../web/mathscript/binary-literals.mjs";
import {Checker,T} from "./core.mjs";
import {interval as I,face as F} from "./lattice.mjs";

export class Translator {
  constructor({normalize=true,nativeCheck=null,checker=new Checker()}={}) {
    this.checker=checker;this.serial=0;
    this.normalize=normalize;this.nativeCheck=nativeCheck;
  }
  fresh(prefix="b") {return `${prefix}${++this.serial}`;}
  schema(expression,env) {
    return expression.kind==="lambda"&&expression.domain.kind==="name"&&expression.domain.name==="Universe"
      ? {tag:"UniverseSchema",parameter:expression.name.text,body:expression.body,env:new Map(env)} : null;
  }
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
        const schema=this.schema(expression,env);
        if(schema) {
          env.set(d.name.text,schema);
          declarations.push({name:d.name.text,status:"not-translated",reason:"Universe schema: each concrete specialization is checked at its use; no single closed translation claimed."});
          continue;
        }
        const term=this.term(expression,new Map(),env);
        // Normal forms are optional inspection output, not a prerequisite for
        // checking a declaration whose Nat value may have millions of successors.
        const checked=this.normalize?this.checker.verify(term):this.checker.infer(term);
        const native=this.nativeCheck?.(checked.term,checked.type,[],{normalize:false})??checked.native;
        if(native&&!native.ok)throw Error(`Native cubical check rejected: ${native.error}`);
        env.set(d.name.text,this.checker.define?.(d.name.text,checked.term,checked.type)??checked.term);
        declarations.push({name:d.name.text,status:native?"checked-native-cubical":"checked-cubical-fragment",term:checked.term,type:checked.type,normal:checked.normal,native});
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
          if(value.tag==="UniverseSchema")throw Error(`Universe arguments required: ${n.name}`);
          return value;
        }
        if(/^U[0-9]+$/.test(n.name))return T.universe(Number(n.name.slice(1)));
        if(n.name==="succ") { const name=this.fresh();return T.lam(name,T.nat,T.succ(T.variable(name))); }
        const builtin={Nat:T.nat,Unit:T.unit,tt:T.point,Void:T.void};
        if(builtin[n.name])return builtin[n.name];
        throw Error(`Untranslated name: ${n.name}`);
      }
      case "number": {let t=T.zero;for(let i=0;i<n.value;i++)t=T.succ(t);return t;}
      case "binaryNumber": return tr(binaryLiteralSyntax(n));
      case "lambda": case "forall": case "exists": {
        const domain=tr(n.domain,null),name=this.fresh(),inner=new Map(ctx).set(name,domain),scope=new Map(env).set(n.name.text,T.variable(name));
        let bodyExpected=null;
        if(n.kind==="lambda"&&expected) {
          const pi=this.checker.nf(expected);
          if(pi.tag==="Pi")bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),T.variable(name));
        }
        const body=this.term(n.body,inner,scope,bodyExpected);
        return (n.kind==="lambda"?T.lam:n.kind==="forall"?T.pi:T.sigma)(name,domain,body);
      }
      case "binary": {
        const left=tr(n.left,null);
        if(["->","and"].includes(n.operator)) return (n.operator==="->"?T.pi:T.sigma)(this.fresh(),left,tr(n.right,null));
        if(n.operator==="or")return T.sum(left,tr(n.right,null));
        if(["+","*","<=","<"].includes(n.operator)) {
          const name=n.operator==="+"?"add":n.operator==="*"?"mul":n.operator==="<"&&env.has("isLt")?"isLt":"le";
          const first=n.operator==="<"&&name==="le"?{kind:"call",fn:{kind:"name",name:"succ"},args:[n.left]}:n.left;
          return tr({kind:"call",fn:{kind:"name",name},args:[first,n.right]},null);
        }
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
          const checked=this.checker.check(term,type,ctx,new Set());
          return this.checker.ascribe?.(checked,type)??checked;
        }
        if(builtin==="succ"&&n.args.length===1)return T.succ(tr(n.args[0],T.nat));
        if(builtin==="W"&&n.args.length===2) {
          const domain=tr(n.args[0],null),family=tr(n.args[1],null),name=this.fresh();
          return T.w(name,domain,T.app(family,T.variable(name)));
        }
        if(builtin==="sup"&&n.args.length===3) {
          const type=tr(n.args[0],null),shape=this.checker.nf(type);
          if(shape.tag!=="W")throw Error("sup requires a W type.");
          const label=tr(n.args[1],shape.domain),arity=T.app(T.lam(shape.name,shape.domain,shape.body),label);
          return T.sup(type,label,tr(n.args[2],T.pi(this.fresh(),arity,type)));
        }
        if(builtin==="wrec"&&n.args.length===4) {
          const [type,motive,step,value]=n.args.map(a=>tr(a,null));
          this.checker.check(value,type,ctx,new Set());
          return T.wrec(motive,step,value);
        }
        if(builtin==="unit_induction"&&n.args.length===3) {
          const [motive,point,value]=n.args.map(a=>tr(a,null));
          return T.unitrec(motive,point,value);
        }
        if(builtin==="FunExt"&&n.args.length===6) {
          const [universe,A,B,f,g,h]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U")throw Error("FunExt needs a concrete universe.");
          this.checker.check(A,universe,ctx,new Set());
          const x=this.fresh(),dim=this.fresh("i"),variable=T.variable(x),fiber=T.app(B,variable);
          this.checker.check(B,T.pi(x,A,universe),ctx,new Set());
          const functionType=T.pi(x,A,fiber);
          this.checker.check(f,functionType,ctx,new Set());
          this.checker.check(g,functionType,ctx,new Set());
          const pointwise=T.pi(x,A,T.path(dim,fiber,T.app(f,variable),T.app(g,variable)));
          this.checker.check(h,pointwise,ctx,new Set());
          return T.line(dim,functionType,T.lam(x,A,T.at(T.app(h,variable),I.variable(dim))));
        }
        if(builtin==="absurd"&&n.args.length===1) {
          if(!expected)throw Error("absurd requires an expected type.");
          return T.abort(expected,tr(n.args[0],T.void));
        }
        if(["left","right"].includes(builtin)&&n.args.length===1) {
          if(!expected)throw Error("Sum injection requires an expected type.");
          const sum=this.checker.nf(expected);
          if(sum.tag!=="Sum")throw Error("Expected a sum type.");
          return (builtin==="left"?T.inl:T.inr)(expected,tr(n.args[0],sum[builtin]));
        }
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
        if(builtin==="trans"&&n.args.length===2) {
          const p=tr(n.args[0],null),q=tr(n.args[1],null),pt=this.checker.nf(inferred(p).type),qt=this.checker.nf(inferred(q).type);
          if(pt.tag!=="Path"||qt.tag!=="Path")throw Error("trans requires paths.");
          this.checker.expect(pt.family,qt.family,ctx);
          if(!this.checker.equal(pt.right,qt.left,ctx))throw Error("Path endpoints do not match.");
          const i=this.fresh("i"),j=this.fresh("j");
          return T.line(j,pt.family,T.comp(i,pt.family,[
            {face:F.endpoint(j,0),term:pt.left},{face:F.endpoint(j,1),term:T.at(q,I.variable(i))},
          ],T.at(p,I.variable(j))));
        }
        if(builtin==="cong"&&n.args.length===2) {
          const fn=tr(n.args[0],null),p=tr(n.args[1],null),pt=this.checker.nf(inferred(p).type);
          if(pt.tag!=="Path")throw Error("cong requires a path.");
          const left=T.app(fn,pt.left),type=inferred(left).type,i=this.fresh("i");
          return T.line(i,type,T.app(fn,T.at(p,I.variable(i))));
        }
        if(builtin==="transport"&&n.args.length===5) {
          const [family,x,y,p,value]=n.args.map(a=>tr(a,null));
          const pt=this.checker.nf(inferred(p).type);if(pt.tag!=="Path")throw Error("transport requires a path.");
          if(!this.checker.equal(pt.left,x,ctx)||!this.checker.equal(pt.right,y,ctx))throw Error("Transport endpoints do not match.");
          const i=this.fresh("i");return T.comp(i,T.app(family,T.at(p,I.variable(i))),[],value);
        }
        if(builtin==="path_induction"&&n.args.length===6) {
          const [A,C,d,x,y,p]=n.args.map(a=>tr(a,null)),i=this.fresh("i"),j=this.fresh("j");
          const pt=this.checker.nf(inferred(p).type);
          if(pt.tag!=="Path"||!this.checker.equal(pt.family,A,ctx)||!this.checker.equal(pt.left,x,ctx)||!this.checker.equal(pt.right,y,ctx))throw Error("Path induction endpoints/carrier do not match.");
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          const family=T.app(T.app(T.app(C,x),T.at(p,I.variable(i))),segment);
          return T.comp(i,family,[],T.app(d,x));
        }
        if(builtin==="based_induction"&&n.args.length===8) {
          const [universe,motiveUniverse,A,x,C,d,y,p]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U"||motiveUniverse.tag!=="U")throw Error("Based induction needs concrete universes.");
          this.checker.check(A,universe,ctx,new Set());
          const b=this.fresh(),q=this.fresh(),i=this.fresh("i"),j=this.fresh("j");
          const pathType=T.path(j,A,x,T.variable(b));
          this.checker.check(C,T.pi(b,A,T.pi(q,pathType,motiveUniverse)),ctx,new Set());
          this.checker.check(p,T.path(j,A,x,y),ctx,new Set());
          const reflexivity=T.line(j,A,x);
          this.checker.check(d,T.app(T.app(C,x),reflexivity),ctx,new Set());
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          return T.comp(i,T.app(T.app(C,T.at(p,I.variable(i))),segment),[],d);
        }
        let fn=n.fn.kind==="name"&&env.get(n.fn.name)?.tag==="UniverseSchema"?env.get(n.fn.name):tr(n.fn,null);
        for(const arg of n.args) {
          if(fn.tag==="UniverseSchema") {
            const universe=tr(arg,null);if(universe.tag!=="U")throw Error("Schema requires a concrete universe level.");
            const scope=new Map(fn.env).set(fn.parameter,universe);
            fn=this.schema(fn.body,scope)??this.term(fn.body,ctx,scope,null);
            continue;
          }
          const pi=this.checker.nf(inferred(fn).type);if(pi.tag!=="Pi")throw Error("Source application is not a function.");
          fn=T.app(fn,tr(arg,pi.domain));
        }
        if(fn.tag==="UniverseSchema")throw Error("Missing universe arguments.");
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
      case "match": {
        const value=tr(n.value,null),type=inferred(value).type,sum=this.checker.nf(type);
        if(sum.tag!=="Sum")throw Error("match requires a sum type.");
        const name=this.fresh(),scope=new Map(env),inner=new Map(ctx).set(name,type);
        if(n.motiveName)scope.set(n.motiveName.text,T.variable(name));
        const motive=T.lam(name,type,this.term(n.type,inner,scope,null));
        const branch=side=>{
          const local=this.fresh(),domain=sum[side],variable=T.variable(local);
          const branchEnv=new Map(env).set(n[side].text,variable);
          const injection=(side==="left"?T.inl:T.inr)(type,variable);
          return T.lam(local,domain,this.term(n[side+"Body"],new Map(ctx).set(local,domain),branchEnv,T.app(motive,injection)));
        };
        return T.sumrec(motive,branch("left"),branch("right"),value);
      }
      case "unpack": {
        const value=tr(n.value,null),sigma=this.checker.nf(inferred(value).type);
        if(sigma.tag!=="Sigma")throw Error("unpack requires a dependent pair.");
        const goal=tr(n.type,null),scope=new Map(env)
          .set(n.left.text,T.first(value)).set(n.right.text,T.second(value));
        const body=this.term(n.body,ctx,scope,goal);
        this.checker.check(body,goal,ctx,new Set());
        return body;
      }
      case "proof": {
        const type=tr(n.type,null);
        const term=this.block(n.statements,type,ctx,env);
        const checked=this.checker.check(term,type,ctx,new Set());
        return this.checker.ascribe?.(checked,type)??checked;
      }
      default:throw Error(`Untranslated syntax: ${n.kind}`);
    }
  }
  block(statements,goal,ctx,env) {
    if(!statements.length)throw Error("Proof block has no conclusion.");
    const [first,...rest]=statements;
    if(first.kind==="exact") {
      if(rest.length)throw Error("Statements after exact are unreachable.");
      return this.term(first.value,ctx,env,goal);
    }
    if(first.kind==="intro") {
      const pi=this.checker.nf(goal);
      if(pi.tag!=="Pi")throw Error("intro requires a dependent function goal.");
      const name=this.fresh(),variable=T.variable(name),inner=new Map(ctx).set(name,pi.domain);
      const scope=new Map(env).set(first.name.text,variable);
      const bodyGoal=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
      return T.lam(name,pi.domain,this.block(rest,bodyGoal,inner,scope));
    }
    if(first.kind==="let"&&first.target.kind==="name") {
      const value=this.term(first.value,ctx,env,null);
      this.checker.infer(value,ctx,new Set());
      return this.block(rest,goal,ctx,new Map(env).set(first.target.name,value));
    }
    if(first.kind==="obtain") {
      const value=this.term(first.value,ctx,env,null),scope=new Map(env);
      const bind=(pattern,term)=>{
        if(pattern.kind==="name") {scope.set(pattern.name,term);return;}
        if(pattern.kind!=="pair"||this.checker.nf(this.checker.infer(term,ctx,new Set()).type).tag!=="Sigma")
          throw Error("obtain requires a dependent pair matching its pattern.");
        bind(pattern.left,T.first(term));bind(pattern.right,T.second(term));
      };
      this.checker.infer(value,ctx,new Set());bind(first.target,value);
      return this.block(rest,goal,ctx,scope);
    }
    if(first.kind==="cases") {
      if(rest.length)throw Error("Statements after cases are not yet translated.");
      const value=this.term(first.value,ctx,env,null),type=this.checker.infer(value,ctx,new Set()).type;
      const sum=this.checker.nf(type);
      if(sum.tag!=="Sum")throw Error("cases requires a sum type.");
      const motive=T.lam(this.fresh(),type,goal);
      const branch=side=>{
        const name=this.fresh(),domain=sum[side],scope=new Map(env).set(first[side].text,T.variable(name));
        return T.lam(name,domain,this.block(first[side+"Body"],goal,new Map(ctx).set(name,domain),scope));
      };
      return T.sumrec(motive,branch("left"),branch("right"),value);
    }
    if(first.kind==="have") {
      const type=this.term(first.type,ctx,env,null),value=this.block(first.body,type,ctx,env);
      this.checker.check(value,type,ctx,new Set());
      return this.block(rest,goal,ctx,new Map(env).set(first.name.text,value));
    }
    throw Error(`Proof tactic not yet translated: ${first.kind}`);
  }
}
