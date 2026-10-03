// The language's builtins: a call of a name the module does not bind, such
// as `ua`, `path`, `comp`, `transport` or `refl`, elaborated by its own rule.
// builtinTerm returns the elaborated term, or undefined when the name and the
// number of arguments match no builtin, and the call is an ordinary one.
import {T,fill,finiteLevel} from "./core.mjs";
import {interval as I,face as F} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {withNativeReferences} from "./equivalence.mjs";
import {halfAdjointEquiv,publicUnivalencePath,publicUnivalenceBeta} from "./public-equivalence.mjs";
import {dependentPathToTransport,transportToDependentPath} from "./path-over.mjs";
import {libraryAssumption} from "../cubical-assumptions.mjs";

export function builtinTerm(t,builtin,n,scope,expected) {
  const {env}=scope;
  const tr=(x,e=expected)=>t.term(x,scope,e);
  const inferred=term=>scope.infer(term);
  if(["ua","UnivalenceBeta"].includes(builtin)&&n.args.length>=3) {
    const [universe,A,B]=n.args.slice(0,3).map(a=>tr(a,null));
    if(universe.tag!=="U")throw Error("Univalence requires a universe.");
    if(!finiteLevel(universe.level))throw scope.unit.locate(Error(`${builtin} takes a universe below UU0.`),n.args[0]);
    scope.check(A,universe);
    scope.check(B,universe);
    const build=(A,B,universe)=>{
      const E=halfAdjointEquiv(A,B),en=scope.fresh("equivalence"),x=scope.fresh("argument");
      return builtin==="ua"?T.lam(en,E,publicUnivalencePath(A,B,T.variable(en),universe.level)):
        T.lam(en,E,T.lam(x,A,publicUnivalenceBeta(A,B,T.variable(en),T.variable(x))));
    };
    let fn;
    // Asking for the generic definition checks and admits it the first
    // time in a session; the request is charged every time, so the
    // charge does not depend on the session's history.
    scope.spend("queries");
    if(t.checker.genericDefinition && t.checker.kernel?.optimizations?.reuseChecks !== false) {
      // The computational derivation is generic in the universe, A and B:
      // one definition, checked once, instantiated at each use (G0).
      const generic=t.checker.genericDefinition(`builtin__${builtin}`,()=>{
        const level=scope.fresh("level"),a=scope.fresh("sourceType"),b=scope.fresh("targetType");
        const at=T.universe(T.variable(level));
        return T.levelLambda(level,T.lam(a,at,T.lam(b,at,build(T.variable(a),T.variable(b),at))));
      });
      fn=T.app(T.app(T.levelApply(generic,universe.level),A),B);
    } else fn=build(A,B,universe);
    for(const arg of n.args.slice(3)) {
      const type=scope.nf(inferred(fn).type);
      if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
      fn=T.app(fn,tr(arg,type.domain));
    }
    return fn;
  }
  if(["Truncate","TruncateIntro","TruncateProp","TruncateElim","LEM","Choice"].includes(builtin)) {
    if(!n.args.length)throw Error(`${builtin} needs a universe argument.`);
    let start=0, truncateFormer=null;
    // Rebuilt classical assumptions explicitly name their declared
    // truncation: LEM(Trunc, U, ...), Choice(Trunc, U, ...). The old
    // LEM(U, ...) and Choice(U, ...) signatures remain available.
    let universe=tr(n.args[0],null);
    if(["LEM","Choice"].includes(builtin) && universe.tag!=="U") {
      truncateFormer=universe; start=1;
      if(n.args.length<2)throw Error(`${builtin} with a truncation former needs a universe argument.`);
      universe=tr(n.args[1],null);
    }
    if(universe.tag!=="U"||!t.checker.assume)throw Error("Logical assumptions require a universe and an explicit native context.");
    scope.spend("queries");
    // One generic assumption each, for the universes below UU0.
    if(!finiteLevel(universe.level))throw scope.unit.locate(Error(`${builtin} holds only for universes below UU0.`),n.args[0]);
    let fn=T.levelApply(libraryAssumption(t.checker,builtin,scope.context,truncateFormer),universe.level);
    for(const arg of n.args.slice(start+1)) {
      const type=scope.nf(inferred(fn).type);
      if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
      fn=T.app(fn,tr(arg,type.domain));
    }
    return fn;
  }
  if(["next","max"].includes(builtin)) {
    if(n.args.length!==(builtin==="next"?1:2))throw Error(`${builtin} takes ${builtin==="next"?"one universe":"two universes"}.`);
    const [left,right]=n.args.map(arg=>t.levelOf(arg,scope));
    return T.universe(builtin==="next"?{tag:"LSucc",count:1,level:left}:{tag:"LMax",left,right});
  }
  if(builtin==="typed"&&n.args.length===2) {
    const type=tr(n.args[0],null),term=tr(n.args[1],type);
    const checked=scope.check(term,type);
    return scope.ascribe(checked,type);
  }
  if(["path","PathP","comp","fill"].includes(builtin)) {
    const size=n.args.length;
    if((builtin==="path"&&size!==2)||(builtin==="PathP"&&size!==3)||(builtin==="comp"&&size<2)||(builtin==="fill"&&size<3))
      throw Error(`Invalid arguments to ${builtin}.`);
    const dim=scope.fresh("i"),family=t.dimensionBody(n.args[0],dim,scope);
    if(builtin==="path")return T.line(dim,family,t.dimensionBody(n.args[1],dim,scope,family));
    if(builtin==="PathP")return T.path(dim,family,tr(n.args[1],null),tr(n.args[2],null));
    const system=n.args.slice(builtin==="fill"?3:2).map(part=>{
      if(part.kind==="call"&&part.fn.kind==="name"&&part.fn.name==="face_when"&&part.args.length===2)
        return {face:t.cofibration(part.args[0],env),term:t.dimensionBody(part.args[1],dim,scope,family)};
      if(part.kind!=="call"||part.fn.kind!=="name"||part.fn.name!=="face"||part.args.length!==3)
        throw Error("A composition wall has syntax face(i, 0 or 1, fun (j : Interval) => ...).");
      const [coordinate,endpoint,wall]=part.args;
      if(coordinate.kind!=="name"||env.get(coordinate.name)?.tag!=="Dimension"||endpoint.kind!=="number"||![0,1].includes(endpoint.value))
        throw Error("A composition face needs an outer interval coordinate and endpoint 0 or 1.");
      return {face:F.endpoint(env.get(coordinate.name).name,endpoint.value),term:t.dimensionBody(wall,dim,scope,family)};
    });
    const base=tr(n.args[1],null);
    return builtin==="fill"?withNativeReferences([family,system,base],(family,system,base)=>fill(dim,family,system,base,t.interval(n.args[2],env))):T.comp(dim,family,system,base);
  }
  if(["path_from_transport","path_to_transport"].includes(builtin)&&n.args.length===4) {
    const dim=scope.fresh("i"),family=t.dimensionBody(n.args[0],dim,scope);
    const left=tr(n.args[1],null),right=tr(n.args[2],null),value=tr(n.args[3],null);
    return T.app((builtin==="path_from_transport"?transportToDependentPath:dependentPathToTransport)(dim,family,left,right),value);
  }
  if(builtin==="at"&&n.args.length===2)return T.at(tr(n.args[0],null),t.interval(n.args[1],env));
  if(builtin==="pair_induction"&&n.args.length===3) {
    const [motive,branch,value]=n.args.map(a=>tr(a,null));
    const sigma=scope.nf(inferred(value).type);
    if(sigma.tag!=="Sigma")throw Error("pair_induction requires a dependent pair.");
    const x=scope.fresh(),y=scope.fresh(),first=T.variable(x),second=T.variable(y);
    const fiber=T.app(T.lam(sigma.name,sigma.domain,sigma.body),first);
    const branchType=T.pi(x,sigma.domain,T.pi(y,fiber,
      T.app(motive,T.pair(sigma,first,second))));
    scope.check(branch,branchType);
    // Cubical Sigma eta identifies (fst p, snd p) with p. The native
    // checker verifies the dependent result conversion at the motive.
    const result=T.app(T.app(branch,T.first(value)),T.second(value));
    const type=T.app(motive,value),checked=scope.check(result,type);
    return scope.ascribe(checked,type);
  }
  if(builtin==="unit_induction"&&n.args.length===3) {
    const [motive,point,value]=n.args.map(a=>tr(a,null));
    return T.unitrec(motive,point,value);
  }
  if(builtin==="FunExt"&&n.args.length===6) {
    const [universe,A,B,f,g,h]=n.args.map(a=>tr(a,null));
    if(universe.tag!=="U")throw Error("FunExt needs a universe.");
    if(!finiteLevel(universe.level))throw scope.unit.locate(Error("FunExt takes a universe below UU0."),n.args[0]);
    scope.check(A,universe);
    const x=scope.fresh(),dim=scope.fresh("i"),variable=T.variable(x),fiber=T.app(B,variable);
    scope.check(B,T.pi(x,A,universe));
    const functionType=T.pi(x,A,fiber);
    scope.check(f,functionType);
    scope.check(g,functionType);
    const pointwise=T.pi(x,A,T.path(dim,fiber,T.app(f,variable),T.app(g,variable)));
    scope.check(h,pointwise);
    return T.line(dim,functionType,T.lam(x,A,T.at(T.app(h,variable),I.variable(dim))));
  }
  if(builtin==="absurd"&&n.args.length===1) {
    if(!expected)throw Error("absurd requires an expected type.");
    return T.abort(expected,tr(n.args[0],T.void));
  }
  if(["left","right"].includes(builtin)&&n.args.length===1) {
    if(!expected)throw Error("Sum injection requires an expected type.");
    const sum=scope.nf(expected);
    if(sum.tag!=="Sum")throw Error("Expected a sum type.");
    return (builtin==="left"?T.inl:T.inr)(expected,tr(n.args[0],sum[builtin]));
  }
  if(builtin==="refl"&&n.args.length===1) {
    const value=tr(n.args[0],null);return T.line(scope.fresh("i"),inferred(value).type,value);
  }
  if(builtin==="sym"&&n.args.length===1)return t.reversePath(scope,tr(n.args[0],null),"sym");
  if(builtin==="trans"&&n.args.length===2)
    return t.concatenatePaths(scope,tr(n.args[0],null),tr(n.args[1],null),"trans");
  if(builtin==="cong"&&n.args.length===2) {
    const fn=tr(n.args[0],null),p=tr(n.args[1],null),pt=scope.nf(inferred(p).type);
    if(pt.tag!=="Path")throw Error("cong requires a path.");
    const left=T.app(fn,pt.left),type=inferred(left).type,i=scope.fresh("i");
    const result=T.line(i,type,T.app(fn,T.at(p,I.variable(i))));
    return t.checker.ascribe && t.checker.kernel?.optimizations?.compactPaths !== false ? scope.ascribe(result,T.path(i,type,left,T.app(fn,pt.right))) : result;
  }
  if(builtin==="apd"&&n.args.length===4) {
    const [fn,x,y,p]=n.args.map(a=>tr(a,null));
    const pt=scope.nf(inferred(p).type),ft=scope.nf(inferred(fn).type);
    if(pt.tag!=="Path"||ft.tag!=="Pi"||!scope.equal(pt.left,x)||!scope.equal(pt.right,y))
      throw Error("Dependent action needs a function and a path with the supplied endpoints.");
    const i=scope.fresh("i"),family=T.app(T.lam(ft.name,ft.domain,ft.body),T.at(p,I.variable(i)));
    const action=T.line(i,family,T.app(fn,T.at(p,I.variable(i))));
    return T.app(dependentPathToTransport(i,family,T.app(fn,x),T.app(fn,y)),action);
  }
  if(builtin==="apd_path"&&n.args.length===2) {
    const fn=tr(n.args[0],null),p=tr(n.args[1],null);
    const ft=scope.nf(inferred(fn).type),pt=scope.nf(inferred(p).type);
    if(ft.tag!=="Pi"||pt.tag!=="Path"||freeDimensions(pt.family).has(pt.dim))
      throw Error("apd_path needs a dependent function and a homogeneous path.");
    scope.expect(pt.family,ft.domain);
    const dim=scope.fresh("i"),index=T.at(p,I.variable(dim));
    const family=T.app(T.lam(ft.name,ft.domain,ft.body),index);
    return T.line(dim,family,T.app(fn,index));
  }
  if(builtin==="transport"&&n.args.length===5) {
    const [family,x,y,p,value]=n.args.map(a=>tr(a,null));
    const pt=scope.nf(inferred(p).type);if(pt.tag!=="Path")throw Error("transport requires a path.");
    if(!scope.equal(pt.left,x)||!scope.equal(pt.right,y))throw Error("Transport endpoints do not match.");
    const i=scope.fresh("i");return T.comp(i,T.app(family,T.at(p,I.variable(i))),[],value);
  }
  if(builtin==="path_induction"&&n.args.length===6) {
    const [A,C,d,x,y,p]=n.args.map(a=>tr(a,null)),i=scope.fresh("i"),j=scope.fresh("j");
    const pt=scope.nf(inferred(p).type);
    if(pt.tag!=="Path"||!scope.equal(pt.family,A)||!scope.equal(pt.left,x)||!scope.equal(pt.right,y))throw Error("Path induction endpoints/carrier do not match.");
    const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
    const family=T.app(T.app(T.app(C,x),T.at(p,I.variable(i))),segment);
    return T.comp(i,family,[],T.app(d,x));
  }
  if(builtin==="based_induction"&&n.args.length===8) {
    const [universe,motiveUniverse,A,x,C,d,y,p]=n.args.map(a=>tr(a,null));
    if(universe.tag!=="U"||motiveUniverse.tag!=="U")throw Error("Based induction needs universes.");
    scope.check(A,universe);
    const b=scope.fresh(),q=scope.fresh(),i=scope.fresh("i"),j=scope.fresh("j");
    const pathType=T.path(j,A,x,T.variable(b));
    scope.check(C,T.pi(b,A,T.pi(q,pathType,motiveUniverse)));
    scope.check(p,T.path(j,A,x,y));
    const reflexivity=T.line(j,A,x);
    scope.check(d,T.app(T.app(C,x),reflexivity));
    const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
    return T.comp(i,T.app(T.app(C,T.at(p,I.variable(i))),segment),[],d);
  }
}
