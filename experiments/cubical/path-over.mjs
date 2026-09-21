// Dependent paths and paths out of transport describe the same boundary data.
// Everything here expands to Path, composition and derived filling; these
// helpers neither add axioms nor change the trusted checker.
import {T,fill,substituteDimension} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
import {equivalenceFromInverse,withNativeReferences} from './equivalence.mjs';

function bridge(dim,family,left,right,build) {
  return withNativeReferences([family,left,right],(family,left,right)=>{
    const used=new Set([dim]);
    const reserve=value=>{
      if(typeof value==='string')used.add(value.replace(/:[01]$/,''));
      else if(value&&typeof value==='object')Object.values(value).forEach(reserve);
    };
    [family,left,right].forEach(reserve);
    const fresh=stem=>{while(used.has(stem))stem+='_';used.add(stem);return stem;};
    const i=fresh('over'),j=fresh('along'),k=fresh('homotopy');
    const A=substituteDimension(family,dim,I.variable(i));
    const B=substituteDimension(A,i,I.one);
    const filled=fill(i,A,[],left,I.variable(i));
    const transported=T.comp(i,A,[],left);
    const dependent=T.path(i,A,left,right);
    const equality=T.path(j,B,transported,right);
    const to=p=>T.line(j,B,T.comp(i,A,[
      {face:F.endpoint(j,0),term:filled},
      {face:F.endpoint(j,1),term:T.at(p,I.variable(i))},
    ],left));
    const from=q=>T.line(i,A,T.comp(j,A,[
      {face:F.endpoint(i,0),term:left},
      {face:F.endpoint(i,1),term:T.at(q,I.variable(j))},
    ],filled));
    const eta=p=>{
      const q=to(p);
      const square=fill(i,A,[
        {face:F.endpoint(j,0),term:filled},
        {face:F.endpoint(j,1),term:T.at(p,I.variable(i))},
      ],left,I.variable(i));
      return T.line(k,dependent,T.line(i,A,T.comp(j,A,[
        {face:F.endpoint(i,0),term:left},
        {face:F.endpoint(i,1),term:T.at(q,I.variable(j))},
        {face:F.endpoint(k,1),term:square},
      ],filled)));
    };
    const epsilon=q=>{
      const p=from(q);
      const square=fill(j,A,[
        {face:F.endpoint(i,0),term:left},
        {face:F.endpoint(i,1),term:T.at(q,I.variable(j))},
      ],filled,I.variable(j));
      return T.line(k,equality,T.line(j,B,T.comp(i,A,[
        {face:F.endpoint(j,0),term:filled},
        {face:F.endpoint(j,1),term:T.at(p,I.variable(i))},
        {face:F.endpoint(k,1),term:square},
      ],left)));
    };
    const p=fresh('dependent_path'),q=fresh('transport_equality');
    return build({dependent,equality,fresh,
      forward:T.lam(p,dependent,to(T.variable(p))),
      backward:T.lam(q,equality,from(T.variable(q))),
      section:T.lam(p,dependent,eta(T.variable(p))),
      retraction:T.lam(q,equality,epsilon(T.variable(q))),
    });
  });
}

// The returned maps are functions, so their argument cannot accidentally be
// captured by one of the fresh filling dimensions.
export function dependentPathToTransport(dim,family,left,right) {
  return bridge(dim,family,left,right,b=>b.forward);
}
export function transportToDependentPath(dim,family,left,right) {
  return bridge(dim,family,left,right,b=>b.backward);
}
export function dependentPathTransportSection(dim,family,left,right) {
  return bridge(dim,family,left,right,b=>b.section);
}
export function dependentPathTransportRetraction(dim,family,left,right) {
  return bridge(dim,family,left,right,b=>b.retraction);
}
export function dependentPathTransportEquivalence(dim,family,left,right) {
  return bridge(dim,family,left,right,b=>{
    // Check the general quasi-inverse construction once under named maps and
    // laws. Applying it preserves the small proofs instead of duplicating
    // their filling cubes throughout its contraction proof.
    const f=b.fresh('forward'),g=b.fresh('backward');
    const eta=b.fresh('section'),eps=b.fresh('retraction');
    const x=b.fresh('source'),y=b.fresh('target'),k=b.fresh('law');
    const v=T.variable,S=b.dependent,E=b.equality;
    const bindings=[
      [f,T.pi(x,S,E),b.forward],
      [g,T.pi(y,E,S),b.backward],
      [eta,T.pi(x,S,T.path(k,S,T.app(v(g),T.app(v(f),v(x))),v(x))),b.section],
      [eps,T.pi(y,E,T.path(k,E,T.app(v(f),T.app(v(g),v(y))),v(y))),b.retraction],
    ];
    let result=equivalenceFromInverse(S,E,v(f),v(g),v(eta),v(eps));
    for(const [name,type]of [...bindings].reverse())result=T.lam(name,type,result);
    for(const [,,value]of bindings)result=T.app(result,value);
    return result;
  });
}
