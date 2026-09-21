// Derived CCHM equivalence operations. These functions only BUILD inert terms;
// the ordinary reference/native checker must verify every result. The fiber
// orientation is y = f(x), matching CCHM §5.3 (the reverse of some HoTT APIs).
import {T,fill} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
const v=T.variable,ap=T.app,fst=T.first,snd=T.second;

// Reserve even bound spellings, making these syntax builders hygienic without
// depending on the checker's later alpha-renaming. Dimensions are reserved too.
function fresh(base,...terms) {
  const used=new Set(),seen=new WeakSet();
  const visit=x=>{
    if(typeof x==='string')used.add(x.replace(/:[01]$/,''));
    else if(x&&typeof x==='object'&&!seen.has(x)){seen.add(x);for(const value of Object.values(x))visit(value);}
  };
  terms.forEach(visit);
  while(used.has(base))base+='_';
  return base;
}
const path=(A,a,b)=>T.path(fresh('fiber_path',A,a,b),A,a,b);
export function contractible(A) {
  const c=fresh('center',A),x=fresh('point',A,c);
  return T.sigma(c,A,T.pi(x,A,path(A,v(c),v(x))));
}
export function fiber(A,B,f,y) {
  const x=fresh('preimage',A,B,f,y);
  return T.sigma(x,A,path(B,y,ap(f,v(x))));
}
export function equiv(A,B) {
  const f=fresh('function',A,B),x=fresh('argument',A,B,f),y=fresh('target',A,B,f,x);
  return T.sigma(f,T.pi(x,A,B),T.pi(y,B,contractible(fiber(A,B,v(f),v(y)))));
}

// The singleton (x:B) × Path B y x contracts by moving along its path.
// Both endpoint equations check by interval reduction and Sigma/Path eta.
export function identityEquivalence(B) {
  const x=fresh('argument',B),y=fresh('target',B,x),u=fresh('point',B,x,y);
  const i=fresh('i',B,x,y,u),j=fresh('j',B,x,y,u,i);
  const id=T.lam(x,B,v(x)),F=fiber(B,B,id,v(y));
  const center=T.pair(F,v(y),T.line(j,B,v(y)));
  const along=T.at(snd(v(u)),I.variable(i));
  const segment=T.line(j,B,T.at(snd(v(u)),I.meet(I.variable(i),I.variable(j))));
  const contraction=T.lam(u,F,T.line(i,F,T.pair(F,along,segment)));
  const proof=T.lam(y,B,T.pair(contractible(F),center,contraction));
  return T.pair(equiv(B,B),id,proof);
}

// Extend a compatible partial element of a contractible type. This is a
// composition in A, with walls following the center-to-point contraction.
export function extendContractible(A,proof,system) {
  const i=fresh('extension',A,proof,system);
  return T.comp(i,A,system.map(({face,term})=>({face,
    term:T.at(ap(snd(proof),term),I.variable(i))})),fst(proof));
}

// CCHM theorem 9: extend a partial element of the fiber of unglue. First use
// the supplied partial equivalences to extend their fibers, then fill the base
// path and glue its endpoint. Every object here is ordinary checked syntax.
export function extendUnglueFiber(G,u,system) {
  if(G.tag!=="Glue")throw Error("Unglue extension requires an explicit Glue type.");
  const A=G.base,b=fresh('glued_point',G,u,system);
  const unglue=T.lam(b,G,T.unglue(G,v(b)));
  const resultType=fiber(G,A,unglue,u);
  const j=fresh('base_path',G,u,system);
  const partial=G.system.map(part=>{
    const f=fst(part.equiv),localFiber=fiber(part.type,A,f,u);
    const localSystem=system.map(p=>({face:p.face,
      term:T.pair(localFiber,fst(p.term),snd(p.term))}));
    const extended=extendContractible(localFiber,ap(snd(part.equiv),u),localSystem);
    return {face:part.face,point:fst(extended),path:snd(extended)};
  });
  const paths=[...partial.map(p=>({face:p.face,term:T.at(p.path,I.variable(j))})),
    ...system.map(p=>({face:p.face,term:T.at(snd(p.term),I.variable(j))}))];
  const endpoint=T.comp(j,A,paths,u);
  const point=T.glue(G,endpoint,partial.map(p=>({face:p.face,term:p.point})));
  const path=T.line(j,A,fill(j,A,paths,u,I.variable(j)));
  return T.pair(resultType,point,path);
}

export function unglueEquivalence(G) {
  if(G.tag!=="Glue")throw Error("Unglue equivalence requires an explicit Glue type.");
  const b=fresh('glued_point',G),u=fresh('base_point',G,b),w=fresh('fiber_point',G,b,u);
  const i=fresh('contraction',G,b,u,w);
  const unglue=T.lam(b,G,T.unglue(G,v(b)));
  const targetFiber=fiber(G,G.base,unglue,v(u));
  const center=extendUnglueFiber(G,v(u),[]);
  const contracted=extendUnglueFiber(G,v(u),[
    {face:F.endpoint(i,0),term:center},{face:F.endpoint(i,1),term:v(w)},
  ]);
  const contraction=T.lam(w,targetFiber,T.line(i,targetFiber,contracted));
  const proof=T.lam(u,G.base,T.pair(contractible(targetFiber),center,contraction));
  return T.pair(equiv(G,G.base),unglue,proof);
}

// Contractibility is itself a proposition. Fill the square between the two
// center-to-point contractions, fixing its four sides explicitly.
export function contractibilityPath(A,c,d) {
  const i=fresh('center_path',A,c,d),j=fresh('point_path',A,c,d,i),x=fresh('point',A,c,d,i,j);
  const center=T.at(ap(snd(c),fst(d)),I.variable(i));
  const contraction=T.lam(x,A,T.line(j,A,extendContractible(A,c,[
    {face:F.endpoint(i,0),term:T.at(ap(snd(c),v(x)),I.variable(j))},
    {face:F.endpoint(i,1),term:T.at(ap(snd(d),v(x)),I.variable(j))},
    {face:F.endpoint(j,0),term:center},
    {face:F.endpoint(j,1),term:v(x)},
  ])));
  return T.line(i,contractible(A),T.pair(contractible(A),center,contraction));
}

// Equivalence witnesses are unique for a fixed forward map. This constructor
// deliberately supplies no proof that two different forward maps are equal.
// Its endpoints check only when their first projections are definitionally equal.
export function equivalenceWitnessPath(A,B,e0,e1) {
  const i=fresh('witness_path',A,B,e0,e1),y=fresh('target',A,B,e0,e1,i);
  const f=fst(e0),F=fiber(A,B,f,v(y));
  const witness=T.lam(y,B,T.at(contractibilityPath(F,ap(snd(e0),v(y)),ap(snd(e1),v(y))),I.variable(i)));
  return T.line(i,equiv(A,B),T.pair(equiv(A,B),f,witness));
}

export function totalEquivalences(A,level=0) {
  const X=fresh('carrier',A);
  return T.sigma(X,T.universe(level),equiv(v(X),A));
}

// CCHM corollary 10, in its contractible-total-space formulation of univalence.
// Glue provides the carrier path; uniqueness of equivalence witnesses repairs
// its two ends to the requested equivalences, rather than postulating a beta axiom.
export function univalenceContraction(A,level=0,identity=identityEquivalence(A)) {
  const total=totalEquivalences(A,level),z=fresh('equivalent_type',A,total);
  const i=fresh('carrier_path',A,total,z),j=fresh('repair',A,total,z,i);
  const center=T.pair(total,A,identity);
  const X=fst(v(z)),e=snd(v(z));
  const G=T.glueType(A,[
    {face:F.endpoint(i,0),type:A,equiv:identity},
    {face:F.endpoint(i,1),type:X,equiv:e},
  ]);
  const w=fresh('glue_equivalence',A,total,z,i,j);
  const b=fresh('glued_argument',A,total,z,i,j,w),y=fresh('fiber_target',A,total,z,i,j,w,b);
  const forward=T.lam(b,G,T.unglue(G,v(b)));
  const witnessType=T.pi(y,A,contractible(fiber(G,A,forward,v(y))));
  const current=T.pair(equiv(G,A),forward,v(w));
  const raw=T.pair(total,G,current);
  // The two repairs are checked under their respective endpoint faces, where
  // G reduces to A/X. A local binder avoids duplicating the large Glue proof.
  const startWitness=equivalenceWitnessPath(A,A,current,identity);
  const endWitness=equivalenceWitnessPath(X,A,current,e);
  const startRepair=T.pair(total,A,T.at(startWitness,I.variable(j)));
  const endRepair=T.pair(total,X,T.at(endWitness,I.variable(j)));
  const repaired=T.comp(j,total,[
    {face:F.endpoint(i,0),term:startRepair},
    {face:F.endpoint(i,1),term:endRepair},
  ],raw);
  const shared=T.app(T.lam(w,witnessType,repaired),snd(unglueEquivalence(G)));
  const contraction=T.lam(z,total,T.line(i,total,shared));
  return T.pair(contractible(total),center,contraction);
}

// Strict inverse maps give a particularly small fiber contraction. This is a
// syntax builder, not a rule assuming an inverse: both inverse equations must
// hold by ordinary conversion or the constructed term is rejected.
export function strictIsomorphismEquivalence(A,B,forward,inverse) {
  const y=fresh('target',A,B,forward,inverse),u=fresh('fiber_point',A,B,forward,inverse,y);
  const i=fresh('contraction',A,B,forward,inverse,y,u),j=fresh('segment',A,B,forward,inverse,y,u,i);
  const F=fiber(A,B,forward,v(y));
  const center=T.pair(F,ap(inverse,v(y)),T.line(j,B,v(y)));
  const along=T.at(snd(v(u)),I.variable(i));
  const segment=T.line(j,B,T.at(snd(v(u)),I.meet(I.variable(i),I.variable(j))));
  const contraction=T.lam(u,F,T.line(i,F,T.pair(F,ap(inverse,along),segment)));
  return T.pair(equiv(A,B),forward,T.lam(y,B,T.pair(contractible(F),center,contraction)));
}

// Connect two points of a fiber using only inverse homotopies. The successive
// fillings make the coherence square explicit, avoiding strict-J adjointification.
// Adapted to y = f(x) from Cubical.Foundations.Isomorphism.lemIso:
// https://github.com/agda/cubical/blob/master/Cubical/Foundations/Isomorphism.agda
function inverseFiberPath(A,B,f,g,eta,epsilon,y,u0,u1) {
  const used=[A,B,f,g,eta,epsilon,y,u0,u1];
  const dimension=stem=>{const name=fresh(stem,used);used.push(name);return name;};
  const i=dimension('fiber_axis'),j=dimension('square_axis'),k=dimension('comparison_axis');
  const h0=dimension('first_fill'),h1=dimension('second_fill'),h2=dimension('middle_fill');
  const x0=fst(u0),x1=fst(u1),p0=snd(u0),p1=snd(u1),gy=ap(g,y);
  const first=(r,s)=>fill(h0,A,[
    {face:F.equalEndpoint(r,1),term:T.at(ap(eta,x0),I.variable(h0))},
    {face:F.equalEndpoint(r,0),term:gy},
  ],ap(g,T.at(p0,r)),s);
  const second=(r,s)=>fill(h1,A,[
    {face:F.equalEndpoint(r,1),term:T.at(ap(eta,x1),I.variable(h1))},
    {face:F.equalEndpoint(r,0),term:gy},
  ],ap(g,T.at(p1,r)),s);
  const middle=(r,s)=>fill(h2,A,[
    {face:F.equalEndpoint(r,1),term:second(I.variable(h2),I.one)},
    {face:F.equalEndpoint(r,0),term:first(I.variable(h2),I.one)},
  ],gy,s);
  const r=I.variable(i),s=I.variable(j),t=I.variable(k);
  const p=middle(r,I.one);
  // This square has edges g(p0), g(p1), g(f(p)), and the constant g(y).
  const square=T.comp(k,A,[
    {face:F.endpoint(i,1),term:second(s,I.reverse(t))},
    {face:F.endpoint(i,0),term:first(s,I.reverse(t))},
    {face:F.endpoint(j,1),term:T.at(ap(eta,p),I.reverse(t))},
    {face:F.endpoint(j,0),term:gy},
  ],middle(r,s));
  // epsilon changes those four edges into p0, p1, f(p), and y.
  const imageSquare=T.comp(k,B,[
    {face:F.endpoint(i,1),term:T.at(ap(epsilon,T.at(p1,s)),t)},
    {face:F.endpoint(i,0),term:T.at(ap(epsilon,T.at(p0,s)),t)},
    {face:F.endpoint(j,1),term:T.at(ap(epsilon,ap(f,p)),t)},
    {face:F.endpoint(j,0),term:T.at(ap(epsilon,y),t)},
  ],ap(f,square));
  const targetFiber=fiber(A,B,f,y);
  return T.line(i,targetFiber,T.pair(targetFiber,p,T.line(j,B,imageSquare)));
}

// eta(x): g(f(x)) = x; epsilon(y): f(g(y)) = y. Neither homotopy is
// required to compute to reflexivity, and no triangle identity is assumed.
function inverseEquivalenceTerm(A,B,f,g,eta,epsilon) {
  const y=fresh('target',A,B,f,g,eta,epsilon),u=fresh('fiber_point',A,B,f,g,eta,epsilon,y);
  const r=fresh('reverse_section',A,B,f,g,eta,epsilon,y,u);
  const F=fiber(A,B,f,v(y));
  const section=T.line(r,B,T.at(ap(epsilon,v(y)),I.reverse(I.variable(r))));
  const center=T.pair(F,ap(g,v(y)),section);
  const contraction=T.lam(u,F,inverseFiberPath(A,B,f,g,eta,epsilon,v(y),center,v(u)));
  return T.pair(equiv(A,B),f,T.lam(y,B,T.pair(contractible(F),center,contraction)));
}

// Reference names are opaque to this syntax builder. Temporarily represent
// them by fresh free names while using the reference fill/substitution helpers,
// then restore the exact native reference nodes. Only the native registry can
// certify these references; no global definition is treated as an assumption.
export function withNativeReferences(inputs,build) {
  const references=new Map(),reserved=[...inputs];
  const rewrite=(node,restore=false)=>{
    if(Array.isArray(node))return node.map(value=>rewrite(value,restore));
    if(!node||typeof node!=="object")return node;
    if(restore&&node.tag==="Var"&&references.has(node.name))return references.get(node.name);
    if(!restore&&["Ref","DefRef"].includes(node.tag)) {
      const name=fresh('checked_reference',reserved);
      reserved.push(name);
      references.set(name,node);
      return v(name);
    }
    return Object.fromEntries(Object.entries(node).map(([key,value])=>[key,rewrite(value,restore)]));
  };
  const symbolic=inputs.map(input=>rewrite(input));
  return rewrite(build(...symbolic),true);
}

export function equivalenceFromInverse(A,B,f,g,eta,epsilon) {
  return withNativeReferences([A,B,f,g,eta,epsilon],inverseEquivalenceTerm);
}

// The standard Glue universe path, with exactly the supplied equivalence on
// the starting face and the identity equivalence on the ending face.
export function univalencePath(A,B,e,level=0) {
  return withNativeReferences([A,B,e],(A,B,e)=>{
    const i=fresh('univalence',A,B,e);
    return T.line(i,T.universe(level),T.glueType(B,[
      {face:F.endpoint(i,0),type:A,equiv:e},
      {face:F.endpoint(i,1),type:B,equiv:identityEquivalence(B)},
    ]));
  });
}

// Applying unglue to the transport filling gives a path from f(x) to transport(x).
// Reversing that path gives the usual propositional beta law. The filler and
// its endpoints are checked cubical operations, not a univalence-beta axiom.
export function univalenceTransportBeta(A,B,e,x) {
  return withNativeReferences([A,B,e,x],(A,B,e,x)=>{
    const i=fresh('transport_beta',A,B,e,x),k=fresh('transport_direction',A,B,e,x,i);
    const identity=identityEquivalence(B);
    const G=r=>T.glueType(B,[
      {face:F.equalEndpoint(r,0),type:A,equiv:e},
      {face:F.equalEndpoint(r,1),type:B,equiv:identity},
    ]);
    const reverse=I.reverse(I.variable(i));
    const filled=fill(k,G(I.variable(k)),[],x,reverse);
    return T.line(i,B,T.unglue(G(reverse),filled));
  });
}
