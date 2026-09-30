// The existing library's explicit logical assumptions, represented as an
// ordinary context. The C kernel checks proofs abstracted over that context;
// it is never asked to trust a new inference rule or a theorem-specific axiom.
const V=name=>({tag:'Var',name}), U=level=>({tag:'U',level});
const pi=(name,domain,body)=>({tag:'Pi',name,domain,body});
const app=(fn,...args)=>args.reduce((fn,arg)=>({tag:'App',fn,arg}),fn);
const path=(A,x,y)=>({tag:'Path',dim:'axiom_path',family:A,left:x,right:y});
const prop=A=>pi('prop_x',A,pi('prop_y',A,path(A,V('prop_x'),V('prop_y'))));
const set=A=>pi('set_x',A,pi('set_y',A,prop(path(A,V('set_x'),V('set_y')))));
// The type of each assumption at a universe; truncate() gives the truncation
// at that universe.
function assumptionType(name, universe, truncate) {
  const A=V('A'), B=V('B'), P=V('P');
  const mere=T=>app(truncate(),T);
  let type;
  if(name==='Truncate')type=pi('A',universe,U(0));
  else if(name==='TruncateIntro')type=pi('A',universe,pi('a',A,mere(A)));
  else if(name==='TruncateProp')type=pi('A',universe,prop(mere(A)));
  else if(name==='TruncateElim')type=pi('A',universe,pi('P',universe,pi('proposition',prop(P),pi('map',pi('a',A,P),pi('witness',mere(A),P)))));
  else if(name==='LEM')type=pi('A',universe,pi('double_negation',pi('negation',pi('a',A,{tag:'Void'}),{tag:'Void'}),mere(A)));
  else if(name==='Choice') {
    const fiber=app(B,V('x')), sections=pi('x',A,fiber);
    type=pi('A',universe,pi('B',pi('x',A,universe),pi('setA',set(A),pi('setFibers',pi('x',A,set(fiber)),pi('inhabited',pi('x',A,mere(fiber)),mere(sections))))));
  }else throw Error(`Unsupported library assumption: ${name}`);
  return type;
}
// Each assumption is one entry, generic over the universes below UU0 (G0):
// LEM : forall U < UU0. forall A : U. …, used at a universe by instantiation.
// None has an instance at UU0 or above. Truncate keeps the archive's
// signature, into U0, until H1's universe-preserving Trunc replaces it.
export function libraryAssumption(checker,name,context=new Map(),truncateFormer=null) {
  let truncateSignature=null;
  const level='assumption_level',universe=U(V(level));
  if(truncateFormer && !['LEM','Choice'].includes(name))throw Error('Only LEM and Choice have rebuilt truncation signatures.');
  if(truncateFormer) {
    const expected={tag:'LPi',name:level,body:pi('A',universe,universe)};
    checker.check(truncateFormer,expected,context);
    // Require an admitted proposition truncation, rather than an arbitrary
    // function A -> U which could change the meaning of the assumption.
    const probe=checker.nf(app({tag:'LApp',fn:truncateFormer,level:V(level)},V('A')));
    const info=probe.tag==='Sort' ? checker.kernel.signatures.get(probe.signature) : null;
    const schema=info ? checker.kernel.signature(info.index) : null;
    const point=schema?.constructors[0], pointType=point ? checker.kernel.node(point.type) : null;
    const domain=pointType?.kind==='Pi' ? checker.kernel.node(pointType.children[0]) : null;
    const result=pointType?.kind==='Pi' ? checker.kernel.node(pointType.children[1]) : null;
    if(!schema || schema.modifier!==1 || schema.levels!==1 || schema.parameters!==1 || schema.recorded!==0
      || schema.constructors.length!==2 || point.generated || point.data!==1 || point.positions!==0 || point.dimensions!==0
      || domain?.kind!=='Var' || domain.payload!==schema.symbols[1] || result?.kind!=='Var' || result.payload!==schema.sort
      || probe.parameters.length!==1 || probe.parameters[0].tag!=='Var' || probe.parameters[0].name!=='A')
      throw Error('Rebuilt LEM and Choice require an admitted proposition truncation.');
    truncateSignature=probe.signature;
  }
  // Aliases of the same checked former share an assumption. Distinct
  // generative truncations have different keys and visible dependency labels.
  const label=truncateSignature ? `${name}[${truncateSignature.replaceAll('__','.')}]` : name;
  const key=truncateSignature ? `${name}:${truncateSignature}` : name;
  if(checker.libraryAssumptions.has(key))return checker.libraryAssumptions.get(key);
  const truncate=()=>({tag:'LApp',fn:truncateFormer ?? libraryAssumption(checker,'Truncate',context),level:V(level)});
  const type={tag:'LPi',name:level,body:assumptionType(name,universe,truncate)};
  const value=checker.assume(`__assumption_${name}${truncateSignature ? `_${truncateSignature}` : ''}`,type,new Set(context.keys()));
  checker.assumptionOrigins.set(value.name,{kind:'generic-assumption',name,truncateSignature,implementation:'web/cubical-assumptions.mjs'});
  checker.libraryAssumptions.set(key,value);
  checker.assumptionLabels.set(value.name,label);
  return value;
}
