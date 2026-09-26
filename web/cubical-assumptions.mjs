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
export function libraryAssumption(checker,name,context=new Map()) {
  if(checker.libraryAssumptions.has(name))return checker.libraryAssumptions.get(name);
  const level='assumption_level',universe=U(V(level));
  const truncate=()=>({tag:'LApp',fn:libraryAssumption(checker,'Truncate',context),level:V(level)});
  const type={tag:'LPi',name:level,body:assumptionType(name,universe,truncate)};
  const value=checker.assume(`__assumption_${name}`,type,new Set(context.keys()));
  checker.assumptionOrigins.set(value.name,{kind:'generic-assumption',name,implementation:'web/cubical-assumptions.mjs'});
  checker.libraryAssumptions.set(name,value);
  checker.assumptionLabels.set(value.name,name);
  return value;
}
