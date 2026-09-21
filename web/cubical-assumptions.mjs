// The existing library's explicit logical assumptions, represented as an
// ordinary context. The C kernel checks proofs abstracted over that context;
// it is never asked to trust a new inference rule or a theorem-specific axiom.
const V=name=>({tag:'Var',name}), U=level=>({tag:'U',level});
const pi=(name,domain,body)=>({tag:'Pi',name,domain,body});
const app=(fn,...args)=>args.reduce((fn,arg)=>({tag:'App',fn,arg}),fn);
const path=(A,x,y)=>({tag:'Path',dim:'axiom_path',family:A,left:x,right:y});
const prop=A=>pi('prop_x',A,pi('prop_y',A,path(A,V('prop_x'),V('prop_y'))));
const set=A=>pi('set_x',A,pi('set_y',A,prop(path(A,V('set_x'),V('set_y')))));
// One schema builder drives both specialization and explanatory display. The
// symbolic U used in the display is elaborator notation, never a kernel term.
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
export function libraryAssumption(checker,name,level,context=new Map()) {
  const key=`${name}_U${level}`;
  if(checker.libraryAssumptions.has(key))return checker.libraryAssumptions.get(key);
  const type=assumptionType(name,U(level),()=>libraryAssumption(checker,'Truncate',level,context));
  const value=checker.assume(`__assumption_${key}`,type,new Set(context.keys()));
  checker.assumptionOrigins.set(value.name, {
    kind: 'universe-specialized-assumption', schema: name, universe: `U${level}`, level,
    schemaType: assumptionType(name,V('U'),()=>app(V('Truncate'),V('U'))),
    implementation: 'web/cubical-assumptions.mjs',
  });
  checker.libraryAssumptions.set(key,value);
  checker.assumptionLabels.set(value.name,`${name}(U${level})`);
  return value;
}
