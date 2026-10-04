// A test fixture: unglue as an equivalence, CCHM theorem 9, as the
// translator built it before library/univalence.cubist proved it in Cubist
// (glue_line_equiv). Its normal form has compositions whose tubes the
// kernel's reduction splits otherwise than the term's own derivation does,
// which tests/translator/univalence-derived.test.mjs checks again (work plan
// I1.2c). The builders only build syntax; the kernel checks every result.
import {T,fill} from '../../web/translator/core.mjs';
import {interval as I,face as F} from '../../web/translator/lattice.mjs';
import {syntaxNames} from '../../web/translator/syntax-graph.mjs';
import {contractible,fiber,equiv,extendContractible} from '../../web/translator/equivalence.mjs';
const v=T.variable,ap=T.app,fst=T.first,snd=T.second;

function fresh(base,...terms) {
  const used=syntaxNames(terms);
  while(used.has(base))base+='_';
  return base;
}

// Extend a partial element of the fiber of unglue: extend the pieces'
// fibers by their equivalences, then fill the base path and glue its end.
function extendUnglueFiber(G,u,system) {
  const A=G.base,b=fresh('glued_point',G,u,system);
  const unglue=T.lam(b,G,T.unglue(G,v(b)));
  const resultType=fiber(G,A,unglue,u);
  const j=fresh('base_path',G,u,system);
  const partial=G.system.map(part=>{
    const f=fst(part.equiv),localFiber=fiber(part.type,A,f,u);
    const localSystem=system.map(p=>({face:p.face,term:T.pair(localFiber,fst(p.term),snd(p.term))}));
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

// unglue : Glue [φ ↦ (T, e)] A → A, with its contractible fibers.
export function unglueEquivalence(G) {
  const b=fresh('glued_point',G),u=fresh('base_point',G,b),w=fresh('fiber_point',G,b,u);
  const i=fresh('contraction',G,b,u,w);
  const unglue=T.lam(b,G,T.unglue(G,v(b)));
  const targetFiber=fiber(G,G.base,unglue,v(u));
  const center=extendUnglueFiber(G,v(u),[]);
  const contracted=extendUnglueFiber(G,v(u),[{face:F.endpoint(i,0),term:center},{face:F.endpoint(i,1),term:v(w)}]);
  const contraction=T.lam(w,targetFiber,T.line(i,targetFiber,contracted));
  const proof=T.lam(u,G.base,T.pair(contractible(targetFiber),center,contraction));
  return T.pair(equiv(G,G.base),unglue,proof);
}
export {equiv};
