import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {gunzipSync} from 'node:zlib';
import {T} from '../core.mjs';
import {checkNative} from '../native.mjs';

const unfoldingHints=[
  'field_logic__field_first',
  'identity_systems__identity_total_point',
  'identity_systems__identity_system_decode',
  'structured_sets__structure_iso_point',
  'structured_sets__structure_iso_center',
  'structured_sets__structure_equality_iso',
  'structured_sets__structure_iso_equality',
];
function referenceSyntax(value) {
  if(Array.isArray(value))return value.map(referenceSyntax);
  if(!value||typeof value!=='object')return value;
  return Object.fromEntries(Object.entries(value).map(([key,child])=>
    [key,key==='tag'&&child==='DefRef'?'Ref':referenceSyntax(child)]));
}
const fixture=referenceSyntax(JSON.parse(gunzipSync(readFileSync(
  new URL('../fixtures/structure-path-roundtrip.json.gz',import.meta.url)))));
const definitions=fixture.definitions.map(d=>({name:d.name,value:d.term,type:d.type}));

test('selective unfolding checks structure path roundtrip while keeping contraction folded',()=>{
  const plain=checkNative(fixture.term,fixture.expected,fixture.assumptions,{definitions,normalize:false});
  // An improved default converter may eventually succeed too. Until then its
  // resource rejection must remain explicit, never become an assumed theorem.
  assert(plain.ok||plain.error.includes('budget'),plain.error);
  const hinted=checkNative(fixture.term,fixture.expected,fixture.assumptions,
    {definitions,normalize:false,unfoldingHints});
  assert(hinted.ok,hinted.error);
  assert(hinted.reductionSteps<50000,`${hinted.reductionSteps} reductions`);
  assert(hinted.arenaNodes<400000,`${hinted.arenaNodes} arena nodes`);
});

test('the same selected unfolding strategy checks the final closed definition',()=>{
  let value=fixture.term,type=fixture.expected;
  for(const [name,domain]of [...fixture.assumptions].reverse()) {
    value=T.lam(name,domain,value);
    type=T.pi(name,domain,type);
  }
  const checked=checkNative(T.zero,T.nat,[],{normalize:false,definitions:[...definitions,
    {name:'closed_roundtrip',value,type,unfoldingHints}]});
  assert(checked.ok,checked.error);
});

test('unfolding hints never identify unequal definitions or fabricate path endpoints',()=>{
  const zero={tag:'Ref',name:'zero'},one={tag:'Ref',name:'one'};
  const definitions=[{name:'zero',value:T.zero,type:T.nat},
    {name:'one',value:T.succ(T.zero),type:T.nat}];
  const proof=T.line('i',T.nat,zero),falseType=T.path('i',T.nat,zero,one);
  for(const hints of [['zero'],['one'],['zero','one'],['one','zero']])
    assert.equal(checkNative(proof,falseType,[],{definitions,normalize:false,unfoldingHints:hints}).ok,false);
  assert.throws(()=>checkNative(proof,null,[],{definitions,unfoldingHints:['not_a_definition']}),/Unknown unfolding hint/);
});
