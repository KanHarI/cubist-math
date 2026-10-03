import "../../../tests/fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {checkKernel} from './kernel-check.mjs';

const v=T.variable;
const universe=T.universe;
const family=level=>T.pi('x',T.unit,universe(level));
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point);

function accept(term,type,assumptions=[]) {
  const native=checkKernel(term,type,assumptions,{normalize:false});
  assert(native.ok,native.error);
  return native;
}
function reject(term,type,assumptions=[]) {
  assert.equal(checkKernel(term,type,assumptions,{normalize:false}).ok,false);
}

test('cumulative function results lift through nested binders without resizing domains',()=>{
  const constant=T.lam('x',T.unit,two);
  accept(constant,family(2));
  accept(T.lam('x',T.unit,T.lam('y',two,two)),
    T.pi('a',T.unit,T.pi('b',two,universe(2))));
  reject(v('large'),family(0),[['large',family(1)]]);
  reject(T.lam('A',universe(0),v('A')),T.pi('B',universe(1),universe(1)));
  // Directed cumulativity never makes U0 and U1 equal as terms.
  reject(T.line('i',universe(2),universe(0)),
    T.path('i',universe(2),universe(0),universe(1)));
});

test('cumulative dependent pair results retain the same first-component domain',()=>{
  const small=T.sigma('x',T.unit,universe(0));
  const large=T.sigma('y',T.unit,universe(2));
  accept(v('pair'),large,[['pair',small]]);
  reject(v('pair'),small,[['pair',large]]);
  reject(v('pair'),T.sigma('y',two,universe(2)),[['pair',small]]);
});

test('substituting a smaller universe preserves well-typed inferred types',()=>{
  // Generic use checks P : Unit -> U1. Instantiating B with a small type
  // produces lambda x:Unit.B, whose most precise inferred type is Unit -> U0.
  // The result type still contains the original family's use at level 1.
  const use=T.lam('P',family(1),T.app(v('P'),T.point));
  const resultType=T.app(use,T.lam('x',T.unit,v('B')));
  const generic=T.lam('B',universe(1),T.lam('b',resultType,v('b')));
  const instance=T.app(generic,two);
  const native=checkKernel(instance,null,[],{normalize:false});
  assert(native.ok,native.error);
  const exported=checkKernel(native.type,null,[],{normalize:false});
  assert(exported.ok,exported.error);
  const rechecked=checkKernel(instance,native.type,[],{normalize:false});
  assert(rechecked.ok,rechecked.error);
  accept(T.app(instance,left),two);
});
