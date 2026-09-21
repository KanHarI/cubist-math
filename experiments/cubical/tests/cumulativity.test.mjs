import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {checkNative} from '../native.mjs';

const v=T.variable;
const universe=T.universe;
const family=level=>T.pi('x',T.unit,universe(level));

function accept(term,type,assumptions=[]) {
  const checker=new Checker();
  checker.verify(term,type,assumptions);
  const native=checkNative(term,type,assumptions,{normalize:false});
  assert(native.ok,native.error);
  return native;
}
function reject(term,type,assumptions=[]) {
  assert.throws(()=>new Checker().verify(term,type,assumptions));
  assert.equal(checkNative(term,type,assumptions,{normalize:false}).ok,false);
}

test('cumulative function results lift through nested binders without resizing domains',()=>{
  const constant=T.lam('x',T.unit,T.nat);
  accept(constant,family(2));
  accept(T.lam('x',T.unit,T.lam('y',T.nat,T.nat)),
    T.pi('a',T.unit,T.pi('b',T.nat,universe(2))));
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
  reject(v('pair'),T.sigma('y',T.nat,universe(2)),[['pair',small]]);
});

test('substituting a smaller universe preserves well-typed inferred types',()=>{
  // Generic use checks P : Unit -> U1. Instantiating B with Nat produces
  // lambda x:Unit.Nat, whose most precise inferred type is Unit -> U0.
  // The result type still contains the original family's use at level 1.
  const use=T.lam('P',family(1),T.app(v('P'),T.point));
  const resultType=T.app(use,T.lam('x',T.unit,v('B')));
  const generic=T.lam('B',universe(1),T.lam('b',resultType,v('b')));
  const instance=T.app(generic,T.nat);
  const reference=new Checker().verify(instance);
  new Checker().verify(reference.type);
  const native=checkNative(instance,null,[],{normalize:false});
  assert(native.ok,native.error);
  const exported=checkNative(native.type,null,[],{normalize:false});
  assert(exported.ok,exported.error);
  const rechecked=checkNative(instance,native.type,[],{normalize:false});
  assert(rechecked.ok,rechecked.error);
  accept(T.app(instance,T.zero),T.nat);
});
