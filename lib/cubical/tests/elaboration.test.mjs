import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {NameSupply} from '../names.mjs';
import {Scope,SourceUnit} from '../elaboration.mjs';
import {Translator} from '../translate.mjs';

test('a name supply never repeats a name, a kernel symbol spelling or a taken name',()=>{
  const names=new NameSupply({taken:name=>name==='x3'});
  assert.deepEqual([names.fresh('x'),names.fresh('a1'),names.fresh('x'),names.fresh('native'),names.fresh()],
    ['x1','a1_2','x4','native_5','b6']);
  // Each unit starts its own serial, so elaborating again repeats its names.
  assert.equal(new NameSupply().fresh('x'),'x1');
});

test('scopes are immutable and binding an existing name is an internal error',()=>{
  const unit=new SourceUnit({checker:new Checker(),source:'def x := 0;'});
  const outer=new Scope(unit),inner=outer.bind('x1',T.nat).alias('x',T.variable('x1'));
  assert.equal(outer.context.size,0);
  assert.equal(outer.env.size,0);
  assert.deepEqual([...inner.context.keys()],['x1']);
  assert.throws(()=>inner.bind('x1',T.nat),/Internal elaboration error: x1 is already bound/);
  const cube=outer.bindDimension('i1').bindDimension('j2');
  assert.deepEqual([...cube.dimensions],[['i1',0],['j2',1]]);
  assert.equal(outer.dimensions.size,0);
  assert.throws(()=>cube.bindDimension('i1'),/already bound/);
  assert.ok(Object.isFrozen(inner)&&Object.isFrozen(unit));
});

test('a derived unit shares its name supply and replaces only the given fields',()=>{
  const unit=new SourceUnit({checker:new Checker(),source:'a',moduleName:'m'});
  const replay=unit.with({source:'b'});
  assert.equal(replay.names,unit.names);
  assert.equal(replay.moduleName,'m');
  assert.equal(unit.source,'a');
  const error=replay.locate(Error('Bad.'),{start:0,end:1});
  assert.equal(error.message,'Bad. at 1:1');
});

test('elaborating a module twice yields the same generated names',()=>{
  const source='def twice(f : Nat -> Nat, n : Nat) := f(f(n)); def id(A : U0) : A -> A { intro x; exact x; }';
  const [first,second]=[new Translator().translate(source),new Translator().translate(source)];
  assert.deepEqual(first.declarations.map(d=>d.term),second.declarations.map(d=>d.term));
});
