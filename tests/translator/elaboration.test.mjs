import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T,freeNames} from '../../web/translator/core.mjs';
import {NameSupply} from '../../web/translator/names.mjs';
import {Scope,SourceUnit} from '../../web/translator/elaboration.mjs';
import {Translator} from '../../web/translator/translate.mjs';
import {kernelChecker} from './kernel-check.mjs';

test('a name supply never repeats a name, a kernel symbol spelling or a taken name',()=>{
  const names=new NameSupply({taken:name=>name==='x3'});
  assert.deepEqual([names.fresh('x'),names.fresh('a1'),names.fresh('x'),names.fresh('native'),names.fresh()],
    ['x1','a1_2','x4','native_5','b6']);
  // Each unit starts its own serial, so elaborating again repeats its names.
  assert.equal(new NameSupply().fresh('x'),'x1');
});

test('scopes are immutable and binding an existing name is an internal error',()=>{
  const unit=new SourceUnit({checker:kernelChecker(),source:'def x := 0;'});
  const outer=new Scope(unit),inner=outer.bind('x1',T.unit).alias('x',T.variable('x1'));
  assert.equal(outer.context.size,0);
  assert.equal(outer.env.size,0);
  assert.deepEqual([...inner.context.keys()],['x1']);
  assert.throws(()=>inner.bind('x1',T.unit),/Internal elaboration error: x1 is already bound/);
  const cube=outer.bindDimension('i1').bindDimension('j2');
  assert.deepEqual([...cube.dimensions],[['i1',0],['j2',1]]);
  assert.equal(outer.dimensions.size,0);
  assert.throws(()=>cube.bindDimension('i1'),/already bound/);
  assert.ok(Object.isFrozen(inner)&&Object.isFrozen(unit));
});

test('a derived unit shares its name supply and replaces only the given fields',()=>{
  const unit=new SourceUnit({checker:kernelChecker(),source:'a',moduleName:'m'});
  const replay=unit.with({source:'b'});
  assert.equal(replay.names,unit.names);
  assert.equal(replay.moduleName,'m');
  assert.equal(unit.source,'a');
  const error=replay.locate(Error('Bad.'),{start:0,end:1});
  assert.equal(error.message,'Bad. at 1:1');
});

test('elaborating a module twice yields the same generated names and inference queries',()=>{
  const source=`def twice(f : Unit -> Unit, n : Unit) := f(f(n));
    def id_(A : U0) : A -> A { intro x; exact x; }
    def Tagged(U < UU0, A : U) : U0 := Unit;
    def untag{{U < UU0, A : U}}(t : Tagged(U, A)) : Unit := t;
    def get(t : Tagged(U0, Unit)) : Unit := untag(t);`;
  const translate=()=>{
    const checker=kernelChecker(),nf=checker.nf,placeholders=[];
    // Normalization during inference sees unsolved term and universe holes.
    // Those queries must not depend on which modules were checked earlier.
    checker.nf=function(term,...args) {
      const names=[...freeNames(term)].filter(name=>name.includes('?'));
      if(names.length)placeholders.push(names);
      return nf.call(this,term,...args);
    };
    try {
      const result=new Translator({checker}).translate(source);
      assert.ok(result.declarations.every(d=>d.term),JSON.stringify(result.declarations.map(d=>d.reason)));
      return {terms:result.declarations.map(d=>d.term),placeholders};
    } finally {checker.kernel.dispose();}
  };
  const [first,second]=[translate(),translate()];
  assert.ok(first.placeholders.length,'the fixture must exercise inference placeholders');
  assert.deepEqual(first,second);
});
