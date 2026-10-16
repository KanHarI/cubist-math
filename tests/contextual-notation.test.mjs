import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram,checkTestModule} from "./check-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";

const module=await create(),nat="inductive Nat { zero; succ(n : Nat); }\n";
async function setup(t,source,dependency) {
  const read=sourceReader(),reader=(name,...args)=>name==="fixture"?dependency:read(name,...args);
  const off=await checkProgram(t,source,{module,reader});
  const on=await checkProgram(t,source,{module,reader,options:{collectScopes:true}});
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  const points=[...on.program.scopePoints.values()];
  for(const point of points)assert.deepEqual(JSON.parse(JSON.stringify(point)),point);
  return on.program;
}
function selected(t,program,source,marker,{module="fixture",length=marker.length}={}) {
  assert.equal(source.split(marker).length,2);
  const start=source.indexOf(marker),points=[...program.scopePoints.values()].filter(point=>point.origin.module===module
    &&point.origin.start===start&&point.origin.end===start+length&&point.phase==="expression"&&point.origin.expansion.some(frame=>frame.kind==="notation"));
  assert.equal(points.length,1,JSON.stringify(points.map(({id,origin})=>({id,origin}))));
  assert.ok(points[0].available,points[0].reason);
  const session=new ContextualSession(program,points[0].id);
  t.after(()=>session.dispose());return session;
}
async function query(session,input,kind,text) {
  const [answer]=await session.run(input);
  assert.equal(answer.kind,kind,JSON.stringify(answer));
  if(text!==undefined)assert.equal(answer.text,text);
  return answer;
}

test("notation-body queries keep source globals, local binders and lazy caller operands separate",async t=>{
  const dependency=nat+`def base : Nat := zero;
    def unused : Nat := succ(zero);
    notation pick { x + y := (fun (z : Nat) => x)(base); }
    def later_ : Unit := tt;`;
  const source=`import fixture;
    def base : Nat := succ(succ(zero));
    def f(p : Nat) : Nat := pick.(p + absent);
    def checked : f(succ(zero)) = succ(zero) := refl(succ(zero));`;
  const program=await setup(t,source,dependency);
  const session=selected(t,program,dependency,"x)(base)",{length:1});
  const work=program.kernel.work(),definitions=[...program.kernel.definitions];
  await query(session,"x","value","p");
  await query(session,"typed(base = zero, refl(base))","value");
  await query(session,"typed(base = succ(succ(zero)), refl(base))","error");
  await query(session,"unused","value","succ(zero)");
  await query(session,"typeof z","type","Nat");
  for(const input of ["p","later_","y"])await query(session,input,"error");
  const locals=await query(session,"/locals","locals");
  assert.deepEqual(locals.bindings.filter(row=>row.visible).map(row=>row.label),["x","y","z"]);
  assert.equal(locals.bindings.filter(row=>row.deferred).length,2,"listing locals does not force the unused ill-typed operand");
  await query(session,"let saved := x","defined");
  await query(session,"let x := zero","defined");
  await query(session,"typed(saved = x, refl(saved))","error");
  await query(session,"saved","value","p");
  assert.deepEqual(program.kernel.work(),work);
  assert.deepEqual([...program.kernel.definitions],definitions);
});

test("nested notation operands replay their original caller without eager evaluation",async t=>{
  const dependency=nat+`notation first { x + y := x; }
    notation outer { a * b := first.(a + b); }`;
  const source="import fixture; def f(p : Nat) : Nat := outer.(p * absent);";
  const program=await setup(t,source,dependency);
  const session=selected(t,program,dependency,"x;",{length:1});
  await query(session,"x","value","p");
  await query(session,"y","error");
  await query(session,"p","error");
  await query(session,"a","error");
  await query(session,"let saved := x","defined");
  await query(session,"typed(saved = x, refl(saved))","value");
});

test("foreign notation names cannot hide caller definition evidence",async t=>{
  const dependency=`import nat; import hlevels;
    inductive Quotient(A : U0, R : A -> A -> U0) : U0 {
      class(a : A); relate(a, b : A, r : R(a, b)) : class(a) = class(b);
    }
    theory T(U < UU0) { M : U; ev : M; }
    def chosen : T(U0) := T.make(Unit, tt);
    notation qe { x + y := match x return Nat { class(a) => y; } obligations by hlevel; }
    notation qf { x + y := (fun (ev : Unit) => match x return Nat { class(a) => y; } obligations by hlevel)(tt); }
    notation qm { x + y := chosen.(match x return Nat { class(a) => y; } obligations by hlevel); }
    notation outer { u * v := qe.(u + v); }
    notation keep { x + y := x; }`;
  const read=sourceReader(),reader=(name,...args)=>name==="fixture"?dependency:read(name,...args);
  for(const [name,local,expression,accepts] of [
    ["left operand", "let x := h(tt);", "qe.(q + b)",true],
    ["right operand", "let y := h(tt);", "qe.(q + b)",true],
    ["inner binder", "let ev := h(tt);", "qf.(q + b)",true],
    ["inner opening", "let ev := h(tt);", "qm.(q + b)",true],
    ["nested rule", "let u := h(tt);", "outer.(q * b)",true],
    ["lazy operand", "let x := h(tt);", "keep.((match q return Nat { class(a) => b; } obligations by hlevel) + absent)",true],
    ["no evidence", "", "qe.(q + b)",false],
    ["caller shadowing", "let y := h(tt); let y := tt;", "qe.(q + b)",false],
  ])await t.test(name,async()=>{
    const source=`import nat; import hlevels; import fixture;
      def probe_(A : U0, R : A -> A -> U0, h : Unit -> IsProp(U0, Nat), b : Nat, q : Quotient(A, R)) : Nat {
        ${local} exact ${expression};
      }`;
    const off=new CubicalProgram(module,reader),on=new CubicalProgram(module,reader,{collectScopes:true});
    try {
      const offResult=await off.check(source,"main"),onResult=await on.check(source,"main");
      assert.equal(onResult.gaps.length,accepts?0:1,JSON.stringify(onResult.gaps));
      assert.deepEqual(onResult.outputs,offResult.outputs);
      assert.deepEqual(onResult.links,offResult.links);
      assert.deepEqual(on.kernel.work(),off.kernel.work());
      const point=[...on.scopePoints.values()].find(point=>point.origin.module==="main"
        &&point.phase==="before"&&point.origin.start===source.indexOf(`exact ${expression};`));
      assert.ok(point?.available,point?.reason);
      const session=new ContextualSession(on,point.id);
      try {await query(session,`/prove { exact ${expression}; }`,accepts?"proof":"error");}
      finally {session.dispose();}
      if(name==="inner binder") {
        const marker="match x return Nat { class(a) => y; } obligations by hlevel",start=dependency.indexOf(marker+")(tt)");
        const instances=[...on.scopePoints.values()].filter(point=>point.origin.module==="fixture"
          &&point.phase==="expression"&&point.origin.start===start&&point.origin.end===start+marker.length);
        assert.equal(instances.length,2,"the lambda body is inferred and checked in distinct contexts");
        for(const point of instances) {
          assert.ok(point.available,point.reason);
          const inside=new ContextualSession(on,point.id);
          try {
            await query(inside,"typed(Nat, qe.(x + y))","value");
            await query(inside,"let saved := x","defined");
            await query(inside,"typed(Nat, qe.(saved + y))","value");
          } finally {inside.dispose();}
        }
      }
    } finally {off.dispose();on.dispose();}
  });
});

test("lazy dependent matches refine caller identities without a query scope collector",async t=>{
  const source=nat+`notation eqn { x + y := typed(y = y, x); }
    def f(n : Nat) : n = n := eqn.((match n {
      zero => refl(zero); succ(k) => refl(succ(k));
    }) + n);
    def checked : f(zero) = refl(zero) := refl(refl(zero));`;
  const program=await setup(t,source);
  const session=selected(t,program,source,"typed(y = y, x)",{module:"main"});
  const work=program.kernel.work(),definitions=[...program.kernel.definitions];
  await query(session,"y","value","n");
  await query(session,"typed(y = y, x)","value");
  await query(session,"let saved := typed(y = y, x)","defined");
  await query(session,"typed(y = y, saved)","value");
  await query(session,"typed(y = succ(y), x)","error");
  await query(session,"typed(y = y, saved)","value");
  assert.equal(session.accepted.length,1);
  assert.deepEqual(program.kernel.work(),work);
  assert.deepEqual([...program.kernel.definitions],definitions);
});

test("lazy operand recipes retain their selected notation in copied scoped syntax",async t=>{
  const dependency=nat+`notation shifted { numeral(n : Nat) := succ(n); }
    notation power { x ^ shifted.(n) := n; }`;
  const source="import fixture; def f : Nat := power.(zero ^ 1);";
  const program=await setup(t,source,dependency);
  const session=selected(t,program,dependency,"n; }",{length:1});
  await query(session,"n","value","succ(succ(zero))");
  await query(session,"let saved := n","defined");
  await query(session,"typed(saved = succ(succ(zero)), refl(saved))","value");
  await query(session,"typed(saved = succ(zero), refl(saved))","error");
});

test("lazy interval and universe operands keep their caller's dimensions and levels",async t=>{
  const dependency=`notation endpoint { p ^ i := p @ i; }
    notation universes { U + x := U; }`;
  const source=`import fixture;
    def line(q : tt = tt) : tt = tt := path j => endpoint.(q ^ j);
    def universe{{V < UU0}} : UU0 := universes.(V + absent);`;
  const program=await setup(t,source,dependency);
  const interval=selected(t,program,dependency,"p @ i");
  await query(interval,"typed((p @ i) = (p @ i), refl(p @ i))","value");
  await query(interval,"q","error");
  const universe=selected(t,program,dependency,"U;",{length:1});
  await query(universe,"U","value","V");
  await query(universe,"V","error");
});

test("lazy recursive arguments preserve structural permissions through query history",async t=>{
  const dependency=nat+"notation keep { x + y := x; }";
  const source=`import fixture; def f(n : Nat) : Nat := match n {
    zero => zero; succ(k) => keep.(f(k) + absent);
  };`;
  const program=await setup(t,source,dependency);
  const session=selected(t,program,dependency,"x;",{length:1});
  await query(session,"typeof x","type","Nat");
  await query(session,"let saved := x","defined");
  await query(session,"let invalid : Unit := x","error");
  await query(session,"typed(saved = x, refl(saved))","value");
  await query(session,"f(n)","error");
  const invalid=await checkProgram(t,source.replace("f(k)","f(n)"),{module,reader:async()=>dependency});
  assert.ok(invalid.result.gaps.some(gap=>gap.name==="f"),"the source checker independently refuses a non-decreasing call");
});

test("forcing a lazy operand spends the query's fuel and uses its fresh name supply",async t=>{
  const dependency=nat+"notation keep { x + y := x; }";
  const source="import fixture; def f(p : Nat) : Nat := keep.(succ(p) + absent);";
  const program=await setup(t,source,dependency),session=selected(t,program,dependency,"x;",{length:1});
  const term=Translator.prototype.term;
  let queryUnit,forced=false;
  Translator.prototype.term=function(node,scope,expected) {
    if(scope.unit.moduleName.startsWith("contextual-session/"))queryUnit=scope.unit;
    if(queryUnit&&node.kind==="call"&&node.origin?.module==="main"&&node.start===source.indexOf("succ(p)")) {
      forced=true;
      assert.equal(scope.unit.fuel,queryUnit.fuel);
      assert.equal(scope.unit.names,queryUnit.names);
      assert.notEqual(scope.checker.kernel.handle,program.kernel.handle);
      scope.spend("queries",scope.unit.fuel.limits.queries+1);
    }
    return term.call(this,node,scope,expected);
  };
  let answer;
  try {answer=await query(session,"x","error");}
  finally {Translator.prototype.term=term;}
  assert.ok(forced);
  assert.equal(answer.failure,"fuel");assert.equal(answer.stage,"query");
  await query(session,"x","value","succ(p)");
  assert.equal(session.accepted.length,0);
});

test("model-numeral implementation scopes preserve the selected receiver",async t=>{
  const source=nat+`theory Reader(U < UU0) { M : U; read(n : Nat) : M;
      def numeral_(n : Nat) : M := read(n) notation numeral;
    }
    def raised : Reader(U0) := Reader.make(Nat, fun (n : Nat) => succ(n));
    def f(p : Nat) : Nat := raised.(2);`;
  const program=await setup(t,source);
  const points=[...program.scopePoints.values()].filter(point=>point.declaration==="f"
    &&point.origin.module==="main"&&point.origin.start===source.indexOf("2)")&&point.origin.end===source.indexOf("2)")+1);
  assert.ok(points.length);
  for(const point of points) {
    assert.ok(point.available,point.reason);
    const session=new ContextualSession(program,point.id);t.after(()=>session.dispose());
    await query(session,"typed(2 = succ(succ(succ(zero))), refl(2))","value");
    await query(session,"typed(2 = succ(succ(zero)), refl(2))","error");
  }
});

test("model numerals keep their authored definition and view links",async t=>{
  for(const collectScopes of [false,true]) {
    const {source,result}=await checkTestModule(t,"notation_literals",{module,options:{collectScopes}});
    const start=source.indexOf("counting.(2 + 5)");
    assert.ok(start>=0);
    for(const offset of [start+10,start+14]) {
      const links=result.links.filter(link=>link.start===offset&&link.end===offset+1);
      assert.ok(links.some(link=>link.binding?.endsWith("__Rig.of_nat")),JSON.stringify(links));
      assert.ok(links.some(link=>link.role==="local"&&link.binding.startsWith('["view",')),JSON.stringify(links));
    }
  }
});

test("literal-reader instances keep their lazy lexeme and qualified source origin",async t=>{
  const dependency="import lexemes; notation decimal { literal(s : Lexeme) := natural_literal(s); }";
  const source="import fixture; def f : Nat := decimal.(32);";
  const program=await setup(t,source,dependency),marker="natural_literal(s)",start=dependency.indexOf(marker);
  const points=[...program.scopePoints.values()].filter(point=>point.origin.module==="fixture"
    &&point.origin.start===start&&point.origin.end===start+marker.length&&point.phase==="expression");
  assert.equal(points.length,2,"parse-answer and parsed-value are separate elaboration instances");
  for(const point of points) {
    assert.ok(point.available,point.reason);
    const session=new ContextualSession(program,point.id);t.after(()=>session.dispose());
    // Literal operands remain syntax. Their list constructors need the same
    // expected type they receive at the original reader's call boundary.
    await query(session,"typeof s","error");
    await query(session,"typeof typed(Lexeme, s)","type","List(__U, Glyph)");
    await query(session,"natural_literal(s)","value");
    const locals=await query(session,"/locals","locals");
    assert.ok(locals.bindings.some(row=>row.label==="s"&&row.deferred));
  }
});

test("a lazy selector keeps the passed notation distinct from the rule's source notation",async t=>{
  const dependency=nat+`notation numeric { numeral(n : Nat) := succ(n); }
    notation select_operand { m + x := m.(0); }`;
  const source=`import fixture; notation numeric { numeral(n : Nat) := succ(succ(n)); }
    def f : Nat := select_operand.(numeric + absent);`;
  const program=await setup(t,source,dependency),session=selected(t,program,dependency,"m.(0)");
  await query(session,"m.(1)","value","succ(succ(succ(zero)))");
  await query(session,"numeric.(1)","value","succ(succ(zero))");
  await query(session,"m","error");
  await query(session,"let saved := m.(1)","defined");
  await query(session,"typed(saved = numeric.(1), refl(saved))","error");
});
