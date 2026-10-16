// Reproducible contextual measurements. Run alone, preferably with
// node --expose-gc tools/contextual-pilot.mjs [FIXTURE] [--artifacts]. Each request has a fresh native
// handle, but the WASM module and JavaScript JIT stay warm in this process.
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import {assertFreshBuild} from "./build-stamp.mjs";
import {sourceReader} from "./module-sources.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {contextualScenarios} from "../tests/fixtures/contextual-sessions.mjs";

assertFreshBuild();
const name=process.argv[2]??"nested-function",collectGeneration=process.argv.includes("--artifacts");
const fixtures=[...contextualScenarios,
  {id:"lazy-notation",source:`inductive Nat { zero; succ(n : Nat); }
    notation first { x + y := x; }
    notation outer { a * b := first.(a + b); }
    def f(p : Nat) : Nat := outer.(p * absent);`,marker:"x;",length:1,
    sessions:[{entry:"x",value:"p"},{entry:"let saved := x"},{entry:"typed(saved = x, refl(saved))"},{entry:"y",accepts:false}]},
  {id:"generated-helper",source:`theory T(U < UU0) { M : U; def get(x : M) : M := x; }
    theory Child(U < UU0) extends T {}`,marker:"x;",length:1,declaration:"Child.get",
    sessions:[{entry:"x",value:"x"},{entry:"let saved := x"},{entry:"typed(saved = x, refl(saved))"},{entry:"later_",accepts:false}]},
  {id:"theory-sections",source:await readFile(new URL("../cubist-tests/theory_sections.cubist",import.meta.url),"utf8"),
    marker:"exact one_mul(one);",scopePhase:"before",gaps:[["own_name","E568"],["own_implicit","E395"]],
    sessions:[{entry:"typed(square(one) = one, one_mul(one))"},{entry:"let saved := one"},
      {entry:"typed(saved = one, refl(saved))"},{entry:"typed(Unit, saved)",accepts:false}]},
];
const fixture=fixtures.find(entry=>entry.id===name),module=await create(),rows=[];
assert.ok(fixture?.sessions,`Unknown fixture: ${name}`);
for(const collectScopes of [false,true]) {
  globalThis.gc?.();
  const memoryBefore=process.memoryUsage();
  const program=new CubicalProgram(module,sourceReader(),{collectScopes,collectGeneration});
  try {
    const start=performance.now(),result=await program.check(fixture.source,"main");
    const checkMs=performance.now()-start;
    assert.deepEqual(result.gaps.map(({name,code})=>[name,code]),fixture.gaps??[]);
    globalThis.gc?.();
    const memoryAfter=process.memoryUsage();
    const row={collectScopes,collectGeneration,checkMs,memoryBefore,memoryAfter,kernelWork:program.kernel.work(),points:program.scopePoints.size};
    if(collectScopes) {
      row.availablePoints=[...program.scopePoints.values()].filter(point=>point.available).length;
      row.unavailableReasons={};
      for(const point of program.scopePoints.values())if(!point.available)
        row.unavailableReasons[point.reason]=(row.unavailableReasons[point.reason]??0)+1;
      // Report the deliberately unshared JSON size without constructing one
      // giant string. The UI transports only lightweight point metadata.
      row.scopeJsonBytes=2+Math.max(0,program.scopePoints.size-1);
      for(const point of program.scopePoints.values())row.scopeJsonBytes+=Buffer.byteLength(JSON.stringify(point));
      row.inputJsonBytes=Buffer.byteLength(JSON.stringify(program.scopeReplay.snapshot()));
      const points=[...program.scopePoints.values()].filter(point=>point.origin.module==="main"&&point.phase===(fixture.scopePhase??"expression")
        &&(!fixture.declaration||point.declaration===fixture.declaration)
        &&point.origin.start===fixture.source.indexOf(fixture.marker)
        &&point.origin.end===fixture.source.indexOf(fixture.marker)+(fixture.length??fixture.marker.length));
      assert.equal(points.length,1,"the measured scope must be unambiguous");
      const [point]=points;assert.ok(point.available,point.reason);
      row.runs=[];
      for(let repetition=0;repetition<3;repetition++) {
        const session=new ContextualSession(program,point.id),entries=[];
        for(const probe of fixture.sessions) {
          const [answer]=await session.run(probe.entry);
          assert.equal(answer.kind,probe.accepts===false?"error":probe.entry.startsWith("let ")?"defined":probe.type?"type":"value");
          if(probe.value??probe.type)assert.equal(answer.text,probe.value??probe.type);
          entries.push({source:probe.entry,kind:answer.kind,text:answer.text,costs:answer.costs});
        }
        assert.equal(session.accepted.length,fixture.sessions.filter(probe=>probe.entry.startsWith("let ")&&probe.accepts!==false).length);
        assert.deepEqual(program.kernel.work(),row.kernelWork);
        row.runs.push(entries);session.dispose();
      }
    }
    rows.push(row);
  } finally {program.dispose();}
}
assert.deepEqual(rows[0].kernelWork,rows[1].kernelWork);
console.log(JSON.stringify({fixture:name,conditions:{node:process.version,gc:!!globalThis.gc,
  sessions:"fresh native handles, shared WASM instance and process; no explicit JIT warm-up",
  memory:"process totals before/after a check, including WASM memory; serialization and queries happen afterward"},rows},null,2));
