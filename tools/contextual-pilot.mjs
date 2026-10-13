// Reproducible CB1 pilot measurements. Run alone, preferably with
// node --expose-gc tools/contextual-pilot.mjs. Each request has a fresh native
// handle, but the WASM module and JavaScript JIT stay warm in this process.
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {assertFreshBuild} from "./build-stamp.mjs";
import {sourceReader} from "./module-sources.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {contextualScenarios} from "../tests/fixtures/contextual-sessions.mjs";

assertFreshBuild();
const module=await create(),fixture=contextualScenarios.find(entry=>entry.id==="nested-function"),rows=[];
for(const collectScopes of [false,true]) {
  globalThis.gc?.();
  const memoryBefore=process.memoryUsage();
  const program=new CubicalProgram(module,sourceReader(),{collectScopes});
  try {
    const start=performance.now(),result=await program.check(fixture.source,"main");
    const checkMs=performance.now()-start;
    assert.deepEqual(result.gaps,[]);
    globalThis.gc?.();
    const memoryAfter=process.memoryUsage();
    const row={collectScopes,checkMs,memoryBefore,memoryAfter,kernelWork:program.kernel.work(),points:program.scopePoints.size};
    if(collectScopes) {
      row.scopeJsonBytes=Buffer.byteLength(JSON.stringify([...program.scopePoints.values()]));
      row.inputJsonBytes=Buffer.byteLength(JSON.stringify(program.scopeReplay.snapshot()));
      const point=[...program.scopePoints.values()].find(point=>point.origin.module==="main"
        &&point.origin.start===fixture.source.indexOf(fixture.marker)&&point.origin.end===fixture.source.indexOf(fixture.marker)+fixture.marker.length);
      row.runs=[];
      for(let repetition=0;repetition<3;repetition++) {
        const session=new ContextualSession(program,point.id),entries=[];
        for(const probe of fixture.sessions) {
          const [answer]=await session.run(probe.entry);
          assert.equal(answer.kind,probe.accepts===false?"error":probe.entry.startsWith("let ")?"defined":probe.type?"type":"value");
          if(probe.value??probe.type)assert.equal(answer.text,probe.value??probe.type);
          entries.push({source:probe.entry,kind:answer.kind,text:answer.text,costs:answer.costs});
        }
        assert.equal(session.accepted.length,1);
        assert.deepEqual(program.kernel.work(),row.kernelWork);
        row.runs.push(entries);session.dispose();
      }
    }
    rows.push(row);
  } finally {program.dispose();}
}
assert.deepEqual(rows[0].kernelWork,rows[1].kernelWork);
console.log(JSON.stringify({conditions:{node:process.version,gc:!!globalThis.gc,
  sessions:"fresh native handles, shared WASM instance and process; no explicit JIT warm-up",
  memory:"process totals before/after a check, including WASM memory; serialization and queries happen afterward"},rows},null,2));
