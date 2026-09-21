import {spawnSync} from "node:child_process";
import {writeFile} from "node:fs/promises";
import {fileURLToPath} from "node:url";
import {interval as I,face as F} from "./lattice.mjs";
const root=fileURLToPath(new URL("../../kernel/",import.meta.url));
const build=spawnSync("make",["-C",root,"all"],{encoding:"utf8"});if(build.status)throw Error(build.stderr);
const native=spawnSync(`${root}build/bench-lattice`,[],{encoding:"utf8"});if(native.status)throw Error(native.stderr);
const c=JSON.parse(native.stdout),iterations=c.iterations;
const i=I.variable("d0"),j=I.variable("d1"),k=I.variable("d2"),a=I.join(i,j),b=I.join(I.reverse(i),k);
let checksum=0;const start=process.cpuUsage();
for(let n=0;n<iterations;n++)checksum+=F.equalEndpoint(I.reverse(I.meet(a,b)),1).length;
const usage=process.cpuUsage(start),js={iterations,cpuMilliseconds:(usage.user+usage.system)/1000,peakRssBytes:process.resourceUsage().maxRSS*1024,checksum};
if(c.checksum!==js.checksum)throw Error("Benchmark implementations disagree.");
const report={scope:"Dimension-algebra microbenchmark only. Three algebra operations per iteration; no type checking, proof instructions or universe/HIT computation. Peak RSS includes each runtime. A single run is not a stable performance claim.",platform:process.platform,architecture:process.arch,node:process.version,native:c,javascript:js,
  mathematicalBenchmarks:["univalence transport","circle winding","group structure identity","F4 Galois correspondence","quotient group"].map(name=>({name,status:"not available: required cubical migration/computational rules incomplete"}))};
await writeFile(new URL("../../docs/cubical/benchmark-results.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
