// Node hosts which need results, rather than a live inspector, share program
// ownership here. Observations are completed before disposing the kernel.
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceTestCases,observeTestCases} from "../web/cubist/test-pragmas.mjs";
import {sourceReader} from "./module-sources.mjs";

export async function checkedSource(source,name,{module=null,reader=sourceReader(),options={}}={}) {
  const program=new CubicalProgram(module??await createCubical(),reader,options);
  try {
    const result=await program.check(source,name);
    const contracts=[...program.sourceAsts.values()].some(ast=>sourceTestCases(ast).length)
      ?observeTestCases(program,result):null;
    return {result,contracts};
  } finally {program.dispose();}
}
