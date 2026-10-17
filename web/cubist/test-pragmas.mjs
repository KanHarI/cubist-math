// Parsed test metadata is inert syntax. Ordinary compilation rejects it;
// test hosts explicitly enable it and compare the resulting observations.
export const sourceTestCases=ast=>(ast.items??ast.declarations).filter(item=>item.testPragmas)
  .map(item=>({id:item.testPragmas.find(pragma=>pragma.pragma==="test").value,item}));

export function requireTestMode(ast,enabled) {
  const first=sourceTestCases(ast)[0];
  if(first&&!enabled)throw Object.assign(new Error("Test pragmas require explicit test mode."),
    {offset:first.item.testPragmas[0].start});
}

export function selectTestCases(cases,selected=null) {
  if(selected===null)return cases;
  if(!Array.isArray(selected)||!selected.length||new Set(selected).size!==selected.length)
    throw new TypeError("Test case selection must be a nonempty list of distinct IDs.");
  for(const id of selected)if(!cases.some(entry=>entry.id===id))throw new TypeError(`Unknown test case ${id}.`);
  return cases.filter(entry=>selected.includes(entry.id));
}

// The same observation serves source tests, checked comments and benchmark
// refusal accounting. It never changes checking or admits an expected failure.
export function observeTestCases(program,result) {
  const cases=[],ids=new Set(),failures=[],prerequisites=[],expectedErrors=[];
  for(const [module,ast] of program.sourceAsts)for(const entry of sourceTestCases(ast)) {
    if(ids.has(entry.id))throw new TypeError(`Duplicate test case ${entry.id}.`);
    ids.add(entry.id);
    cases.push({...entry,module,failures:[]});
  }
  const inTarget=(item,offset)=>Number.isInteger(offset)&&item.start<=offset&&offset<item.end;
  const symbols=Object.values(program.symbols);
  const owned=new Map(cases.map(entry=>{
    const {item,module}=entry,key=`${module}__${item.name?.text}`;
    const primary=symbols.find(symbol=>symbol.binding===key&&inTarget(item,symbol.start));
    const names=new Set(primary?[primary.name]:[]);
    if(primary)for(const group of program.publications.get(module)??[])
      if(group.owner===item.name.text)for(const name of group.members)names.add(name);
    return [entry,symbols.filter(symbol=>names.has(symbol.name)&&symbol.binding===`${module}__${symbol.name}`)];
  }));
  const describe=gap=>`${gap.module}${gap.name?`.${gap.name}`:""}: ${gap.code??"uncoded failure"}: ${gap.reason}`;
  const byCase=new Map(cases.map(entry=>[entry,[]]));
  for(const gap of result.gaps) {
    const symbol=program.symbols[`${gap.module}__${gap.name}`];
    const entry=cases.find(entry=>entry.module===gap.module&&(
      gap.duplicate?inTarget(entry.item,gap.declarationStart??gap.start)
      :owned.get(entry).some(output=>output.name===gap.name)||inTarget(entry.item,gap.start)));
    const observation={...gap,failure:gap.failure??symbol?.failure,blockedBy:gap.blockedBy??symbol?.blockedBy};
    if(!gap.name||["fuel","budget","deadline"].includes(observation.failure))prerequisites.push(describe(gap));
    else if(entry)byCase.get(entry).push(observation);
    else (gap.module===program.main?failures:prerequisites).push(describe(gap));
  }
  for(const entry of cases) {
    const {item,module}=entry,pragmas=item.testPragmas;
    const errors=byCase.get(entry),expected=pragmas.find(pragma=>pragma.pragma==="expect_error");
    if(expected) {
      if(errors.length!==1||errors[0].code!==expected.value||errors[0].blockedBy)
        entry.failures.push(`Expected one owned ${expected.value} refusal; observed ${errors.map(describe).join("; ")||"none"}.`);
      else expectedErrors.push(errors[0]);
    } else for(const error of errors)entry.failures.push(describe(error));
    const outputs=owned.get(entry);
    const observed=outputs.length||errors.length||result.directiveFuel.some(directive=>directive.module===module&&directive.start===item.start);
    if(!observed)entry.failures.push("The annotated target was not observed.");
    const axioms=pragmas.find(pragma=>pragma.pragma==="expect_axioms");
    if(axioms) {
      const resolved=[];
      for(const name of axioms.value) {
        const assumption=program.checker.libraryAssumptions.get(name);
        if(!assumption)entry.failures.push(`Unknown checked assumption ${name}.`);
        else resolved.push(assumption.name);
      }
      const wanted=[...new Set(resolved)].sort();
      for(const output of outputs.filter(output=>output.verified)) {
        const actual=[...new Set(output.axioms)].sort();
        if(JSON.stringify(actual)!==JSON.stringify(wanted))
          entry.failures.push(`${output.name}: expected assumptions [${axioms.value.join(", ")}], observed [${actual.map(name=>program.checker.assumptionLabels.get(name)??name).join(", ")}].`);
      }
    }
  }
  // The compiler reports warnings for the main source. An imported failure
  // remains a prerequisite failure; test expectations cannot hide it.
  for(const entry of cases) {
    const actual=entry.module===program.main?(result.warnings??[]).filter(warning=>inTarget(entry.item,warning.start)).map(warning=>warning.code).sort():[];
    const expected=entry.item.testPragmas.filter(pragma=>pragma.pragma==="expect_warning").map(pragma=>pragma.value).sort();
    if(JSON.stringify(actual)!==JSON.stringify(expected))entry.failures.push(`Expected warnings [${expected}], observed [${actual}].`);
  }
  for(const warning of result.warnings??[])
    if(!cases.some(entry=>entry.module===program.main&&inTarget(entry.item,warning.start)))failures.push(`${warning.code}: ${warning.message}`);
  return {cases:cases.map(({id,module,item,failures})=>({id,module,start:item.start,end:item.end,failures})),
    failures,prerequisites,expectedErrors};
}
