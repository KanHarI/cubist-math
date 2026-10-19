import { isResourceLimit } from "../resource-limits.mjs";
import {tokenize} from "./parser.mjs";
import {lint} from "./lint.mjs";

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
export function observeTestCases(program,result,{main=program.main}={}) {
  const cases=[],ids=new Set(),failures=[],prerequisites=[],expectedErrors=[];
  const dependencies=new Set();
  const include=module=>{
    if(dependencies.has(module))return;
    dependencies.add(module);
    for(const imported of program.sourceAsts.get(module)?.imports??[])include(imported);
  };
  include(main);
  for(const [module,ast] of program.sourceAsts)if(dependencies.has(module))for(const entry of sourceTestCases(ast)) {
    if(ids.has(entry.id))throw new TypeError(`Duplicate test case ${entry.id}.`);
    ids.add(entry.id);
    cases.push({...entry,module,failures:[]});
  }
  const inTarget=(item,offset)=>Number.isInteger(offset)&&item.start<=offset&&offset<item.end;
  const unannotated=[...program.sourceAsts].filter(([module])=>dependencies.has(module))
    .flatMap(([module,ast])=>(ast.items??ast.declarations).filter(item=>!item.testPragmas).map(item=>({module,item})));
  const entries=[...cases,...unannotated],bindingOwners=new Map(),members=new Map();
  for(const [module,groups] of program.publications)for(const group of groups)
    members.set(`${module}__${group.owner}`,group.members);
  const owned=new Map(entries.map(entry=>{
    const {item,module}=entry,key=`${module}__${item.name?.text}`;
    const candidate=program.symbols[key],primary=candidate&&inTarget(item,candidate.start)?candidate:null;
    const names=new Set(primary?[primary.name]:[]);
    if(primary)for(const name of members.get(key)??[])names.add(name);
    const outputs=[...names].map(name=>program.symbols[`${module}__${name}`]).filter(Boolean);
    for(const output of outputs)bindingOwners.set(output.binding,entry);
    return [entry,outputs];
  }));
  for(const entry of unannotated)if(program.sourceAsts.get(entry.module).declarations.includes(entry.item)&&!owned.get(entry).length)
    (entry.module===main?failures:prerequisites).push(`${entry.module}.${entry.item.name.text}: the declaration was not observed.`);
  const describe=gap=>`${gap.module}${gap.name?`.${gap.name}`:""}: ${gap.code??"uncoded failure"}: ${gap.reason}`;
  const byCase=new Map(cases.map(entry=>[entry,[]]));
  const resource=error=>{
    const seen=new Set();
    while(error) {
      if(isResourceLimit(error.failure))return true;
      if(!error.blockedBy||seen.has(error.blockedBy))return false;
      seen.add(error.blockedBy);error=program.symbols[error.blockedBy];
    }
    return false;
  };
  for(const gap of result.gaps.filter(gap=>dependencies.has(gap.module))) {
    // A duplicate has its own refusal but never owns the earlier symbol.
    const symbol=gap.duplicate?null:program.symbols[`${gap.module}__${gap.name}`];
    // Blame can point into retained source from a different declaration.
    // Only publication ownership and the declaring syntax locate the target.
    const entry=bindingOwners.get(symbol?.binding)
      ||entries.find(entry=>entry.module===gap.module&&inTarget(entry.item,gap.declarationStart??symbol?.start));
    const observation={...gap,failure:gap.failure??symbol?.failure,blockedBy:gap.blockedBy??symbol?.blockedBy};
    if(byCase.has(entry))byCase.get(entry).push(observation);
    if(gap.module!==main||!gap.name||resource(observation))prerequisites.push(describe(gap));
    else if(!byCase.has(entry))failures.push(describe(gap));
  }
  for(const entry of cases) {
    const {item,module}=entry,pragmas=item.testPragmas;
    const errors=byCase.get(entry),expected=pragmas.find(pragma=>pragma.pragma==="expect_error");
    if(errors.some(resource))continue;
    if(expected) {
      if(errors.length!==1||errors[0].code!==expected.value||errors[0].blockedBy)
        entry.failures.push(`Expected one owned ${expected.value} refusal; observed ${errors.map(describe).join("; ")||"none"}.`);
      else if(module===main)expectedErrors.push({...errors[0],caseId:entry.id});
    } else for(const error of errors)entry.failures.push(describe(error));
    const outputs=owned.get(entry);
    const observed=outputs.length||errors.length||result.directiveFuel.some(directive=>directive.module===module&&directive.start===item.start);
    if(!observed)entry.failures.push("The annotated target was not observed.");
    const anchor=pragmas.find(pragma=>pragma.pragma==="expect_error_at");
    if(anchor) {
      const tokens=tokenize(program.sources[module].slice(item.start,item.end)).slice(0,-1);
      const matches=tokens.flatMap((token,index)=>anchor.value.every((text,part)=>tokens[index+part]?.text===text)
        ?[{module,start:item.start+token.start,end:item.start+tokens[index+anchor.value.length-1].end}]:[]);
      if(matches.length!==1)entry.failures.push(`Expected one source anchor [${anchor.value.join(" ")}]; found ${matches.length}.`);
      else if(errors.length===1) {
        const [error]=errors,sites=[{module:error.module,start:error.start,end:error.end},error.diagnostic?.primary];
        if(sites.some(site=>site?.module!==module||site.start!==matches[0].start||site.end!==matches[0].end))
          entry.failures.push(`The refusal must cover exactly [${anchor.value.join(" ")}] in ${module}.`);
      }
    }
    const searches=pragmas.find(pragma=>pragma.pragma==="expect_searches");
    if(searches) {
      const actual=outputs.find(output=>output.name===item.name.text)?.searchFuel?.searches;
      if(actual!==searches.value)entry.failures.push(`Expected ${searches.value} charged searches; observed ${actual??"no counter"}.`);
    }
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
  const warnings=new Map([[main,main===program.main?result.warnings??[]:lint(program.sources[main],program.sourceAsts.get(main))]]);
  for(const {module} of cases)if(!warnings.has(module))
    warnings.set(module,lint(program.sources[module],program.sourceAsts.get(module)));
  for(const entry of cases) {
    if(byCase.get(entry).some(resource))continue;
    const actual=warnings.get(entry.module).filter(warning=>inTarget(entry.item,warning.start)).map(warning=>warning.code).sort();
    const expected=entry.item.testPragmas.filter(pragma=>pragma.pragma==="expect_warning").map(pragma=>pragma.value).sort();
    if(JSON.stringify(actual)!==JSON.stringify(expected))entry.failures.push(`Expected warnings [${expected}], observed [${actual}].`);
  }
  for(const [module,items] of warnings)for(const warning of items)
    if(!cases.some(entry=>entry.module===module&&inTarget(entry.item,warning.start)))
      (module===main?failures:prerequisites).push(`${module}: ${warning.code}: ${warning.message}`);
  for(const entry of cases)if(entry.module!==main)
    for(const failure of entry.failures)prerequisites.push(`${entry.id}: ${failure}`);
  return {cases:cases.map(({id,module,item,failures})=>({id,module,start:item.start,end:item.end,failures})),
    failures,prerequisites,expectedErrors:expectedErrors.filter(error=>!cases.find(entry=>entry.id===error.caseId).failures.length)};
}

export const testProblems=report=>report?[...report.prerequisites,...report.failures,
  ...report.cases.flatMap(entry=>entry.failures.map(message=>`${entry.id}: ${message}`))]:[];
