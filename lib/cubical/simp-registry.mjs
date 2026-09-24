// Metadata about already checked equality proofs. Registrations never create
// a new kernel rule or an assumption; their terms are rechecked when used.
export function emptySimpRegistry() {
  return { defaults:new Map(), sets:new Map() };
}

export function copySimpRegistry(registry=emptySimpRegistry()) {
  return {defaults:new Map(registry.defaults),sets:new Map(registry.sets)};
}

export function mergeSimpRegistries(left,right=emptySimpRegistry()) {
  const merged=copySimpRegistry(left);
  for(const [key,rule] of right.defaults) {
    const existing=merged.defaults.get(key);
    if(!existing||rule.priority>existing.priority)merged.defaults.set(key,rule);
  }
  for(const [name,set] of right.sets) {
    const existing=merged.sets.get(name);
    if(!existing)merged.sets.set(name,set);
    else if(existing.origin!==set.origin)merged.sets.set(name,{
      ambiguous:true,origins:[...new Set([...(existing.origins??[existing.origin]),
        ...(set.origins??[set.origin])])].sort()});
  }
  return merged;
}

export function orderedDefaultRules(registry) {
  return [...registry.defaults.values()].sort((a,b)=>b.priority-a.priority||
    (a.identity<b.identity?-1:a.identity>b.identity?1:0));
}

export function resolveSimpSet(registry,name) {
  const set=registry.sets.get(name);
  if(!set)return null;
  if(set.ambiguous)throw Error(`Simplification set ${name} is ambiguous: ${set.origins.join(", ")}.`);
  return set.rules;
}

export function uniqueSimpRules(rules) {
  const seen=new Set();
  return rules.filter(rule=>{
    const identity=`${rule.identity}:${rule.reverse?"reverse":"forward"}`;
    if(seen.has(identity))return false;
    seen.add(identity);return true;
  });
}
