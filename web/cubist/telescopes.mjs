// Ordinary declaration telescopes keep each written group's shared domain
// outside every binder in that group. Both scoping and lambda construction
// use these groups, including inferred declarations' parameter metadata.
export function parameterGroups(params) {
  const groups = [];
  for (let k = 0; k < params.length;) {
    const first = params[k++], parameters = [first];
    while (first.group !== undefined && k < params.length && params[k].group === first.group) parameters.push(params[k++]);
    groups.push({parameters, after: k, ...(first.bound ? {bound: first.bound} : {domain: first.type})});
  }
  return groups;
}

export function parameterLambdas(params, body) {
  for (const group of parameterGroups(params).reverse()) {
    const {parameters, bound, domain} = group;
    const binder = bound ? {bound} : {domain};
    body = parameters.length === 1
      ? {kind: "lambda", name: parameters[0].name, ...binder, body}
      : {kind: "binderGroup", binderKind: "lambda", names: parameters.map(p => p.name), ...binder, body};
  }
  return body;
}

// The parser's inferred-declaration form repeats its header as lambdas and
// metadata. Canonicalize before assigning identities, then rebuild both
// views from the same resolved parameter tokens at the adapter boundary.
export function declarationTelescope(declaration) {
  const params = declaration.valueParameters;
  if (!params?.length) return {tree: declaration, inferred: false};
  if (declaration.params?.length) throw new TypeError("A declaration has two parameter telescopes.");
  let value = declaration.value;
  for (const {parameters} of parameterGroups(params)) {
    const names = value?.kind === "lambda" ? [value.name] : value?.kind === "binderGroup" && value.binderKind === "lambda" ? value.names : [];
    if (names.length !== parameters.length || names.some((name, k) => name !== parameters[k].name))
      throw new TypeError("Inferred declaration metadata does not describe its parameter lambdas.");
    value = value.body;
  }
  return {tree: {...declaration, params, valueParameters: [], value}, inferred: true};
}
