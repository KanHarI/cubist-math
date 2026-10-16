// Source-level assignment is shared by retained helper expansion and term
// elaboration. Public labels assign positions in one explicit telescope;
// neither caller reconstructs that telescope from destination names.
// What a call's arguments give, parameter by parameter: a written argument,
// a hole, an omitted parameter (before the last one given), or nothing more.
// A named argument gives the parameter it names: an implicit one in double
// braces, f{{A := Nat}}(x), an explicit one in parentheses. The others in
// double braces fill the implicit parameters no name gives, in order; those
// in parentheses fill the explicit parameters no name gives, in order, and
// then whatever the result takes.
export function assignArguments(n, parameters, unit, called) {
  const positional = [], named = new Map(), names = parameters?.map(parameter => parameter.name);
  const name = (arg, braced) => {
    const name = arg.name.text;
    if (!parameters)
      throw unit.locate(Error(`${called} has no named parameters: a named argument gives a parameter that a definition declares.`), arg.name);
    // A generated constructor may label an implicit parameter and an
    // explicit one alike: the braces say which is meant.
    const matching = parameters.findIndex(parameter => parameter.name === name && !!parameter.implicit === braced);
    const index = matching >= 0 ? matching : names.indexOf(name);
    if (index < 0)
      throw unit.locate(Error(`${called} has no parameter ${name}; its parameters are ${names.join(", ")}.`), arg.name);
    if (named.has(index)) throw unit.locate(Error(`The argument ${name} is given twice.`), arg.name);
    if (!!parameters[index].implicit !== braced)
      throw unit.locate(Error(braced ? `${name} is not an implicit parameter of ${called}: give it in parentheses, as ${called}(${name} := …).`
        : `${name} is an implicit parameter of ${called}: give it in double braces, as ${called}{{${name} := …}}(…).`), arg.name);
    named.set(index, arg.value);
  };
  for (const arg of n.args) {
    if (arg.kind === "namedArgument") name(arg, false);
    else positional.push(arg);
  }
  const braced = new Map();
  if (n.implicitArgs) {
    const implicit = parameters?.flatMap((parameter, index) => parameter.implicit ? [index] : []) ?? [];
    if (!implicit.length)
      throw unit.locate(Error(`${called} has no implicit parameters: give its arguments in parentheses, as ${called}(…).`), n.implicitArgs[0]);
    const unnamed = [];
    for (const arg of n.implicitArgs) {
      if (arg.kind === "namedArgument") name(arg, true);
      else unnamed.push(arg);
    }
    const open = implicit.filter(index => !named.has(index));
    if (unnamed.length > open.length)
      throw unit.locate(Error(`${called} has ${implicit.length} implicit parameter${implicit.length === 1 ? "" : "s"}, ${
        implicit.map(index => names[index]).join(", ")}; the double braces give ${n.implicitArgs.length}.`), unnamed[open.length]);
    unnamed.forEach((arg, k) => braced.set(open[k], arg));
  }
  const given = new Map(), count = parameters?.length ?? 0;
  let next = 0;
  for (let index = 0; index < count; index++) {
    if (named.has(index)) given.set(index, named.get(index));
    else if (braced.has(index)) given.set(index, braced.get(index));
    else if (!parameters[index].implicit && next < positional.length) given.set(index, positional[next++]);
  }
  for (let index = count; next < positional.length; index++) given.set(index, positional[next++]);
  const last = Math.max(-1, ...given.keys());
  return index => given.has(index) ? given.get(index) : index < last ? null : undefined;
}

