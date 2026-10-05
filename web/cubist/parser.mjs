// A small mathematical proof language. Parsing never evaluates JavaScript.

// The operators a theory's notation can bind (theories.mjs).
export const notationOperators = ["+", "*", "<", "<="];

export function tokenize(source) {
  if (typeof source !== "string" || source.length > 1000000)
    throw new Error("Source exceeds 1 MB.");
  const tokens = [];
  const re =
    /\s+|\/\/[^\n]*|(?:<=|=>|->|:=|<-|\+\+)|0b[A-Za-z_0-9]*|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[\[\](){}:,;.+*<=>@&|-]|./gy;
  for (const match of source.matchAll(re)) {
    const text = match[0];
    if (/^\s|^\/\//.test(text)) continue;
    if (
      !/^(?:0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|<=|=>|->|:=|<-|\+\+|[\[\](){}:,;.+*<=>@&|-])$/.test(text)
    )
      throw Object.assign(new Error(`Unexpected character ${text}`), {
        offset: match.index,
      });
    tokens.push({ text, start: match.index, end: match.index + text.length });
    if (tokens.length > 160000) throw new Error("Source has too many tokens.");
  }
  tokens.push({ text: "EOF", start: source.length, end: source.length });
  return tokens;
}
// Reserved names: the language's keywords, which begin a declaration, a
// statement or a term, or join terms, and its built-in types Unit and Void,
// whose meaning checking relies on (a theory's laws, for one). None can be
// bound: not by a declaration, a parameter, a binder, a pattern, a field or
// a constructor. Every binding site reads its name through name(), which
// refuses them, as it does universe constants. A word that means something
// only inside one construct is a contextual keyword and stays a name
// elsewhere: the words of directives (computable, evaluate, expecting,
// print, typeof, inspect, simp_rule, simp_set), sort, law, notation and
// extends in a theory, set, prop, type and trunc in a header, and with, at,
// by, from, over, along, only, using and the like in particular statements.
// The library and the archive bind prop, set, law and evaluate.
export const reservedNames = new Set([
  "import", "def", "inductive", "theory", "section",
  "let", "obtain", "exact", "calc", "open", "match", "rfl", "rw", "simp", "simpa", "intro", "ext", "hlevel", "induction",
  "fun", "forall", "exists", "and", "or", "as", "return",
  "Unit", "Void",
]);

export function parse(source, typeOnly = false) {
  const ts = tokenize(source);
  let i = 0,
    depth = 0;
  const peek = () => ts[i].text;
  function take(text) {
    const t = ts[i];
    if (text && text !== t.text)
      throw Object.assign(new Error(`Expected '${text}', found '${t.text}'.`), {
        offset: t.start,
      });
    if (t.text !== "EOF") i++;
    return t;
  }
  // A binding gives a name its value with `:=`; `=` is the equality type.
  const binds = () => peek() === ":=";
  // Implicit parameters and arguments are in double braces, {{ … }}: two
  // braces with nothing between them, which no block or clause list starts
  // with. Inside them, }} closes the group.
  const doubleBrace = () => peek() === "{" && ts[i + 1].text === "{" && ts[i].end === ts[i + 1].start;
  const closeDoubleBrace = (first = take("}")) => {
    if (peek() !== "}" || ts[i].start !== first.end)
      throw Object.assign(new Error("Close double braces with }}, two braces together."), { offset: first.start });
    return { first, last: take("}") };
  };
  function define(form) {
    if (binds()) return take();
    throw Object.assign(new Error(`Write := to give a value: ${form}`), { offset: ts[i].start });
  }
  function name() {
    const t = take();
    if (t.text === "EOF" || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(t.text))
      throw Object.assign(new Error("Expected a name."), { offset: t.start });
    // U0, UU3 and the like name universes: they cannot be bound or declared.
    if (/^U+[0-9]+$/.test(t.text))
      throw Object.assign(new Error(`${t.text} is a universe constant; pick another name.`), { offset: t.start });
    if (reservedNames.has(t.text))
      throw Object.assign(new Error(`${t.text} is reserved, as a keyword or a built-in type of the language; pick another name.`), { offset: t.start });
    return t;
  }
  // A binder's type, or a universe binder's bound: `x : A` or `U < UU0`.
  function binderType(example) {
    if (peek() === "<") { take("<"); return { bound: expr() }; }
    if (peek() !== ":")
      throw Object.assign(new Error(`Expected ':' or '<', found '${peek()}', as in ${example}.`), { offset: ts[i].start });
    take(":");
    return { type: expr() };
  }
  // A parenthesized telescope of binder groups, `(n, m : Nat, U < UU0)`,
  // each name with its group. Universe binders only where `universes`.
  function parameters(example, universes) {
    take("(");
    const params = [];
    if (peek() !== ")") {
      while (true) {
        const names = sharedNames();
        const { type, bound } = binderType(example);
        if (bound && !universes)
          throw Object.assign(new Error("A constructor's arguments are terms; bind universes in the declaration's header."),
            { offset: names[0].start });
        const group = params.length;
        for (const p of names) params.push({ name: p, ...(bound ? { bound } : { type }), group });
        if (peek() !== ",") break;
        take(",");
      }
    }
    take(")");
    return params;
  }
  // The result position of an inductive header: an h-level modifier, a
  // universe, or a modifier and then a universe (`prop U`). The words type,
  // set, prop and trunc are keywords only here, as its first word.
  function sortResult() {
    let modifier = null;
    const word = peek(), start = ts[i].start;
    if (["type", "set", "prop"].includes(word)) {
      const token = take();
      modifier = { kind: word, start: token.start, end: token.end };
    } else if (word === "trunc" && ts[i + 1].text === "(") {
      const token = take();
      take("(");
      const negative = peek() === "-";
      if (negative) take();
      const number = take();
      if (!/^[0-9]+$/.test(number.text))
        throw Object.assign(new Error("trunc takes an integer level n ≥ -1, as in trunc(1)."), { offset: number.start });
      const level = (negative ? -1 : 1) * Number(number.text);
      if (level < -1)
        throw Object.assign(new Error("trunc(n) needs n ≥ -1: prop is trunc(-1), set is trunc(0)."), { offset: number.start });
      modifier = { kind: "trunc", level, start: token.start, end: take(")").end };
    }
    const universe = peek() === "{" ? null : expr();
    if (!modifier && !universe)
      throw Object.assign(new Error("After ':' give an h-level, a universe or both, as in : prop U."), { offset: start });
    return { modifier, universe, start };
  }
  // Names that share a type are separated by commas: (n, m : Nat).
  function sharedNames(example = "(n, m : Nat)") {
    const names = [name()];
    while (peek() === ",") { take(","); names.push(name()); }
    if (/^[A-Za-z_]/.test(peek()) && peek() !== "EOF")
      throw Object.assign(new Error(`Separate names with commas: ${example}`), { offset: ts[i].start });
    return names;
  }
  // p ++ q concatenates paths, left to right as calc chains do; it binds
  // looser than arithmetic and tighter than =. Coordinates combine tighter
  // than @: i & j is their meet (minimum), i | j their join (maximum), and
  // prefix -i reverses one, so p @ -i & j | k is p @ (((-i) & j) | k). Prefix
  // -p reverses a path, tighter still: -p @ i is (-p) @ i.
  const prec = {
    "->": 1,
    or: 2,
    and: 3,
    "=": 4,
    "<": 4,
    "<=": 4,
    "++": 5,
    "+": 6,
    "*": 7,
    "@": 8,
    "|": 9,
    "&": 10,
  };
  const PREFIX = 11;
  // Tuples are notation for right-associated binary dependent pairs. Preserve
  // the delimiter locations for macro inspection; elaboration sees only pairs.
  function tuple(open, first, item) {
    const items = [first];
    while (peek() === ",") { take(","); items.push(item()); }
    const close = take(")");
    if (items.length === 1) return { ...first, start: open.start, end: close.end };
    if (items.length === 2)
      return { kind: "pair", left: items[0], right: items[1], start: open.start, end: close.end };
    if (depth + items.length > 128)
      throw Object.assign(new Error("Expanded tuple nesting exceeds 128."), { offset: open.start });
    let result = items.at(-1);
    for (let j = items.length - 2; j >= 0; j--)
      result = { kind: "pair", left: items[j], right: result,
        start: items[j].start, end: result.end, syntheticTuplePair: j !== 0 };
    return { ...result, start: open.start, end: close.end,
      tupleStart: open.start, tupleEnd: close.start };
  }
  function expr(min = 0) {
    if (++depth > 128)
      throw Object.assign(new Error("Expression nesting exceeds 128."), {
        offset: ts[i].start,
      });
    let a = prefix(take());
    // An argument, or a named one, `x := e`, which gives the parameter x.
    const argument = () => {
      if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(peek()) || ts[i + 1]?.text !== ":=") return expr();
      const parameter = name();
      take(":=");
      const value = expr();
      return { kind: "namedArgument", name: parameter, value, start: parameter.start, end: value.end };
    };
    // A call's arguments in parentheses, and where they end.
    const callArguments = () => {
      take("(");
      const args = [];
      if (peek() !== ")") {
        args.push(argument());
        while (peek() === ",") {
          take(",");
          args.push(argument());
        }
      }
      return { args, end: take(")").end };
    };
    while (true) {
      if (peek() === "(") {
        const { args, end } = callArguments();
        a = { kind: "call", fn: a, args, start: a.start, end };
        continue;
      }
      // Implicit arguments, f{{U0, Nat}}(x) or f{{A := Nat}}(x) (L4.1b): a
      // double brace group after a name, then the call's own arguments, if
      // any.
      if (a.kind === "name" && doubleBrace()) {
        const open = take("{"), inner = take("{"), implicitArgs = [argument()];
        while (peek() === ",") {
          take(",");
          implicitArgs.push(argument());
        }
        const { first, last } = closeDoubleBrace();
        const { args, end } = peek() === "(" ? callArguments() : { args: [], end: last.end };
        a = { kind: "call", fn: a, args, implicitArgs,
          implicitGroup: { opens: [open.start, inner.start], closes: [first.end, last.end], start: open.start, end: last.end },
          start: a.start, end };
        continue;
      }
      // A qualified name, T.squash, is tight too: a name, a dot and a name.
      if (a.kind === "name" && peek() === "." && ts[i - 1].end === ts[i].start
          && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text) && ts[i + 1].start === ts[i].end) {
        const dot = take(".");
        const member = take();
        // Every dot of a longer one, m.group.monoid, is tight.
        a = { kind: "name", name: `${a.name}.${member.text}`, qualifiedDot: { start: dot.start, end: dot.end },
          ...(a.qualifiedDot ? { qualifiedDots: [...(a.qualifiedDots ?? [a.qualifiedDot]), { start: dot.start, end: dot.end }] } : {}),
          start: a.start, end: member.end };
        continue;
      }
      // A field of any other value, f(x).map, is tight too: a model's field
      // (L2.4), which the translator reads from the value's type.
      if (peek() === "." && ts[i - 1].end === ts[i].start
          && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text) && ts[i + 1].start === ts[i].end) {
        const dot = take("."), member = take();
        a = { kind: "member", value: a, field: member, dot: { start: dot.start, end: dot.end }, start: a.start, end: member.end };
        continue;
      }
      // A projection p.1 or p.2 is tight: no space on either side of the dot.
      // A quantifier's dot is followed by a space, so it never reads as one.
      if (peek() === "." && ts[i - 1].end === ts[i].start && /^[0-9]+$/.test(ts[i + 1].text)
          && ts[i + 1].start === ts[i].end) {
        const dot = take("."), digit = take();
        if (digit.text !== "1" && digit.text !== "2")
          throw Object.assign(new Error("A pair has only the projections .1 and .2. A tuple nests pairs to the right: the third component of (a, b, c) is .2.2."), { offset: digit.start });
        a = { kind: "projection", value: a, index: Number(digit.text),
          dot: { start: dot.start, end: dot.end }, digit: { start: digit.start, end: digit.end },
          start: a.start, end: digit.end };
        continue;
      }
      const p = prec[peek()];
      if (p === undefined || p < min) break;
      const operatorToken = take(), operator = operatorToken.text;
      let carrier;
      if (operator === "=" && peek() === "[") {
        take("["); carrier = expr(); take("]");
      }
      const right = expr(p + (["->", "and", "or"].includes(operator) ? 0 : 1));
      a = {
        kind: operator === "@" ? "pathApply" : "binary",
        operator,
        operatorStart: operatorToken.start,
        operatorEnd: operatorToken.end,
        left: a,
        right,
        ...(carrier ? { carrier } : {}),
        start: a.start,
        end: right.end,
      };
    }
    depth--;
    return a;
  }
  // The expression a token starts: a keyword form, a negation, a tuple, a
  // literal or a name.
  function prefix(t) {
    if (t.text === "with") return unfoldingExpr(t);
    if (t.text === "induction") return inductionExpr(t);
    if (t.text === "match") return matchExpr(t);
    if (t.text === "unpack" && peek() !== "(") return unpackExpr(t);
    if (t.text === "path" && /^[A-Za-z_][A-Za-z_0-9]*$/.test(peek()) && ts[i + 1]?.text === "=>") {
      const dimension = name();
      take("=>");
      const body = expr();
      return { kind: "pathLambda", dimension, body, start: t.start, end: body.end };
    }
    if (t.text === "along") {
      const family = expr();
      take("by");
      const path = expr();
      take("from");
      const value = expr();
      return { kind:"along", family, path, value, start:t.start, end:value.end };
    }
    if (t.text === "fun") return lambdaExpr(t);
    if (t.text === "forall" || t.text === "exists") return quantifierExpr(t);
    if (t.text === "-") {
      const operand = expr(PREFIX);
      return { kind: "unary", operator: "-", operand, operatorStart: t.start, operatorEnd: t.end,
        start: t.start, end: operand.end };
    }
    if (t.text === "(") return tuple(t, expr(), () => expr());
    if (/^0b[01]+$/.test(t.text)) {
      const digits = t.text.slice(2).replace(/^0+(?=.)/, "");
      if (digits.length > 256)
        throw Object.assign(new Error("Binary literals are limited to 256 significant bits."), { offset: t.start });
      return { kind: "binaryNumber", digits, spelling: t.text, start: t.start, end: t.end };
    }
    if (/^[0-9]+$/.test(t.text)) {
      if (Number(t.text) > 256)
        throw Object.assign(
          new Error("Numerals are limited to 256 in this version."),
          { offset: t.start },
        );
      return { kind: "number", value: Number(t.text), start: t.start, end: t.end };
    }
    if (/^[A-Za-z_][A-Za-z_0-9]*$/.test(t.text) && t.text !== "EOF")
      return { kind: "name", name: t.text, start: t.start, end: t.end };
    throw Object.assign(
      new Error(`Expected an expression, found '${t.text}'.`),
      { offset: t.start },
    );
  }
  // with unfolding [names] { e }.
  function unfoldingExpr(t) {
    take("unfolding");
    take("[");
    const hints = [];
    if (peek() !== "]") {
      hints.push(name());
      while (peek() === ",") { take(","); hints.push(name()); }
    }
    take("]");
    take("{");
    const body = expr();
    const end = take("}").end;
    return { kind: "withUnfolding", hints, body, start: t.start, end };
  }
  // `induction v [as z] [return T] { c(xs, hs) @ i => body; … }`: a clause
  // per constructor, as in match, whose names are the constructor's
  // arguments and then, optionally, an induction hypothesis for each
  // recursive argument. Natural numbers keep their own form,
  // `induction n [as k] return C { zero => …; succ h => …; }`, where as names
  // the value in the motive and the predecessor in the successor clause, and
  // h is the hypothesis.
  function inductionExpr(t) {
    const value = expr();
    let motiveName = null, type = null;
    if (peek() === "as") { take("as"); motiveName = name(); }
    if (peek() === "return") { take("return"); type = expr(); }
    else if (motiveName) throw Object.assign(new Error("Give the motive after as: induction v as z return T { … }."), { offset: ts[i].start });
    take("{");
    const clauses = [];
    while (peek() !== "}") {
      if (peek() === "EOF") throw Object.assign(new Error("Expected '}' to close the induction."), { offset: ts[i].start });
      const head = clauseHead();
      const body = expr();
      const end = take(";").end;
      clauses.push({ kind: "clause", ...head, body, start: head.constructor.start, end });
    }
    const end = take("}").end;
    const [zero, succ] = clauses;
    if (type && clauses.length === 2 && zero.constructor.text === "zero" && !zero.args && !zero.binders.length && !zero.coordinates.length
        && succ.constructor.text === "succ" && !succ.args && succ.binders.length === 1 && !succ.coordinates.length) {
      const a = { kind: "induction", value, index: motiveName, type, base: zero.body, hypothesis: succ.binders[0], step: succ.body, start: t.start, end };
      Object.defineProperty(a, "clauses", { value: clauses, enumerable: false });
      return a;
    }
    return { kind: "induction", motiveName, value, type, clauses, start: t.start, end };
  }
  // `match v [as z] [return T] { c(xs) @ i => body; … }`: a clause per
  // constructor, its arguments in parentheses, then its dimensions. The
  // legacy match on a sum, `left x => …; right y => …;`, keeps its fields.
  function matchExpr(t) {
    const value = expr(), values = [value];
    while (peek() === ",") { take(","); values.push(expr()); }
    let motiveName = null, type = null;
    if (peek() === "as") { take("as"); motiveName = name(); }
    if (peek() === "return") { take("return"); type = expr(); }
    else if (motiveName) throw Object.assign(new Error("Give the motive after as: match v as z return T { … }."), { offset: ts[i].start });
    take("{");
    const clauses = [];
    while (peek() !== "}") {
      if (peek() === "EOF") throw Object.assign(new Error("Expected '}' to close the match."), { offset: ts[i].start });
      const head = clauseHead();
      const body = expr();
      const end = take(";").end;
      clauses.push({ kind: "clause", ...head, body, start: head.constructor.start, end });
    }
    const end = take("}").end;
    const obligations = matchObligations(true);
    if (values.length > 1 && motiveName)
      throw Object.assign(new Error("A match on several values takes its motive from return T or the type expected of it, without as."), { offset: t.start });
    const a = { kind: "match", motiveName, value, ...(values.length > 1 ? { values } : {}), type, start: t.start, end, ...obligations };
    // The legacy shape keeps its fields; its clauses stay readable but are
    // not enumerated, so a walk over the tree meets each body once.
    if (!obligations.obligationsToken && clauses.length === 2 && clauses[0].constructor.text === "left" && clauses[1].constructor.text === "right"
        && clauses.every(clause => !clause.args && clause.binders.length === 1 && !clause.coordinates.length)) {
      Object.assign(a, { left: clauses[0].binders[0], leftBody: clauses[0].body,
        right: clauses[1].binders[0], rightBody: clauses[1].body });
      Object.defineProperty(a, "clauses", { value: clauses, enumerable: false });
    } else a.clauses = clauses;
    return a;
  }
  // unpack v as (x, y) return T { body; }.
  function unpackExpr(t) {
    const value = expr();
    take("as");
    take("(");
    const left = name();
    take(",");
    const right = name();
    take(")");
    take("return");
    const type = expr();
    take("{");
    const body = expr();
    take(";");
    const end = take("}").end;
    return {
      kind: "unpack",
      value,
      type,
      left,
      right,
      body,
      start: t.start,
      end,
    };
  }
  // fun x => body, or fun with binder groups.
  function lambdaExpr(t) {
    const binders = [];
    // Binder groups are one comma-separated list, like parameters:
    // fun (x, y : A, b : B) => body.
    if (peek() === "(") {
      take("(");
      while (true) {
        const names = sharedNames();
        const { type: domain, bound } = binderType("fun (U < UU0, A : U) => …");
        binders.push({ names, domain, bound });
        if (peek() !== ",") break;
        take(",");
      }
      take(")");
      if (peek() === "(")
        throw Object.assign(new Error("Separate binder groups with commas: fun (a : A, b : B) => …"), { offset: ts[i].start });
    }
    if (!binders.length) binders.push({ names: [name()], domain: null });
    take("=>");
    let a = expr();
    for (let index=binders.length-1;index>=0;index--) {
      const binder=binders[index];
      a = {
        kind: binder.names.length === 1 ? "lambda" : "binderGroup",
        ...(binder.names.length === 1 ? {name:binder.names[0]} : {names:binder.names}),
        binderKind:"lambda",domain: binder.domain, ...(binder.bound ? { bound: binder.bound } : {}),
        body:a, start:t.start, end:a.end,
        // Only the outer expression owns the single source `fun` token.
        ...(index ? {generatedBinder:true} : {keyword:{start:t.start,end:t.end}}),
      };
    }
    return a;
  }
  // forall or exists, over one binder group.
  function quantifierExpr(t) {
    const names = sharedNames(`${t.text} n, m : Nat. P(n, m)`);
    const { type: domain, bound } = binderType(`${t.text} n : Nat. P(n)`);
    if (bound && t.text === "exists")
      throw Object.assign(new Error("Only forall and fun bind a universe variable: exists has no level form."), { offset: t.start });
    // `.` ends the type: forall n : Nat. P(n). A space follows it, so a
    // tight x.y stays free for projections.
    if (peek() !== ".")
      throw Object.assign(new Error(`End ${t.text}'s type with a dot: ${t.text} n : Nat. P(n)`), { offset: ts[i].start });
    const dot = take(".");
    if (!/\s/.test(source[dot.end] ?? " "))
      throw Object.assign(new Error(`Write a space after the . that ends ${t.text}'s type: ${t.text} n : Nat. P(n)`), { offset: dot.start });
    const body = expr();
    return {
      kind: names.length === 1 ? t.text : "binderGroup",
      ...(names.length === 1 ? {name:names[0]} : {names}),
      binderKind:t.text, domain, ...(bound ? { bound } : {}), body, start:t.start, end:body.end,
      keyword:{start:t.start,end:t.end},
    };
  }
  function pattern() {
    if (++depth > 128)
      throw Object.assign(new Error("Pattern nesting exceeds 128."), {
        offset: ts[i].start,
      });
    let p;
    if (peek() === "(") {
      const t = take("("), left = pattern();
      if (peek() !== ",")
        throw Object.assign(new Error("A pair pattern needs at least two components."), { offset: t.start });
      p = tuple(t, left, pattern);
    } else {
      const t = name();
      p = { kind: "name", name: t.text, start: t.start, end: t.end };
    }
    depth--;
    return p;
  }
  // A match clause's head, `c(xs) @ i =>`: its constructor, which a generated
  // one may name with its type, T.squash; its arguments in parentheses; then
  // its dimensions.
  // A clause's head: one pattern for each value matched, separated by
  // commas, then =>. The first pattern's fields are the clause's own, as
  // they were before several values could be matched; the others are
  // `more`. A pattern is a constructor, with its arguments in parentheses,
  // each a name or a pattern itself, and a path constructor's coordinates
  // after @; a bare name is a constructor without arguments, a variable or
  // _, which the elaborator tells apart by the matched type.
  function clauseHead() {
    const first = clausePattern(false), more = [];
    while (peek() === ",") { take(","); more.push(clausePattern(false)); }
    take("=>");
    return { ...first, ...(more.length ? { more } : {}) };
  }
  function clausePattern(nested) {
    let constructor = name(), qualifiedDot = null;
    if (peek() === "." && ts[i - 1].end === ts[i].start && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text)
        && ts[i + 1].start === ts[i].end) {
      const dot = take("."), member = take();
      qualifiedDot = { start: dot.start, end: dot.end };
      constructor = { text: `${constructor.text}.${member.text}`, start: constructor.start, end: member.end };
    }
    let args = null;
    // An argument: a name, or a constructor pattern with its own arguments.
    const argument = () => /^[A-Za-z_][A-Za-z_0-9]*$/.test(peek()) && (ts[i + 1]?.text === "("
      || ts[i + 1]?.text === "." && ts[i + 1].start === ts[i].end) ? clausePattern(true) : name();
    if (peek() === "(") {
      take("(");
      args = [];
      if (peek() !== ")") {
        args.push(argument());
        while (peek() === ",") { take(","); args.push(argument()); }
      }
      take(")");
    }
    // A bare name binds a sum's side in the legacy clause, left x =>. A path
    // constructor's coordinates follow @, as in the point the clause covers:
    // loop @ i =>.
    const binders = [], coordinates = [];
    if (!nested) while (peek() !== "=>" && peek() !== "@" && peek() !== ",") binders.push(name());
    while (peek() === "@") { take("@"); coordinates.push(name()); }
    return { ...(nested ? { kind: "pattern", start: constructor.start, end: ts[i - 1].end } : {}),
      constructor, args, binders, coordinates, ...(qualifiedDot ? { qualifiedDot } : {}) };
  }

  function matchObligations(expression) {
    if (peek() !== "obligations") return {};
    const obligationsToken = take("obligations");
    if (peek() === "by") {
      take("by");
      let obligationProof;
      if (peek() === "{") obligationProof = {kind:"block",body:block()};
      else if (peek() === "hlevel" || peek() === "rfl") {
        const tactic = take(), hints = [];
        if (tactic.text === "hlevel" && peek() === "with") {
          take("with"); take("[");
          if (peek() !== "]") { hints.push(expr()); while (peek() === ",") { take(","); hints.push(expr()); } }
          take("]");
        }
        const statement = {kind:tactic.text,hints,start:tactic.start,end:ts[i - 1].end,keyword:tactic};
        obligationProof = {kind:"tactic",body:[statement]};
      } else {
        if (peek() === "simp" || peek() === "simpa")
          throw Object.assign(Error("obligations by supports hlevel (with optional hints), rfl, a proof block, or a whole clause term; put simp or simpa inside a proof block."), {offset:ts[i].start});
        obligationProof = {kind:"term",value:expr()};
      }
      if (!expression && peek() === ";") take(";");
      return {obligationsToken,obligationProof,end:ts[i - 1].end};
    }
    take("{");
    const obligations = [];
    while (peek() !== "}") {
      if (peek() === "EOF") throw Object.assign(Error("Expected '}' to close obligations."), {offset:ts[i].start});
      const head = clauseHead();
      const body = expression ? expr() : block();
      if (expression) take(";");
      obligations.push({kind:"clause",...head,body,obligation:true,start:head.constructor.start,end:ts[i - 1].end});
    }
    const end = take("}").end;
    return {obligationsToken,obligations,end};
  }

  function block() {
    if (++depth > 128)
      throw Object.assign(new Error("Block nesting exceeds 128."), {
        offset: ts[i].start,
      });
    take("{");
    const statements = [];
    while (peek() !== "}") {
      const t = take();
      const parsed = [statement(t)].flat();
      // A statement's leading token is its keyword, a source link site.
      for (const parsedStatement of parsed) parsedStatement.keyword = { start: t.start, end: t.end };
      statements.push(...parsed);
    }
    take("}");
    depth--;
    return statements;
  }
  // The rules of rw or simp, inside their brackets: [p, <- q].
  function rewriteRules() {
    const rules = [];
    if (peek() !== "]") while (true) {
      const reverse = peek() === "<-";
      const reverseToken = reverse ? take("<-") : null;
      const value = expr();
      rules.push({ value, reverse, start: reverseToken?.start ?? value.start, end: value.end });
      if (peek() !== ",") break;
      take(",");
    }
    return rules;
  }
  // A bracketed list of names, after its keyword: without [a, b], with [h].
  function nameList(keyword) {
    take(keyword); take("[");
    const names = [];
    if (peek() !== "]") while (true) {
      names.push(name());
      if (peek() !== ",") break;
      take(",");
    }
    take("]");
    return names;
  }
  // One proof statement, from its keyword t; intro m, n; is one per name.
  function statement(t) {
    if (t.text === "intro") {
      // intro m, n; takes several inputs, named in order.
      const names = [name()];
      while (peek() === ",") { take(","); names.push(name()); }
      if (/^[A-Za-z_]/.test(peek()) && peek() !== "EOF")
        throw Object.assign(new Error("Separate names with commas: intro m, n;"), { offset: ts[i].start });
      const end = take(";");
      return names.map(n => ({ kind: "intro", name: n, start: t.start, end: end.end }));
    }
    if (t.text === "let" || t.text === "obtain") return letStatement(t);
    // `open m;` puts a model's fields and notation in scope for the rest of
    // the block (L2.4).
    if (t.text === "open") {
      const model = expr(), end = take(";");
      return { kind: "open", model, start: t.start, end: end.end };
    }
    if (t.text === "have")
      throw Object.assign(new Error("have was removed: write let name : T := term; or prove the claim in a block, let name : T { … }."),
        { offset: t.start });
    if (t.text === "show")
      throw Object.assign(new Error("show was removed: prove the restated goal in a block, let h : T { … }, then exact h;."),
        { offset: t.start });
    if (t.text === "suffices")
      throw Object.assign(new Error("suffices was removed: prove the claim first, let h : T { … }, then prove the goal from h."),
        { offset: t.start });
    if (t.text === "rfl") {
      const end = take(";");
      return { kind: "rfl", start: t.start, end: end.end };
    }
    if (t.text === "ext") {
      const variable = name(), end = take(";");
      return { kind: "ext", variable, start: t.start, end: end.end };
    }
    if (t.text === "over") {
      const family=expr();
      take("along");
      const path=expr();
      take("by");
      const body=block();
      return {kind:"over",family,path,body,start:t.start,end:ts[i-1].end};
    }
    if (t.text === "calc") return calcStatement(t);
    if (t.text === "rw") return rwStatement(t);
    if (t.text === "simp" || t.text === "simpa") return simpStatement(t);
    if (t.text === "hlevel") {
      const hints = [];
      if (peek() === "with") {
        take("with"); take("[");
        if (peek() !== "]") while (true) {
          hints.push(expr());
          if (peek() !== ",") break;
          take(",");
        }
        take("]");
      }
      const end = take(";");
      return { kind: "hlevel", hints, start: t.start, end: end.end };
    }
    if (t.text === "exact") {
      const value = expr(),
        e = take(";");
      return { kind: "exact", value, start: t.start, end: e.end };
    }
    if (t.text === "match") return matchStatement(t);
    if (t.text === "induction") return matchStatement(t, true);
    if (t.text === "cases")
      throw Object.assign(new Error("cases was removed: write match value { left(a) => { … } right(b) => { … } }."),
        { offset: t.start });
    throw Object.assign(
      new Error(
        `Expected a proof statement; found '${t.text}'.`,
      ),
      { offset: t.start },
    );
  }
  // let name := term; let name : T := term; let name : T { … }; and
  // obtain (a, b) := pair;.
  function letStatement(t) {
    const target = pattern();
    if (t.text === "let" && target.kind !== "name")
      throw Object.assign(new Error("Use obtain to unpack a pair."), {
        offset: target.start,
      });
    if (t.text === "let" && peek() === ":") {
      // let name : T := term; states the name's type, and
      // let name : T { … } proves T in a nested block.
      take(":");
      const type = expr();
      if (binds()) {
        take();
        const value = expr(), end = take(";");
        return { kind: "let", target, type, value, start: t.start, end: end.end };
      }
      const body = block();
      return { kind: "let", target, type, body, start: t.start, end: ts[i - 1].end };
    }
    define(t.text === "let" ? "let name := term;" : "obtain (a, b) := pair;");
    const value = expr();
    const e = take(";");
    return { kind: t.text, target, value, start: t.start, end: e.end };
  }
  // calc { a = b by proof; … }.
  function calcStatement(t) {
    take("{");
    const steps = [];
    while (peek() !== "}") {
      const left = expr(5);
      take("=");
      const right = expr();
      // The `by` keyword is the source site of this step's checked path.
      const by = take("by");
      const proof = peek() === "{" ? { kind: "block", body: block() } : { kind: "term", value: expr() };
      if (proof.kind === "term") take(";");
      steps.push({ left, right, proof, by: { start: by.start, end: by.end },
        start: left.start, end: ts[i - 1].end });
    }
    const end = take("}");
    return { kind: "calc", steps, start: t.start, end: end.end };
  }
  // rw [rules] [at lhs|rhs] [occurrence n];
  function rwStatement(t) {
    take("[");
    const rules = rewriteRules();
    take("]");
    if (!rules.length) throw Object.assign(new Error("rw requires a path."), { offset: t.start });
    let target = null, occurrence = 1;
    if (peek() === "at") {
      take("at");
      target = take().text;
      if (!["lhs", "rhs"].includes(target))
        throw Object.assign(new Error("rw target must be lhs or rhs."), { offset: ts[i - 1].start });
    }
    if (peek() === "occurrence") {
      take("occurrence");
      const count = take();
      occurrence = Number(count.text);
      if (!Number.isSafeInteger(occurrence) || occurrence < 1)
        throw Object.assign(new Error("rw occurrence must be a positive integer."), { offset: count.start });
    }
    const end = take(";");
    return { kind: "rw", rules, target, occurrence, start: t.start, end: end.end };
  }
  // simp [only] [rules] [without [names]] [with [names]] [at h as h'];
  // and simpa …, ending using term.
  function simpStatement(t) {
    const only=peek()==="only";
    if(only)take("only");
    let rules = [];
    if(peek()==="[") {
      take("[");
      rules = rewriteRules();
      take("]");
    } else if(only) {
      throw Object.assign(new Error("simp only requires an explicit rule list."),{offset:ts[i].start});
    }
    let without=[];
    if(peek()==="without") {
      if(only)throw Object.assign(new Error("simp only cannot exclude rules."),{offset:ts[i].start});
      without=nameList("without");
    }
    const witnesses=peek()==="with"?nameList("with"):[];
    let at=null,as=null;
    if(t.text==="simp"&&peek()==="at") {
      take("at");at=name();take("as");as=name();
    }
    const using = t.text === "simpa" ? (take("using"),expr()) : null;
    const end = take(";");
    return {kind:t.text === "simpa" ? "simpaOnly" : "simpOnly", rules, only,without,witnesses,
      ...(at?{at,as}:{}),
      ...(using?{using}:{}), start:t.start, end:end.end};
  }
  // The closing statement `match v { c(xs) @ i => { … } … }` (work plan
  // L2.2a): a clause per constructor, each a proof block of the goal at
  // that constructor. Its motive comes from the goal. The induction
  // statement is the same, and its clauses may also name the induction
  // hypotheses: `induction v { c(xs, hs) => { … } … }`.
  function matchStatement(t, induction = false) {
    const keyword = induction ? "induction" : "match";
    const value = expr(), values = [value];
    if (peek() === "," && induction)
      throw Object.assign(new Error("The induction statement takes apart one value; take the first, then the next inside each clause."),
        { offset: ts[i].start });
    while (peek() === ",") { take(","); values.push(expr()); }
    if (peek() === "as" || peek() === "return")
      throw Object.assign(new Error(`The ${keyword} statement takes its motive from the goal: write ${keyword} v { c(xs) => { … } … } without as or return.`),
        { offset: ts[i].start });
    take("{");
    const clauses = [];
    while (peek() !== "}") {
      if (peek() === "EOF") throw Object.assign(new Error(`Expected '}' to close the ${keyword}.`), { offset: ts[i].start });
      const head = clauseHead();
      if (peek() !== "{")
        throw Object.assign(new Error(`A clause of the ${keyword} statement is a proof block: c(xs) => { … }.`), { offset: ts[i].start });
      const body = block();
      clauses.push({ kind: "clause", ...head, body, start: head.constructor.start, end: ts[i - 1].end });
    }
    const e = take("}");
    return { kind: "matchStatement", ...(induction ? { induction: true } : {}), value, ...(values.length > 1 ? { values } : {}), clauses, start: t.start, end: e.end, ...matchObligations(false) };
  }
  if (typeOnly) {
    const result = expr();
    take("EOF");
    return result;
  }
  const declarations = [],items=[],directives=[];
  let module = null;
  const imports = [];
  while (peek() === "import") {
    take("import");
    const imported = name().text;
    module ??= imported;
    imports.push(imported);
    take(";");
  }
  while (peek() !== "EOF") {
    let t = take();
    if(t.text==="simp_rule") {
      const rule=name();
      let priority=0;
      if(peek()==="priority") {
        take("priority");
        const number=take();
        priority=Number(number.text);
        if(!Number.isSafeInteger(priority)||priority<0||priority>1000)
          throw Object.assign(new Error("simp_rule priority must be an integer from 0 to 1000."),{offset:number.start});
      }
      const end=take(";").end;
      const directive={kind:"simp_rule",rule,priority,start:t.start,end};
      directives.push(directive);items.push(directive);continue;
    }
    if(t.text==="simp_set") {
      const set=name();define("simp_set name := [rules];");take("[");
      const rules=[];
      if(peek()!=="]")while(true) {
        rules.push(name());
        if(peek()!==",")break;
        take(",");
      }
      take("]");
      const end=take(";").end;
      const directive={kind:"simp_set",name:set,rules,start:t.start,end};
      directives.push(directive);items.push(directive);continue;
    }
    // `evaluate term expecting value;` is a checked computation test.
    if (t.text === "evaluate") {
      const value = expr();
      take("expecting");
      const expected = expr();
      const end = take(";").end;
      const directive = { kind: "evaluate", value, expected, start: t.start, end };
      directives.push(directive); items.push(directive); continue;
    }
    // `print(evaluate(term));`, `print(typeof(term));` and
    // `print(inspect(term));` show what a closed term computes to, its type,
    // and the term the kernel checked.
    if (t.text === "print" && peek() === "(") {
      take("(");
      const show = take();
      if (!["evaluate", "typeof", "inspect"].includes(show.text))
        throw Object.assign(new Error("print shows evaluate(term), typeof(term) or inspect(term)."), { offset: show.start });
      take("(");
      const value = expr();
      take(")");
      take(")");
      const end = take(";").end;
      const directive = { kind: "print", show: show.text, value, start: t.start, end };
      directives.push(directive); items.push(directive); continue;
    }
    // `theory T [extends P, label : Q(f := g notation x + y)] { fields }`
    // declares a theory (L2.4): its parents, sorts, operations with their
    // notations, and laws. The translator expands it into the definitions of
    // its models (theories.mjs).
    if (t.text === "theory") {
      const n = name(), parents = [];
      const notationAfter = () => {
        const notationKeyword = take(), left = name(), operator = take(), right = name();
        if (!notationOperators.includes(operator.text))
          throw Object.assign(new Error("A notation is a binary operator: x + y, x * y, x < y or x <= y."), { offset: operator.start });
        return { operator: operator.text, left, right, keyword: notationKeyword, operatorToken: operator,
          start: notationKeyword.start, end: right.end };
      };
      if (peek() === "extends") {
        take("extends");
        while (true) {
          const start = ts[i].start, label = ts[i + 1].text === ":" ? name() : null;
          if (label) take(":");
          const parent = name(), renaming = [];
          if (peek() === "(") {
            take("(");
            while (peek() !== ")") {
              const from = name();
              take(":=");
              const to = name(), notation = peek() === "notation" ? notationAfter() : null;
              renaming.push({ from, to, notation });
              if (peek() !== ",") break;
              take(",");
            }
            take(")");
          }
          parents.push({ label, name: parent, renaming, start, end: ts[i - 1].end });
          if (peek() !== ",") break;
          take(",");
        }
      }
      take("{");
      const fields = [];
      const word = text => peek() === text && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text);
      while (peek() !== "}") {
        if (peek() === "EOF") throw Object.assign(new Error("Expected '}' to close the theory."), { offset: ts[i].start });
        const start = ts[i].start;
        if (word("sort")) {
          take("sort");
          const sort = name();
          take(":");
          const level = take();
          if (!["set", "prop"].includes(level.text))
            throw Object.assign(new Error("A sort is a set or a proposition: sort M : set; or sort P : prop;"), { offset: level.start });
          fields.push({ kind: "sort", name: sort, level: level.text, levelToken: level, start, end: take(";").end });
          continue;
        }
        const law = word("law");
        const keyword = law ? take("law") : null;
        const field = name(), params = peek() === "(" ? parameters("(x, y : M)", false) : [];
        if (peek() !== ":")
          throw Object.assign(new Error(`Expected ':' and the type of ${field.text}, as in ${law ? "law mul_one(x : M) : x * one = x;" : "mul(x, y : M) : M;"}`), { offset: ts[i].start });
        take(":");
        const type = expr();
        const notation = !law && peek() === "notation" ? notationAfter() : null;
        fields.push({ kind: law ? "law" : "operation", name: field, params, type, notation,
          ...(keyword ? { keyword } : {}), start, end: take(";").end });
      }
      const end = take("}").end;
      declarations.push({ kind: "theory", name: n, parents, fields, start: t.start, end });
      items.push(declarations.at(-1));
      continue;
    }
    // `inductive T(params) : R { constructors }` declares a type (H1; the
    // specification's section 9). R is an h-level, a universe or both.
    if (t.text === "inductive") {
      const n = name(), params = peek() === "(" ? parameters("(U < UU0, A : U)", true) : [];
      let result = null;
      if (peek() === ":") { take(":"); result = sortResult(); }
      take("{");
      const constructors = [];
      while (peek() !== "}") {
        if (peek() === "EOF") throw Object.assign(new Error("Expected '}' to close the inductive declaration."), { offset: ts[i].start });
        const c = name(), args = peek() === "(" ? parameters("(n : Nat)", false) : [];
        let type = null;
        if (peek() === ":") { take(":"); type = expr(); }
        const end = take(";").end;
        constructors.push({ kind: "constructor", name: c, params: args, type, start: c.start, end });
      }
      const end = take("}").end;
      declarations.push({ kind: "inductive", name: n, params, result, constructors, start: t.start, end });
      items.push(declarations.at(-1));
      continue;
    }
    // `computable def` asserts that the checked result uses no assumption.
    const computable = t.text === "computable" && peek() === "def";
    const modifierStart = computable ? t.start : undefined;
    if (computable) t = take();
    if (t.text !== "def")
      throw Object.assign(new Error(t.text === "import" ? "Imports must come before declarations."
        : "Expected a declaration or directive: def, computable def, inductive, evaluate, print, simp_rule, simp_set or theory."), {
        offset: t.start,
      });
    const n = name(),
      params = [];
    // A declaration's parameter list, `(n, m : Nat, U < UU0)` or, before it,
    // the implicit ones, `{{U < UU0, A : U}}`, which a call fills as holes
    // unless it gives them (L4.1b).
    const telescope = (close, implicit) => {
      if (peek() !== close) {
        while (true) {
          const names = sharedNames();
          const { type, bound } = binderType(implicit ? "{{U < UU0, A : U}}" : "(U < UU0, A : U)");
          const group = params.length;
          for (const p of names) params.push({ name:p, ...(bound ? { bound } : { type }), group, ...(implicit ? { implicit } : {}) });
          if (peek() !== ",") break;
          take(",");
        }
      }
      return take(close);
    };
    let implicitParameters = null;
    if (doubleBrace()) {
      const open = take("{"), inner = take("{");
      const { first, last } = closeDoubleBrace(telescope("}", true));
      implicitParameters = { opens: [open.start, inner.start], closes: [first.end, last.end], start: open.start, end: last.end };
    } else if (peek() === "{")
      throw Object.assign(new Error("Implicit parameters are in double braces: def f{{U < UU0, A : U}}(…)."), { offset: ts[i].start });
    const header = implicitParameters ? { implicitParameters } : {};
    if (!params.length && binds()) {
      take();
      const value = expr();
      const end = take(";").end;
      declarations.push({
        kind: t.text,
        ...(computable ? { computable, modifierStart } : {}),
        name: n,
        value,
        valueStart: value.start,
        valueEnd: value.end,
        valueParameters: [],
        params,
        start: t.start,
        end,
      });items.push(declarations.at(-1));
      continue;
    }
    if (peek() === "(") {
      take("(");
      telescope(")", false);
    }
    if (binds()) {
      take();
      let value = expr();
      const valueStart = value.start, valueEnd = value.end;
      const end = take(";").end;
      for (let j = params.length - 1; j >= 0;) {
        const group = params[j].group, members = [];
        while (j >= 0 && params[j].group === group) members.unshift(params[j--]);
        const binder = members[0].bound ? { bound: members[0].bound } : { domain: members[0].type };
        value = members.length === 1
          ? {kind:"lambda",name:members[0].name,...binder,body:value,
              start:members[0].name.start,end:value.end}
          : {kind:"binderGroup",binderKind:"lambda",names:members.map(p=>p.name),
              ...binder,body:value,start:members[0].name.start,end:value.end};
      }
      declarations.push({
        kind: t.text,
        ...(computable ? { computable, modifierStart } : {}),
        name: n,
        value,
        valueStart,
        valueEnd,
        valueParameters: params,
        params: [],
        ...header,
        start: t.start,
        end,
      });items.push(declarations.at(-1));
      continue;
    }
    if (peek() === "=") define("def name := term;");
    take(":");
    const type = expr();
    // `def name : T := term;` states the type of a term; it is the block
    // `{ exact term; }`.
    if (peek() === ":=") {
      const assign = take(":="), value = expr(), end = take(";").end;
      declarations.push({
        kind: t.text, ...(computable ? { computable, modifierStart } : {}), name: n, params, type, ...header,
        body: [{ kind: "exact", value, start: assign.start, end }], typedValue: true, start: t.start, end,
      });items.push(declarations.at(-1));
      continue;
    }
    if (peek() === ";" && type.kind === "binary" && type.operator === "=")
      throw Object.assign(new Error("Write := to give a value: def name : T := term; here `=` read as an equality type"), { offset: type.operatorStart });
    const body = block();
    declarations.push({
      kind: t.text,
      ...(computable ? { computable, modifierStart } : {}),
      name: n,
      params,
      type,
      body,
      ...header,
      start: t.start,
      end: ts[i - 1].end,
    });items.push(declarations.at(-1));
  }
  return { module, imports, declarations,
    ...(directives.length?{directives,items}:{}) };
}
