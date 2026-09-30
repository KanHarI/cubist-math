// A small mathematical proof language. Parsing never evaluates JavaScript.
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
      throw Object.assign(new Error(`${t.text} is a universe constant; choose another name.`), { offset: t.start });
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
    let a;
    const t = take();
    if (t.text === "with") {
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
      a = { kind: "withUnfolding", hints, body, start: t.start, end };
    } else if (t.text === "induction") {
      // `induction n [as k] return C { … }`: as names the value in the motive
      // and the predecessor in the successor clause; without it the motive is
      // constant and the predecessor unnamed.
      const value = expr();
      let index = null;
      if (peek() === "as") { take("as"); index = name(); }
      take("return");
      const type = expr();
      take("{");
      take("zero");
      take("=>");
      const base = expr();
      take(";");
      take("succ");
      const hypothesis = name();
      take("=>");
      const step = expr();
      take(";");
      const end = take("}").end;
      a = {
        kind: "induction",
        value,
        index,
        type,
        base,
        hypothesis,
        step,
        start: t.start,
        end,
      };
    } else if (t.text === "match") {
      // `match v [as z] [return T] { c(xs) @ i => body; … }`: a clause per
      // constructor, its arguments in parentheses, then its dimensions. The
      // legacy match on a sum, `left x => …; right y => …;`, keeps its fields.
      const value = expr();
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
      a = { kind: "match", motiveName, value, type, start: t.start, end, ...obligations };
      // The legacy shape keeps its fields; its clauses stay readable but are
      // not enumerated, so a walk over the tree meets each body once.
      if (!obligations.obligationsToken && clauses.length === 2 && clauses[0].constructor.text === "left" && clauses[1].constructor.text === "right"
          && clauses.every(clause => !clause.args && clause.binders.length === 1 && !clause.coordinates.length)) {
        Object.assign(a, { left: clauses[0].binders[0], leftBody: clauses[0].body,
          right: clauses[1].binders[0], rightBody: clauses[1].body });
        Object.defineProperty(a, "clauses", { value: clauses, enumerable: false });
      } else a.clauses = clauses;
    } else if (t.text === "unpack" && peek() !== "(") {
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
      a = {
        kind: "unpack",
        value,
        type,
        left,
        right,
        body,
        start: t.start,
        end,
      };
    } else if (t.text === "path" && /^[A-Za-z_][A-Za-z_0-9]*$/.test(peek()) && ts[i + 1]?.text === "=>") {
      const dimension = name();
      take("=>");
      const body = expr();
      a = { kind: "pathLambda", dimension, body, start: t.start, end: body.end };
    } else if (t.text === "along") {
      const family = expr();
      take("by");
      const path = expr();
      take("from");
      const value = expr();
      a = { kind:"along", family, path, value, start:t.start, end:value.end };
    } else if (t.text === "fun") {
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
      a = expr();
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
    } else if (t.text === "forall" || t.text === "exists") {
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
      a = {
        kind: names.length === 1 ? t.text : "binderGroup",
        ...(names.length === 1 ? {name:names[0]} : {names}),
        binderKind:t.text, domain, ...(bound ? { bound } : {}), body, start:t.start, end:body.end,
        keyword:{start:t.start,end:t.end},
      };
    } else if (t.text === "-") {
      const operand = expr(PREFIX);
      a = { kind: "unary", operator: "-", operand, operatorStart: t.start, operatorEnd: t.end,
        start: t.start, end: operand.end };
    } else if (t.text === "(") {
      a = tuple(t, expr(), () => expr());
    } else if (/^0b[01]+$/.test(t.text)) {
      const digits = t.text.slice(2).replace(/^0+(?=.)/, "");
      if (digits.length > 256)
        throw Object.assign(new Error("Binary literals are limited to 256 significant bits."), { offset: t.start });
      a = { kind: "binaryNumber", digits, spelling: t.text, start: t.start, end: t.end };
    } else if (/^[0-9]+$/.test(t.text)) {
      if (Number(t.text) > 256)
        throw Object.assign(
          new Error("Numerals are limited to 256 in this version."),
          { offset: t.start },
        );
      a = { kind: "number", value: Number(t.text), start: t.start, end: t.end };
    } else if (/^[A-Za-z_][A-Za-z_0-9]*$/.test(t.text) && t.text !== "EOF")
      a = { kind: "name", name: t.text, start: t.start, end: t.end };
    else
      throw Object.assign(
        new Error(`Expected an expression, found '${t.text}'.`),
        { offset: t.start },
      );
    while (true) {
      if (peek() === "(") {
        take("(");
        const args = [];
        if (peek() !== ")") {
          args.push(expr());
          while (peek() === ",") {
            take(",");
            args.push(expr());
          }
        }
        const end = take(")");
        a = { kind: "call", fn: a, args, start: a.start, end: end.end };
        continue;
      }
      // A qualified name, T.squash, is tight too: a name, a dot and a name.
      if (a.kind === "name" && peek() === "." && ts[i - 1].end === ts[i].start
          && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text) && ts[i + 1].start === ts[i].end) {
        const dot = take(".");
        const member = take();
        a = { kind: "name", name: `${a.name}.${member.text}`, qualifiedDot: { start: dot.start, end: dot.end },
          start: a.start, end: member.end };
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
  function clauseHead() {
    let constructor = name(), qualifiedDot = null;
    if (peek() === "." && ts[i - 1].end === ts[i].start && /^[A-Za-z_][A-Za-z_0-9]*$/.test(ts[i + 1].text)
        && ts[i + 1].start === ts[i].end) {
      const dot = take("."), member = take();
      qualifiedDot = { start: dot.start, end: dot.end };
      constructor = { text: `${constructor.text}.${member.text}`, start: constructor.start, end: member.end };
    }
    let args = null;
    if (peek() === "(") {
      take("(");
      args = [];
      if (peek() !== ")") {
        args.push(name());
        while (peek() === ",") { take(","); args.push(name()); }
      }
      take(")");
    }
    // A bare name binds a sum's side in the legacy clause, left x =>. A path
    // constructor's coordinates follow @, as in the point the clause covers:
    // loop @ i =>.
    const binders = [], coordinates = [];
    while (peek() !== "=>" && peek() !== "@") binders.push(name());
    while (peek() === "@") { take("@"); coordinates.push(name()); }
    take("=>");
    return { constructor, args, binders, coordinates, ...(qualifiedDot ? { qualifiedDot } : {}) };
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
      let s;
      if (t.text === "intro") {
        // intro m, n; takes several inputs, named in order.
        const names = [name()];
        while (peek() === ",") { take(","); names.push(name()); }
        if (/^[A-Za-z_]/.test(peek()) && peek() !== "EOF")
          throw Object.assign(new Error("Separate names with commas: intro m, n;"), { offset: ts[i].start });
        const end = take(";");
        s = names.map(n => ({ kind: "intro", name: n, start: t.start, end: end.end }));
      } else if (t.text === "let" || t.text === "obtain") {
        const target = pattern();
        if (t.text === "let" && target.kind !== "name")
          throw Object.assign(new Error("Use obtain to unpack a pair."), {
            offset: target.start,
          });
        define(t.text === "let" ? "let name := term;" : "obtain (a, b) := pair;");
        const value = expr();
        const e = take(";");
        s = { kind: t.text, target, value, start: t.start, end: e.end };
      } else if (t.text === "have") {
        const n = name();
        if (peek() === "=") define("have name := term;");
        if (binds()) {
          take();
          const value = expr(), end = take(";");
          s = { kind: "haveValue", name: n, value, start: t.start, end: end.end };
        } else {
          take(":");
          const type = expr();
          if (peek() === ":=") {
            take(":=");
            const value = expr(), end = take(";");
            s = { kind: "haveValue", name: n, type, value, start: t.start, end: end.end };
          } else {
            const body = block();
            s = { kind: "have", name: n, type, body, start: t.start, end: ts[i - 1].end };
          }
        }
      } else if (t.text === "show") {
        // show T; restates the goal as a type equal to it by computation.
        const type = expr(), end = take(";");
        s = { kind: "show", type, start: t.start, end: end.end };
      } else if (t.text === "suffices") {
        // suffices h : T by proof; proves the goal from h : T, and the
        // statements after it prove T. The proof is a term or a block.
        if (!/^[A-Za-z_]/.test(peek()) || peek() === "EOF" || ts[i + 1].text !== ":")
          throw Object.assign(new Error("suffices names its hypothesis: suffices h : T by term;"), { offset: ts[i].start });
        const n = name();
        take(":");
        const type = expr();
        if (peek() !== "by")
          throw Object.assign(new Error(`suffices needs a proof of the goal from ${n.text} after by: suffices ${n.text} : T by term;`), { offset: ts[i].start });
        const by = take("by");
        const proof = peek() === "{" ? { kind: "block", body: block() } : { kind: "term", value: expr() };
        const end = proof.kind === "term" ? take(";").end : ts[i - 1].end;
        s = { kind: "suffices", name: n, type, proof, by: { start: by.start, end: by.end }, start: t.start, end };
      } else if (t.text === "rfl") {
        const end = take(";");
        s = { kind: "rfl", start: t.start, end: end.end };
      } else if (t.text === "ext") {
        const variable = name(), end = take(";");
        s = { kind: "ext", variable, start: t.start, end: end.end };
      } else if (t.text === "over") {
        const family=expr();
        take("along");
        const path=expr();
        take("by");
        const body=block();
        s = {kind:"over",family,path,body,start:t.start,end:ts[i-1].end};
      } else if (t.text === "calc") {
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
        s = { kind: "calc", steps, start: t.start, end: end.end };
      } else if (t.text === "rw") {
        take("[");
        const rules = [];
        if (peek() !== "]") while (true) {
          const reverse = peek() === "<-";
          const reverseToken = reverse ? take("<-") : null;
          const value = expr();
          rules.push({ value, reverse, start: reverseToken?.start ?? value.start, end: value.end });
          if (peek() !== ",") break;
          take(",");
        }
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
        s = { kind: "rw", rules, target, occurrence, start: t.start, end: end.end };
      } else if (t.text === "simp" || t.text === "simpa") {
        const only=peek()==="only";
        if(only)take("only");
        const rules = [];
        if(peek()==="[") {
          take("[");
          if (peek() !== "]") while (true) {
            const reverse = peek() === "<-";
            const reverseToken = reverse ? take("<-") : null;
            const value = expr();
            rules.push({value, reverse, start:reverseToken?.start ?? value.start, end:value.end});
            if (peek() !== ",") break;
            take(",");
          }
          take("]");
        } else if(only) {
          throw Object.assign(new Error("simp only requires an explicit rule list."),{offset:ts[i].start});
        }
        const without=[];
        if(peek()==="without") {
          if(only)throw Object.assign(new Error("simp only cannot exclude rules."),{offset:ts[i].start});
          take("without");take("[");
          if(peek()!=="]")while(true) {
            without.push(name());
            if(peek()!==",")break;
            take(",");
          }
          take("]");
        }
        const witnesses=[];
        if(peek()==="with") {
          take("with");take("[");
          if(peek()!=="]")while(true) {
            witnesses.push(name());
            if(peek()!==",")break;
            take(",");
          }
          take("]");
        }
        let at=null,as=null;
        if(t.text==="simp"&&peek()==="at") {
          take("at");at=name();take("as");as=name();
        }
        const using = t.text === "simpa" ? (take("using"),expr()) : null;
        const end = take(";");
        s = {kind:t.text === "simpa" ? "simpaOnly" : "simpOnly", rules, only,without,witnesses,
          ...(at?{at,as}:{}),
          ...(using?{using}:{}), start:t.start, end:end.end};
      } else if (t.text === "hlevel") {
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
        s = { kind: "hlevel", hints, start: t.start, end: end.end };
      } else if (t.text === "exact") {
        const value = expr(),
          e = take(";");
        s = { kind: "exact", value, start: t.start, end: e.end };
      } else if (t.text === "match") {
        // The closing statement `match v { c(xs) @ i => { … } … }` (work plan
        // L2.2a): a clause per constructor, each a proof block of the goal at
        // that constructor. Its motive comes from the goal.
        const value = expr();
        if (peek() === ",")
          throw Object.assign(new Error("The match statement takes apart one value; match on the first, then on the next inside each clause."),
            { offset: ts[i].start });
        if (peek() === "as" || peek() === "return")
          throw Object.assign(new Error("The match statement takes its motive from the goal: write match v { c(xs) => { … } … } without as or return."),
            { offset: ts[i].start });
        take("{");
        const clauses = [];
        while (peek() !== "}") {
          if (peek() === "EOF") throw Object.assign(new Error("Expected '}' to close the match."), { offset: ts[i].start });
          const head = clauseHead();
          if (peek() !== "{")
            throw Object.assign(new Error("A clause of the match statement is a proof block: c(xs) => { … }."), { offset: ts[i].start });
          const body = block();
          clauses.push({ kind: "clause", ...head, body, start: head.constructor.start, end: ts[i - 1].end });
        }
        const e = take("}");
        s = { kind: "matchStatement", value, clauses, start: t.start, end: e.end, ...matchObligations(false) };
      } else if (t.text === "cases") {
        const value = expr();
        take("{");
        take("left");
        const left = name();
        take("=>");
        const leftBody = block();
        take("right");
        const right = name();
        take("=>");
        const rightBody = block();
        const e = take("}");
        s = {
          kind: "cases",
          value,
          left,
          leftBody,
          right,
          rightBody,
          start: t.start,
          end: e.end,
        };
      } else
        throw Object.assign(
          new Error(
            `Expected a proof statement; found '${t.text}'.`,
          ),
          { offset: t.start },
        );
      const parsed = [s].flat();
      // A statement's leading token is its keyword, a source link site.
      for (const statement of parsed) statement.keyword = { start: t.start, end: t.end };
      statements.push(...parsed);
    }
    take("}");
    depth--;
    return statements;
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
        : "Expected a declaration or directive: def, computable def, inductive, evaluate, simp_rule or simp_set."), {
        offset: t.start,
      });
    const n = name(),
      params = [];
    if (binds()) {
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
      if (peek() !== ")") {
        while (true) {
          const names = sharedNames();
          const { type, bound } = binderType("(U < UU0, A : U)");
          const group = params.length;
          for (const p of names) params.push({ name:p, ...(bound ? { bound } : { type }), group });
          if (peek() !== ",") break;
          take(",");
        }
      }
      take(")");
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
        kind: t.text, ...(computable ? { computable, modifierStart } : {}), name: n, params, type,
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
      start: t.start,
      end: ts[i - 1].end,
    });items.push(declarations.at(-1));
  }
  return { module, imports, declarations,
    ...(directives.length?{directives,items}:{}) };
}
