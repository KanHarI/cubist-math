// A small mathematical proof language. Parsing never evaluates JavaScript.
export function tokenize(source) {
  if (typeof source !== "string" || source.length > 1000000)
    throw new Error("Source exceeds 1 MB.");
  const tokens = [];
  const re =
    /\s+|\/\/[^\n]*|(?:<=|=>|->)|0b[A-Za-z_0-9]*|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[\[\](){}:,;+*<=>]|./gy;
  for (const match of source.matchAll(re)) {
    const text = match[0];
    if (/^\s|^\/\//.test(text)) continue;
    if (
      !/^(?:0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|<=|=>|->|[\[\](){}:,;+*<=>])$/.test(text)
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
  function name() {
    const t = take();
    if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(t.text))
      throw Object.assign(new Error("Expected a name."), { offset: t.start });
    return t;
  }
  const prec = {
    "->": 1,
    or: 2,
    and: 3,
    "=": 4,
    "<": 4,
    "<=": 4,
    "+": 5,
    "*": 6,
  };
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
      const value = expr();
      take("as");
      const index = name();
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
      const value = expr();
      let motiveName = null;
      if (peek() === "as") {
        take("as");
        motiveName = name();
      }
      take("return");
      const type = expr();
      take("{");
      take("left");
      const left = name();
      take("=>");
      const leftBody = expr();
      take(";");
      take("right");
      const right = name();
      take("=>");
      const rightBody = expr();
      take(";");
      const end = take("}").end;
      a = {
        kind: "match",
        motiveName,
        value,
        type,
        left,
        leftBody,
        right,
        rightBody,
        start: t.start,
        end,
      };
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
    } else if (t.text === "fun") {
      take("(");
      const n = name();
      take(":");
      const domain = expr();
      take(")");
      take("=>");
      const body = expr();
      a = {
        kind: "lambda",
        name: n,
        domain,
        body,
        start: t.start,
        end: body.end,
      };
    } else if (t.text === "forall" || t.text === "exists") {
      const n = name();
      take(":");
      const domain = expr();
      take(",");
      const body = expr();
      a = {
        kind: t.text,
        name: n,
        domain,
        body,
        start: t.start,
        end: body.end,
      };
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
      const p = prec[peek()];
      if (p === undefined || p < min) break;
      const operatorToken = take(), operator = operatorToken.text;
      let carrier;
      if (operator === "=" && peek() === "[") {
        take("["); carrier = expr(); take("]");
      }
      const right = expr(p + (["->", "and", "or"].includes(operator) ? 0 : 1));
      a = {
        kind: "binary",
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
        const n = name(),
          end = take(";");
        s = { kind: "intro", name: n, start: t.start, end: end.end };
      } else if (t.text === "let" || t.text === "obtain") {
        const target = pattern();
        if (t.text === "let" && target.kind !== "name")
          throw Object.assign(new Error("Use obtain to unpack a pair."), {
            offset: target.start,
          });
        take("=");
        const value = expr();
        const e = take(";");
        s = { kind: t.text, target, value, start: t.start, end: e.end };
      } else if (t.text === "have") {
        const n = name();
        take(":");
        const type = expr(),
          body = block();
        s = {
          kind: "have",
          name: n,
          type,
          body,
          start: t.start,
          end: ts[i - 1].end,
        };
      } else if (t.text === "exact") {
        const value = expr(),
          e = take(";");
        s = { kind: "exact", value, start: t.start, end: e.end };
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
            `Expected intro, let, obtain, have, cases, or exact; found '${t.text}'.`,
          ),
          { offset: t.start },
        );
      statements.push(s);
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
  const declarations = [];
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
    const opaque = t.text === "opaque";
    if (opaque) t = take("def");
    if (!["theorem", "def", "axiom"].includes(t.text))
      throw Object.assign(new Error("Expected theorem, def, or axiom."), {
        offset: t.start,
      });
    const n = name(),
      params = [];
    if (peek() === "=" && t.text !== "axiom") {
      take("=");
      const value = expr();
      const end = take(";").end;
      declarations.push({
        kind: t.text,
        opaque,
        name: n,
        value,
        valueStart: value.start,
        valueEnd: value.end,
        valueParameters: [],
        params,
        start: t.start,
        end,
      });
      continue;
    }
    if (peek() === "(") {
      take("(");
      if (peek() !== ")") {
        while (true) {
          const p = name();
          take(":");
          params.push({ name: p, type: expr() });
          if (peek() !== ",") break;
          take(",");
        }
      }
      take(")");
    }
    if (peek() === "=" && t.text !== "axiom") {
      take("=");
      let value = expr();
      const valueStart = value.start, valueEnd = value.end;
      const end = take(";").end;
      for (const p of [...params].reverse())
        value = {
          kind: "lambda",
          name: p.name,
          domain: p.type,
          body: value,
          start: p.name.start,
          end: value.end,
        };
      declarations.push({
        kind: t.text,
        opaque,
        name: n,
        value,
        valueStart,
        valueEnd,
        valueParameters: params,
        params: [],
        start: t.start,
        end,
      });
      continue;
    }
    take(":");
    const type = expr();
    const body = t.text === "axiom" ? (take(";"), null) : block();
    declarations.push({
      kind: t.text,
      opaque,
      name: n,
      params,
      type,
      body,
      start: t.start,
      end: ts[i - 1].end,
    });
  }
  return { module, imports, declarations };
}
