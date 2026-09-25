// A small mathematical proof language. Parsing never evaluates JavaScript.
export function tokenize(source) {
  if (typeof source !== "string" || source.length > 1000000)
    throw new Error("Source exceeds 1 MB.");
  const tokens = [];
  const re =
    /\s+|\/\/[^\n]*|(?:<=|=>|->|:=|<-)|0b[A-Za-z_0-9]*|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[\[\](){}:,;+*<=>@]|./gy;
  for (const match of source.matchAll(re)) {
    const text = match[0];
    if (/^\s|^\/\//.test(text)) continue;
    if (
      !/^(?:0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|<=|=>|->|:=|<-|[\[\](){}:,;+*<=>@])$/.test(text)
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
    if (t.text === "EOF" || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(t.text))
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
    "@": 7,
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
      while (peek() === "(") {
        take("(");
        const names = [name()];
        while (peek() !== ":") names.push(name());
        take(":");
        const domain = expr();
        take(")");
        binders.push({ names, domain });
      }
      if (!binders.length) binders.push({ names: [name()], domain: null });
      take("=>");
      a = expr();
      for (let index=binders.length-1;index>=0;index--) {
        const binder=binders[index];
        a = {
          kind: binder.names.length === 1 ? "lambda" : "binderGroup",
          ...(binder.names.length === 1 ? {name:binder.names[0]} : {names:binder.names}),
          binderKind:"lambda",domain: binder.domain, body:a, start:t.start, end:a.end,
          // Only the outer expression owns the single source `fun` token.
          ...(index ? {generatedBinder:true} : {keyword:{start:t.start,end:t.end}}),
        };
      }
    } else if (t.text === "forall" || t.text === "exists") {
      const names = [name()];
      while (peek() !== ":") names.push(name());
      take(":");
      const domain = expr();
      take(",");
      const body = expr();
      a = {
        kind: names.length === 1 ? t.text : "binderGroup",
        ...(names.length === 1 ? {name:names[0]} : {names}),
        binderKind:t.text, domain, body, start:t.start, end:body.end,
        keyword:{start:t.start,end:t.end},
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
        const names = [name()];
        while (peek() !== ";") names.push(name());
        const end = take(";");
        s = names.map(n => ({ kind: "intro", name: n, start: t.start, end: end.end }));
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
        if (peek() === "=") {
          take("=");
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
      const set=name();take("=");take("[");
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
    // `computable def` asserts that the checked result uses no assumption.
    const computable = t.text === "computable" && ["def", "opaque"].includes(peek());
    const modifierStart = computable ? t.start : undefined;
    if (computable) t = take();
    const opaque = t.text === "opaque";
    if (opaque) t = take("def");
    if (!["def", "axiom"].includes(t.text))
      throw Object.assign(new Error("Expected def or axiom."), {
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
          const names = [name()];
          while (peek() !== ":") names.push(name());
          take(":");
          const type = expr();
          const group = params.length;
          for (const p of names) params.push({ name:p, type, group });
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
      for (let j = params.length - 1; j >= 0;) {
        const group = params[j].group, members = [];
        while (j >= 0 && params[j].group === group) members.unshift(params[j--]);
        value = members.length === 1
          ? {kind:"lambda",name:members[0].name,domain:members[0].type,body:value,
              start:members[0].name.start,end:value.end}
          : {kind:"binderGroup",binderKind:"lambda",names:members.map(p=>p.name),
              domain:members[0].type,body:value,start:members[0].name.start,end:value.end};
      }
      declarations.push({
        kind: t.text,
        opaque,
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
    take(":");
    const type = expr();
    const body = t.text === "axiom" ? (take(";"), null) : block();
    declarations.push({
      kind: t.text,
      opaque,
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
