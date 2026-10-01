// Replay snapshots emitted by test-instructions --fixtures FILE. Native
// definition references in a snapshot were expanded by the native test.
import { CubicalKernel, cubicalKinds } from "../web/cubical-kernel.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { H1Translation, counterpartSpecifications } from "../web/h1-translation.mjs";
import { T } from "../web/dist/cubical-runtime/core.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { instructions, stepRules } from "../web/cubical-instructions.mjs";

const binders = new Set(["Var","Pi","Lam","Sigma","W","LPi","LLam"]);
const native = new Set(["Nat","Zero","Succ","NatRec","Sum","Inl","Inr","SumRec","W","Sup","WRec",
  "Pushout","PushLeft","PushRight","PushPath","PushElim"]);
const errorKinds = ["none","mismatch","budget","deadline","other"];
// These requests use a different declared API (or, for Lookup, the
// documented raw-definition workflow). Pin that diagnostic as well as its
// error class; shared baseline requests retain the native diagnostic.
const declaredRefusalMessages = {
  lookup:"The term checker has no rules for declared types",
  pushLeft:"Expected Pushout, found Sort",
  sup:"Expected W, found Sort",
  hcomp:"A declared data sort has no formal composition or transport",
};
export function replayInstructions(module, fixtures, {sourceModule=module}={}) {
  const kernel = new CubicalKernel(sourceModule), source = new NativeCubicalElaborator(kernel);
  const target = new H1Translation(module,source);
  const report = { replayed:0, equalities:0, refused:0, unequal:0, refusals:{}, refusalReasons:[], kinds:{}, failures:[] };
  const importNode = node => {
    if (!node) return 0;
    let [index,payload,children] = node;
    const kind = cubicalKinds[index];
    if (typeof payload === "object") payload=kernel.formula(payload.sort ? "face" : "interval",
      payload.clauses.map(clause=>clause.map(BigInt)));
    else if(binders.has(kind)) payload=kernel.symbol(`fixture_${payload}`);
    return kernel.term(kind,payload,...children.map(importNode));
  };
  const refusal = fixture => {
    const entries = new Map();
    const collect = fact => {
      if(!fact) return;
      for(const entry of [...(fact.context ?? []),...(fact.entry ? [fact.entry] : [])]) entries.set(`${entry[1]}_${entry[0]}`,entry);
      fact.inputs?.forEach(collect);
    };
    fixture.arguments.forEach(collect); collect({entry:fixture.entry});
    const dimensions = new Map([...entries.values()].filter(([,dim])=>dim).map(([symbol])=>[`d${symbol}`,symbol]));
    const decode = node=>source.syntax.decode(importNode(node),dimensions);
    const context = new Map([...entries.values()].filter(([,dim])=>!dim).map(([symbol,,type])=>[`fixture_${symbol}`,decode(type)]));
    const terms=fixture.arguments.map(argument=>argument && argument.kind !== 3 ? decode(argument.term) : null);
    const imageContext=new Map([...context].map(([name,type])=>[name,target.map(type,context,dimensions)]));
    const images=terms.map(term=>term && target.map(term,context,dimensions));
    const face=fixture.face ? {clauses:fixture.face.clauses.map(clause=>clause.map(BigInt))} : null;
    const attempt = (checker,values,scope,declared) => {
      const driver=checker.driver, graph=driver.graph, syntax=checker.syntax;
      const assumptions=[...scope].map(([name,type])=>[checker.kernel.symbol(name),syntax.encode(type,dimensions)]);
      const mask=checker.dimensionMask(dimensions);
      const ownScope=driver.contextScope(assumptions,mask);
      const entryId=entry=>entry[1] ? graph.dimension(entry[0]) : ownScope.get(checker.kernel.symbol(`fixture_${entry[0]}`));
      const mapped=node=>declared ? target.map(decode(node),context,dimensions) : decode(node);
      const raw=node=>syntax.encode(mapped(node),dimensions);
      const formula=value=>checker.kernel.formula("face",value.clauses.map(clause=>clause.map(BigInt)));
      const derive = fact => {
        if(!fact) return 0;
        if(fact.kind !== 3) {
          const judgement=driver.check(raw(fact.term),raw(fact.type),assumptions,mask);
          if(fact.kind !== 2) return judgement;
          const other=driver.check(raw(fact.other),raw(fact.type),assumptions,mask);
          const left=driver.focus(graph.refl(judgement),"other"), right=driver.focus(graph.refl(other),"other");
          if(!driver.agree(left,right)) throw Error("Refusal premise equality failed to replay.");
          return graph.transitivity(left.ref.id,graph.symmetry(right.ref.id));
        }
        const [a,b,c]=fact.inputs.map(derive);
        switch(instructions[fact.rule]) {
          case "system": return graph.system(entryId(fact.entry),a,b);
          case "systemTube": return graph.systemTube(a,formula(fact.face),b,c);
          case "systemOverlap": return graph.systemOverlap(a,fact.operand,b);
          case "glueBase": return graph.glueBase(a);
          case "gluePiece": return graph.gluePiece(a,formula(fact.face),b,c);
          case "glueTermBase": return graph.glueTermBase(a,b);
          case "glueTermPiece": return graph.glueTermPiece(a,b,c);
          default: throw Error(`Unknown fixture system rule ${instructions[fact.rule]}.`);
        }
      };
      // Every premise is independently admitted, including the unfinished
      // system's recorded instructions, before testing the rejected request.
      const judgements=fixture.arguments.map(derive);
      const execute=()=> {
      switch(fixture.operation) {
        case "pushout":
          return declared ? checker.infer(T.sort(counterpartSpecifications()[3].name,values),scope,dimensions)
            : graph.pushout(...judgements);
        case "pushLeft": case "pushRight":
          return declared ? checker.infer(target.map({tag:fixture.operation === "pushLeft" ? "PushLeft" : "PushRight",as:terms[0],value:terms[1]},context,dimensions),scope,dimensions)
            : graph.pushPoint(...judgements,fixture.operation === "pushRight");
        case "sup":
          // Mapping the request's native annotation selects the new Con
          // API, including the wrong-former case that must still refuse.
          return declared ? checker.infer(target.map({tag:"Sup",as:terms[0],label:terms[1],children:terms[2]},context,dimensions),scope,dimensions)
            : graph.sup(...judgements);
        case "wElim":
          return declared ? checker.infer(target.map({tag:"WRec",motive:terms[0],step:terms[1],value:terms[2]},context,dimensions),scope,dimensions)
            : graph.wElim(...judgements);
        case "hcomp": return graph.hcomp(judgements[0]);
        case "trans": return graph.trans(judgements[0],checker.kernel.formula("face",face.clauses));
        case "iota": return graph.step(graph.refl(judgements[0]),"other",[],"iota");
        case "replace": return graph.replace(judgements[0],"other",[fixture.operand],judgements[1]);
        case "lambda": return graph.lambda(entryId(fixture.entry),judgements[0]);
        case "extend": return graph.extend(judgements[0],graph.entry(entryId(fixture.entry)).name);
        case "level": return graph.levelEntry(graph.entry(entryId(fixture.entry)).symbol);
        case "step": return graph.step(judgements[0],fixture.operand >>> 16,[],stepRules[fixture.operand & 65535]);
        case "system": return graph.system(entryId(fixture.entry),...judgements);
        case "systemTube": return graph.systemTube(judgements[0],checker.kernel.formula("face",face.clauses),judgements[1],judgements[2]);
        case "systemOverlap": return graph.systemOverlap(judgements[0],fixture.operand,judgements[1]);
        case "gluePiece": return graph.gluePiece(judgements[0],checker.kernel.formula("face",face.clauses),judgements[1],judgements[2]);
        case "comp": case "glueBase": case "glue": case "glueTermBase": case "glueTerm": case "unglue": case "apply": case "lift":
          return graph[fixture.operation](...judgements);
        case "define": return graph.define(`unclosed_fixture_${fixture.line}`,judgements[0]);
        case "lookup": {
          const reference=checker.kernel.define(`unadmitted_fixture_${fixture.line}`,syntax.encode(values[0],dimensions),raw(fixture.arguments[0].type));
          return graph.lookup(reference);
        }
        case "universeTerm": return graph.universe(syntax.encode(values[0],dimensions));
        case "universeEntry": return graph.universe(checker.kernel.term("Var",graph.entry(entryId(fixture.entry)).symbol));
        case "levelApplyTerm": return graph.levelApply(judgements[0],syntax.encode(values[1],dimensions));
        case "convertible": return graph.convertible(syntax.encode(values[0],dimensions),syntax.encode(values[1],dimensions));
        default: throw Error(`Unknown refusal operation ${fixture.operation}.`);
      }
      };
      try {
        const answer=execute();
        if(fixture.operation === "convertible" && answer === false) return {kind:"none",message:""};
      }
      catch(error) {
        if(!["other","mismatch"].includes(error.kind)) throw error;
        return {kind:error.kind,message:error.message};
      }
      throw Error(`${declared ? "Declared" : "Native"} request accepted ${fixture.operation}.`);
    };
    const nativeReason=attempt(source,terms,context,false), declaredReason=attempt(target.checker,images,imageContext,true);
    if(!fixture.nativeError || nativeReason.kind !== errorKinds[fixture.nativeError.kind])
      throw Error(`Native refusal no longer matches its recorded reason: ${nativeReason.message}`);
    if(declaredReason.kind !== nativeReason.kind)
      throw Error(`Refusal class changed from ${nativeReason.kind} to ${declaredReason.kind}: ${declaredReason.message}`);
    if(nativeReason.kind === "other") {
      // A native constructor whose annotation is not its former keeps its
      // retired node under τ, which the current kernel refuses as syntax.
      const retired=(fixture.operation === "sup" && terms[0].tag !== "W")
        || (["pushLeft","pushRight"].includes(fixture.operation) && terms[0].tag !== "Pushout");
      const expected=retired ? "Unknown term constructor"
        : declaredRefusalMessages[fixture.operation] ?? fixture.nativeError.expected;
      if(!nativeReason.message.includes(fixture.nativeError.expected) || !declaredReason.message.includes(expected))
        throw Error(`Refusal diagnostic changed: native ${nativeReason.message}; declared ${declaredReason.message}`);
    }
    // Mismatch fixtures compare the kernel's type-error class: replay can
    // choose fresh binder names and expose a different mismatch diagnostic.
    report.refusalReasons.push({line:fixture.line,operation:fixture.operation,
      recordedExpected:fixture.nativeError.expected,native:nativeReason,declared:declaredReason});
    if(fixture.operation === "convertible") { report.unequal++; return; }
    report.refused++; report.refusals[fixture.operation]=(report.refusals[fixture.operation] ?? 0)+1;
  };
  try {
    for (const fixture of fixtures) {
      const originalTransaction = new CubicalDeclarationTransaction(kernel,source);
      const imageTransaction = new CubicalDeclarationTransaction(target.kernel,target.checker);
      if(fixture.operation) {
        try { refusal(fixture); }
        catch(error) { report.failures.push({line:fixture.line,operation:fixture.operation,reason:error.message}); }
        finally { originalTransaction.finish(false); imageTransaction.finish(false); }
        continue;
      }
      const dimensions = new Map(fixture.context.filter(([,dim])=>dim).map(([symbol])=>[`d${symbol}`,symbol]));
      const decode = node => source.syntax.decode(importNode(node),dimensions);
      const context = new Map(fixture.context.filter(([,dim])=>!dim).map(([symbol,,type])=>[`fixture_${symbol}`,decode(type)]));
      const term=decode(fixture.term), type=decode(fixture.type), other=fixture.other ? decode(fixture.other) : null;
      const kinds = new Set();
      const visit = value => {
        if (!value || typeof value !== "object") return;
        if (native.has(value.tag) || ["Comp","HComp","Trans"].includes(value.tag)) kinds.add(value.tag);
        Object.values(value).forEach(visit);
      };
      visit(term); visit(type); visit(other);
      if (![...kinds].some(kind=>native.has(kind))) {
        originalTransaction.finish(true); imageTransaction.finish(true); continue;
      }
      try {
        source.check(term,type,context,dimensions);
        if (other && !source.equal(term,other,context,dimensions)) throw Error("Native equality failed to replay.");
        const imageContext = new Map([...context].map(([name,type])=>[name,target.map(type,context,dimensions)]));
        const image=target.map(term,context,dimensions), expected=target.map(type,context,dimensions);
        target.checker.check(image,expected,imageContext,dimensions);
        if (other && !target.checker.equal(image,target.map(other,context,dimensions),imageContext,dimensions))
          throw Error("Translated equality failed to replay.");
        report.replayed++; if(other) report.equalities++;
        for(const kind of kinds) report.kinds[kind]=(report.kinds[kind] ?? 0)+1;
      } catch(error) { report.failures.push({line:fixture.line,rule:fixture.rule,reason:error.message}); }
      finally { originalTransaction.finish(true); imageTransaction.finish(true); }
    }
    return report;
  } finally { target.dispose(); kernel.dispose(); }
}
