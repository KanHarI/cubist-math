import {createReplConsole} from "./repl-console.mjs";

const element=(tag,text)=>{
  const node=document.createElement(tag);
  if(text!==undefined)node.textContent=text;
  return node;
};
const phases={expression:"Expression",before:"Before statement",after:"After statement",inspection:"Inspected occurrence"};

// The UI holds descriptions and opaque worker session IDs only. Source edits
// revoke the selection immediately; a late response can never re-enable it.
export function createContextualConsole(panel,{request}) {
  const picker=panel.querySelector("select"),status=panel.querySelector("[role=status]"),path=panel.querySelector(".context-path");
  const controls=panel.querySelector("fieldset"),root=panel.querySelector(".context-console");
  const close=panel.querySelector(".context-close");
  let epoch=0,selection=0,snapshot=null,enabled=false,active=null;
  const indexes=new Map(),points=new Map();
  const stale="This context is stale. Check the current source and select a context again.";
  const valid=token=>enabled&&token===epoch;
  const originLabel=point=>{
    const source=snapshot.sources[point.origin.module]??"",before=source.slice(0,point.origin.start);
    return `${point.origin.module}:${before.split("\n").length}:${point.origin.start-before.lastIndexOf("\n")}`;
  };
  const excerpt=point=>(snapshot.sources[point.origin.module]??"").slice(point.origin.start,point.origin.end)
    .replace(/\s+/g," ").slice(0,80);
  const label=point=>`${point.declaration??"Source"} · ${phases[point.phase]} · ${originLabel(point)} · ${excerpt(point)}`;
  function release() {
    const previous=active;active=null;
    if(previous)request("context-close",{session:previous.session}).catch(()=>{});
  }
  function invalidate(reason=stale) {
    epoch++;selection++;enabled=false;indexes.clear();points.clear();release();
    controls.disabled=true;picker.disabled=true;status.textContent=reason;
    for(const button of document.querySelectorAll(".context-entry"))button.disabled=true;
    return epoch;
  }
  async function index(module,token) {
    if(!valid(token))return [];
    if(!indexes.has(module))indexes.set(module,request("contexts",{module}));
    const result=await indexes.get(module);
    if(!valid(token))return [];
    for(const point of result.points)points.set(point.id,point);
    return result.points;
  }
  async function select(point,current=()=>true) {
    const token=epoch,chosen=++selection;
    release();controls.disabled=true;root.replaceChildren();
    const ancestors=[];
    for(let current=point;current;current=points.get(current.parent))ancestors.unshift(current);
    path.textContent=ancestors.filter((item,index)=>index===0||excerpt(item)!==excerpt(ancestors[index-1]))
      .map(item=>`${phases[item.phase]} ${excerpt(item)}`).join(" › ");
    if(!point.available){status.textContent=point.reason;return;}
    status.textContent="Opening the selected context…";
    let opened;
    try {opened=await request("context-open",{scope:point.id});}
    catch(error) {
      if(valid(token)&&selection===chosen&&current())status.textContent=error.message;
      return;
    }
    if(!valid(token)||selection!==chosen||!current()) {
      request("context-close",{session:opened.session}).catch(()=>{});return;
    }
    active=opened;controls.disabled=false;
    status.textContent=`${label(point)}. Results apply only to this selected instance; local values may be symbolic.`;
    createReplConsole(root,{
      label:"Contextual console input",
      greeting:["Use /locals for bindings, /goal for the target, and /prove { ... } to try a proof."],
      run:async input=>{
        const current=active;
        if(!valid(token)||selection!==chosen||!current)return [{kind:"unavailable",text:stale}];
        const results=await request("context-run",{session:current.session,input});
        return valid(token)&&selection===chosen&&active===current?results:[{kind:"unavailable",text:stale}];
      },
      reset:async()=>{
        if(!valid(token)||selection!==chosen)throw new Error(stale);
        release();
        const reopened=await request("context-open",{scope:point.id});
        if(!valid(token)||selection!==chosen) {
          request("context-close",{session:reopened.session}).catch(()=>{});throw new Error(stale);
        }
        active=reopened;
      },
    });
    root.querySelector("textarea").placeholder="/locals;   /goal;   typeof x;";
    root.querySelector("textarea").focus();
  }
  function choose(candidates,heading) {
    selection++;release();controls.disabled=true;root.replaceChildren();path.textContent="";
    picker.replaceChildren(element("option","Choose a scope instance…"));picker.firstChild.value="";
    const counts=new Map(),ordinals=new Map();
    // Hidden expansion provenance can differ while all displayed coordinates
    // coincide. Number the labels users actually see, not the metadata.
    const group=label;
    for(const point of candidates)counts.set(group(point),(counts.get(group(point))??0)+1);
    for(const point of candidates) {
      const key=group(point),ordinal=(ordinals.get(key)??0)+1;ordinals.set(key,ordinal);
      const option=element("option",label(point)+(counts.get(key)>1?` · instance ${ordinal} of ${counts.get(key)}`:"")
        +(point.available?"":" · unavailable"));
      option.value=point.id;picker.append(option);
    }
    panel.hidden=false;picker.disabled=false;
    status.textContent=`${heading}. Select one of ${candidates.length} recorded contexts. Different instances may have different refinements.`;
    panel.scrollIntoView({block:"nearest"});picker.focus();
  }
  picker.onchange=()=>{
    const point=points.get(picker.value);
    if(!point){selection++;release();controls.disabled=true;return;}
    select(point);
  };
  close.onclick=()=>{selection++;release();controls.disabled=true;panel.hidden=true;};
  return {
    invalidate,
    get collecting() {return enabled;},
    async openInspection({module,scope},current=()=>true) {
      const token=epoch,listed=await index(module,token);
      if(!valid(token)||!current())return;
      const point=listed.find(point=>point.id===scope);
      if(!point)throw new Error("The inspected context is unavailable. Check the source and inspect the occurrence again.");
      choose([point],"Inspected context");
      picker.value=point.id;
      await select(point,current);
    },
    checked(result,token,collect) {
      if(token!==epoch)return;
      snapshot=result;enabled=collect;
      status.textContent=collect?"Open a context from the inspector, checked source or a generated declaration."
        :"Enable local context collection and check the source to select a context.";
    },
    async decorate(target,view,{module,generated=false}) {
      const token=epoch,first=target.firstElementChild;
      if(!enabled)return;
      let listed;
      try {listed=await index(module,token);}
      catch(error) {
        if(valid(token))invalidate(error.message);
        return;
      }
      if(!valid(token)||first!==target.firstElementChild)return;
      let start=0;
      const lines=view.source.split("\n"),rows=target.querySelectorAll(".source-line");
      for(const [line,text] of lines.entries()) {
        const end=start+text.length+1;
        let candidates;
        if(generated) {
          const ranges=(view.contextRanges??[]).filter(range=>range.declarationId
            ?range.entry>=start&&range.entry<end:range.start<end&&range.end>start);
          candidates=listed.filter(point=>ranges.some(range=>range.declarationId?point.declarationId===range.declarationId
            :point.origin.module===range.origin.module&&point.origin.start>=range.origin.start+Math.max(start,range.start)-range.start
              &&point.origin.start<range.origin.start+Math.min(end,range.end)-range.start));
        } else candidates=listed.filter(point=>point.origin.module===module&&point.origin.start>=start&&point.origin.start<end);
        candidates=candidates.filter(point=>point.phase!=="inspection"&&point.origin.end>point.origin.start);
        if(candidates.length) {
          const button=element("button","REPL");button.className="context-entry";button.type="button";
          button.setAttribute("aria-label",`Open contexts at ${generated?"generated ":""}line ${line+1}`);
          button.onclick=()=>{if(valid(token))choose(candidates,`${generated?"Generated":"Source"} line ${line+1}`);};
          rows[line].append(button);
        }
        start=end;
      }
    },
  };
}
