export const referenceKey = node => node.kind === "name" ? node.name : null;

// Display provenance is independent of resolution. A structural selection
// can still name its written receiver in diagnostics after it is moved.
export const sourceName = node => node.spelling ?? (node.kind === "notationReceiver" ? sourceName(node.notation)
  : node.kind === "name" ? node.name
  : node.kind === "member" && sourceName(node.value) ? `${sourceName(node.value)}.${node.field.text}` : null);

// A field selection keeps its receiver as syntax. In particular, a local
// T's T.M cannot be confused with the declaration whose qualified name is T.M.
export function members(node, receiver, fields) {
  const dots = node.qualifiedDots ?? (node.qualifiedDot ? [node.qualifiedDot] : []);
  let value = receiver, end = receiver.end;
  for (const [index, text] of fields.entries()) {
    const start = dots[index]?.end ?? end + 1;
    end = start + text.length;
    value = {kind: "member", value, field: {text, start, end,...(node.origin?{origin:{...node.origin,start,end}}:{}),
      ...(node.synthetic?{synthetic:true}:{})}, start: node.start, end,
      ...(node.origin?{origin:node.origin}:{}),
      ...(node.synthetic ? {synthetic: true} : {})};
  }
  return value;
}
