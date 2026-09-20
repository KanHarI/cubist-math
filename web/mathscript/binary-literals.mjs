// Literal notation expands to checked library constructors, never to unary Nat
// or a JavaScript-computed proof. Keep digit strings exact beyond 2^53.
export function binaryLiteralSyntax(node) {
  const name = text => ({ kind: "name", name: text, start: node.start, end: node.end, library: true });
  const call = (text, arg) => ({ kind: "call", fn: name(text), args: [arg],
    start: node.start, end: node.end, library: true });
  if (node.digits === "0") return name("binary_zero");
  let positive = name("binary_one");
  for (const bit of node.digits.slice(1))
    positive = call(bit === "0" ? "binary_bit0" : "binary_bit1", positive);
  return call("binary_positive", positive);
}

export function binaryLiteralExpansion(node) {
  const print = n => n.kind === "name" ? n.name : `${n.fn.name}(${print(n.args[0])})`;
  return print(binaryLiteralSyntax(node));
}
