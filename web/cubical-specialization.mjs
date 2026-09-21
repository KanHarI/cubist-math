import { cubicalMathTree } from "./cubical-notation.mjs";
import { renderMathNotation } from "./math-notation.mjs";

// This panel explains elaboration provenance. Its generic schema is deliberately
// separated from the checked kernel expression and its native assembly.
export function renderSpecialization(container, view, { jump, listing } = {}) {
  container.replaceChildren();
  const origin = view.expression.tag === "Var" && view.expression.name === view.specialization?.binding
    ? view.specialization : null;
  container.hidden = !origin;
  if (!origin) return;
  const doc = container.ownerDocument;
  const el = (tag, text) => { const node = doc.createElement(tag); if (text) node.textContent = text; return node; };
  container.append(el("h3", "Universe specialization"));
  const route = el("p", `${origin.schema}(U) → U := ${origin.universe} → ${origin.schema}(${origin.universe})`);
  route.className = "specialization-route";
  container.append(route, el("p", `The elaborator substitutes ${origin.universe} for the universe parameter U. The kernel receives the resulting signature as an explicit assumption (CC_VAR), not an application of a universe-generic kernel term. This is an axiom instance, not a proved theorem.`));
  const details = el("details"), summary = el("summary", "Generic schema signature (elaborator notation)");
  const schema = el("div"); schema.className = "kernel-term typeset";
  renderMathNotation(schema, cubicalMathTree(origin.schemaType), { identitySugar: true });
  details.append(summary, el("p", "U is a schema parameter. Fixed universe levels, such as the U0 result of Truncate, are not substituted."), schema);
  container.append(details);
  const signature = el("details");
  signature.append(el("summary", `Specialized checked signature at ${origin.universe}`));
  const type = el("div"); type.className = "kernel-term typeset";
  renderMathNotation(type, cubicalMathTree(view.type, view.symbols), {
    resolve: binding => view.symbols[binding], identitySugar: true, truncationSugar: false,
  });
  signature.append(type); container.append(signature);
  if (listing && jump) {
    const roots = el("p", "Native assembly: ");
    for (const root of listing.roots.filter(root => ["Expression", "Checked type"].includes(root.label))) {
      const button = el("button", `${root.label} %${root.handle}`); button.className = "assembly-reference";
      button.dataset.specializationHandle = String(root.handle); button.onclick = () => jump(root.handle);
      roots.append(button, " ");
    }
    container.append(roots);
  }
  if (origin.mentions.length) {
    const links = el("ul");
    for (const mention of origin.mentions) {
      const row = el("li"), link = el("a", `${origin.schema}(${mention.universe}, …) in ${mention.module}.${mention.declaration}`);
      link.href = `proof.html?proof=${encodeURIComponent(mention.module)}&name=${encodeURIComponent(mention.declaration)}`;
      link.title = mention.expression; row.append(link); links.append(row);
    }
    container.append(el("p", `Explicit source uses at ${origin.universe} (open the containing declaration):`), links);
  }
  const implementation = el("a", "Read the schema implementation");
  implementation.href = `https://github.com/KanHarI/cubist-math/blob/main/${origin.implementation}`;
  container.append(implementation);
}
