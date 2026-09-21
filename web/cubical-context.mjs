// Presentation only: the kernel still checks against the full context.
// Classify by checked binding identity, never by the displayed source name.
export function splitInspectionContext(view, entries = view.context ?? []) {
  const axiomNames = new Set(view.axioms ?? []);
  const context = [], axioms = [];
  for (const entry of entries) {
    const isAxiom = axiomNames.has(entry.name) || axiomNames.has(entry.binding)
      || view.symbols?.[entry.binding]?.kind === "axiom";
    (isAxiom ? axioms : context).push(entry);
  }
  return { context, axioms };
}
