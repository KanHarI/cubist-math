// Small, per-tab snapshots preserve inspector selections across source files.
// They contain UI state only; returning to a proof still checks its source.
const prefix = "mathscript:navigation:";
export function readProofNavigation(key) {
  try { return key ? JSON.parse(sessionStorage.getItem(prefix + key)) : null; }
  catch { return null; }
}
export function saveProofNavigation(snapshot) {
  const key = crypto.randomUUID();
  sessionStorage.setItem(prefix + key, JSON.stringify(snapshot));
  return key;
}
export function proofReturnURL(key) {
  const saved = readProofNavigation(key);
  if (!saved?.proof) return null;
  const url = new URL("proof.html", location.href);
  url.searchParams.set("proof", saved.proof);
  url.searchParams.set("restore", key);
  if (["cubical", "legacy"].includes(saved.backend)) url.searchParams.set("backend", saved.backend);
  return url.href;
}
export function validatedProofURL(value) {
  try {
    const url = new URL(value, location.href);
    return url.origin === location.origin && url.pathname === new URL("proof.html", location.href).pathname
      ? url.href : null;
  } catch { return null; }
}
