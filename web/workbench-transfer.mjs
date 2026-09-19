// Same-origin, one-shot transfers avoid sessionStorage's small string quota.
// The workbench still replays every instruction before accepting the document.
function database() {
  return new Promise((resolve, reject) => {
    const request = indexedDB.open("thth-workbench-transfers", 1);
    request.onupgradeneeded = () => request.result.createObjectStore("proofs");
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}
async function transaction(mode, action) {
  const db = await database();
  try {
    return await new Promise((resolve, reject) => {
      const tx = db.transaction("proofs", mode);
      const request = action(tx.objectStore("proofs"));
      tx.oncomplete = () => resolve(request.result);
      tx.onabort = tx.onerror = () => reject(tx.error ?? request.error);
    });
  } finally { db.close(); }
}
export async function saveWorkbenchTransfer(payload) {
  const key = crypto.randomUUID();
  await transaction("readwrite", store => store.put(payload, key));
  return key;
}
export async function readWorkbenchTransfer(key) {
  const payload = await transaction("readonly", store => store.get(key));
  if (!payload) throw new Error("This expression transfer is no longer available. Open it again from the proof inspector.");
  return payload;
}
export function removeWorkbenchTransfer(key) {
  return transaction("readwrite", store => store.delete(key));
}
