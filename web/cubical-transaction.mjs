// One native declaration checkpoint plus the JavaScript state tied to its
// handles. Matchers construct syntax but never commit a proof themselves.
export class CubicalDeclarationTransaction {
  constructor(kernel, checker) {
    this.kernel = kernel;
    this.checker = checker;
    this.sizes = new Map([
      [kernel.definitions,kernel.definitions.size],
      // Definition and signature indices survive a commit and are freed by a
      // rollback, and so are the names the driver keeps by them.
      [kernel.definitionNames,kernel.definitionNames.size],
      [kernel.signatures,kernel.signatures.size],
      [kernel.signatureRecords,kernel.signatureRecords.size],
      [checker.definitionViews,checker.definitionViews.size],
      [checker.genericDefinitions,checker.genericDefinitions.size],
      [checker.definitionExtensions,checker.definitionExtensions.size],
      [checker.inductives,checker.inductives.size],
      [checker.scopeDefinitions,checker.scopeDefinitions.size],
      [checker.assumptions,checker.assumptions.size],
      [checker.assumptionLabels,checker.assumptionLabels.size],
      [checker.assumptionOrigins,checker.assumptionOrigins.size],
      [checker.axioms,checker.axioms.size],
      [checker.libraryAssumptions,checker.libraryAssumptions.size],
    ]);
    // These maps contain frontend metadata as well as identities. Snapshot
    // values too: removing only new keys cannot undo an updated record.
    this.metadata = new Map([checker.theories,checker.theoryProjections,checker.notationPrinting]
      .filter(Boolean).map(collection => [collection,new Map(collection)]));
    kernel.module._cb_checkpoint(kernel.handle);
    // Both the commit and the rollback truncate the context entries to their
    // count at the checkpoint; the driver's names for them go too.
    this.entries = kernel.module._cb_entry_count(kernel.handle) >>> 0;
    // Nodes from this handle on are made after the checkpoint: a commit
    // moves them and a rollback drops them, and the binders' names with them.
    this.nodes = kernel.arena().nodes + 1;
    this.active = true;
  }
  added(collection) {
    return [...collection.keys()].slice(this.sizes.get(collection));
  }
  finish(accept) {
    if (!this.active) throw Error("Declaration transaction was already finished.");
    this.active = false;
    const {kernel,checker} = this;
    const definitions = this.added(kernel.definitions);
    if (accept) {
      if (!kernel.module._cb_commit_checkpoint(kernel.handle)) throw Error(kernel.error());
      for (const name of definitions) {
        const handle=kernel.definitions.get(name);
        kernel.definitions.set(name,kernel.module._cb_relocated(kernel.handle,handle));
      }
      // A binder kept by the commit keeps the name it was encoded with, and
      // the key its entries are chosen by.
      for (const map of [kernel.binderNames, kernel.binderKeys]) {
        const moved = [...map].filter(([handle]) => handle >= this.nodes);
        for (const [handle] of moved) map.delete(handle);
        for (const [handle, name] of moved) {
          const kept = kernel.module._cb_relocated(kernel.handle, handle) >>> 0;
          if (kept && !map.has(kept)) map.set(kept, name);
        }
      }
    } else {
      kernel.module._cb_rollback(kernel.handle);
      for (const [collection,snapshot] of this.metadata) {
        collection.clear(); for (const [key,value] of snapshot) collection.set(key,value);
      }
      for (const collection of this.sizes.keys())
        for (const key of this.added(collection)) collection.delete(key);
      for (const map of [kernel.binderNames, kernel.binderKeys])
        for (const handle of map.keys()) if (handle >= this.nodes) map.delete(handle);
    }
    // Handles from here on are new nodes, none of them shown yet.
    for (const handle of kernel.binderNames.shownUnnamed ?? []) if (handle >= this.nodes) kernel.binderNames.shownUnnamed.delete(handle);
    kernel.entryNames.truncate(this.entries);
    checker.syntax.reset();
    kernel.forgetNodes();
    // Its judgements were truncated with the checkpoint, and handles moved.
    kernel.instructionDriver = null;
    kernel.derivedHandles = null;
  }
}
