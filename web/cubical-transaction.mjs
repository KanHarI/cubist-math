// One native declaration checkpoint plus the JavaScript state tied to its
// handles. Matchers construct syntax but never commit a proof themselves.
export class CubicalDeclarationTransaction {
  constructor(kernel, checker) {
    this.kernel = kernel;
    this.checker = checker;
    this.sizes = new Map([
      [kernel.definitions,kernel.definitions.size],
      [checker.definitionViews,checker.definitionViews.size],
      [checker.schemaSpecializations,checker.schemaSpecializations.size],
      [checker.schemaSourceNames,checker.schemaSourceNames.size],
      [checker.scopeDefinitions,checker.scopeDefinitions.size],
      [checker.assumptions,checker.assumptions.size],
      [checker.assumptionLabels,checker.assumptionLabels.size],
      [checker.assumptionOrigins,checker.assumptionOrigins.size],
      [checker.libraryAssumptions,checker.libraryAssumptions.size],
    ]);
    this.hints = [...kernel.unfoldingHints];
    kernel.module._cb_checkpoint(kernel.handle);
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
    } else {
      kernel.module._cb_rollback(kernel.handle);
      for (const collection of this.sizes.keys())
        for (const key of this.added(collection)) collection.delete(key);
      kernel.unfoldingHints = [];
      if (this.hints.length) kernel.setUnfoldingHints(this.hints);
    }
    checker.syntax.reset();
    // Its judgements were truncated with the checkpoint, and handles moved.
    kernel.instructionDriver = null;
    kernel.derivedHandles = null;
  }
}
