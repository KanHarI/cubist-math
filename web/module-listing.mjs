// The modules the browser can load, by root, for module-resolution.mjs: every
// module of the rebuilt library, every module of the archive, entry points
// such as euclid included, and every Cubist test. The CLI finds the same
// modules on disk.
import { archiveModules, cubistTestModules, libraryModules } from "./cubist/modules.mjs";

export const moduleListing = Object.freeze({
  library: Object.freeze([...libraryModules]),
  archive: Object.freeze([...archiveModules]),
  tests: Object.freeze([...cubistTestModules]),
});
