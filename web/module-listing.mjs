// The modules the browser can load, by root, for module-resolution.mjs: every
// module of the rebuilt library, and every module of the archive, entry points
// such as euclid included. The CLI finds the same modules on disk.
import { archiveModules, libraryModules } from "./cubist/modules.mjs";

export const moduleListing = Object.freeze({
  library: Object.freeze([...libraryModules]),
  archive: Object.freeze([...archiveModules]),
});
