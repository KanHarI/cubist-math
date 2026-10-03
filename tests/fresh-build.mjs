// Imported first by every test file that loads web/dist, directly or through
// the modules it imports, so that a test file run on its own, with node or
// node --test, refuses a stale build as tools/test.mjs does
// (tools/build-stamp.mjs). tests/fresh-build.test.mjs checks that each such
// file imports it.
import { assertFreshBuild } from "../tools/build-stamp.mjs";
assertFreshBuild();
