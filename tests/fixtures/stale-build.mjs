// node --import ./tests/fixtures/stale-build.mjs COMMAND runs the command
// with a build stamp that always finds web/dist stale.
import { register } from "node:module";
register("./stale-build-hooks.mjs", import.meta.url);
