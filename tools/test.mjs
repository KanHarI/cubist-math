import { spawn, execFileSync } from "node:child_process";
import { access } from "node:fs/promises";
import { selectTests, projectRoot, help } from "./test-selection.mjs";

try {
  const selected = selectTests(process.argv.slice(2));
  if (selected.help) {
    process.stdout.write(help);
  } else if (!selected.tests.length) {
    process.stdout.write("No added or modified .cubist files to check.\n");
  } else {
    await Promise.all([...selected.tests, ...selected.proofs].map(path => access(path)));
    // Native protocol tests share executables. Build before Node launches test
    // files concurrently: a clean checkout must not race missing/half-built files.
    if (selected.tests.some(path => path.startsWith(projectRoot + "lib/cubical/tests/")))
      execFileSync("make", ["-C", "kernel", "all"], { cwd: projectRoot, stdio: "inherit" });
    const environment = { ...process.env, MATHSCRIPT_TEST_PROOFS: JSON.stringify(selected.proofs), MATHSCRIPT_OPTIMIZATIONS: JSON.stringify(selected.optimizations) };
    // A nested invocation must start its own Node test run, not inherit the
    // parent runner's internal child-process protocol.
    delete environment.NODE_TEST_CONTEXT;
    const child = spawn(process.execPath, ["--test", ...selected.flags, ...selected.tests], {
      cwd: projectRoot,
      stdio: "inherit",
      env: environment,
    });
    child.on("error", error => { process.stderr.write(`${error.message}\n`); process.exitCode = 1; });
    child.on("exit", (code, signal) => {
      if (signal) process.stderr.write(`Test process stopped by ${signal}.\n`);
      process.exitCode = code ?? 1;
    });
  }
} catch (error) {
  process.stderr.write(`${error.message}\nRun npm test -- --help for usage.\n`);
  process.exitCode = 1;
}
