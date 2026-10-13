const assertion = error => !!error && (error.code === "ERR_ASSERTION" || assertion(error.cause));
const precondition = error => !!error && (error.code === "ERR_TEST_PRECONDITION" || precondition(error.cause));

export function testResults(run) {
  let events;
  try { events = run.log.trim().split("\n").filter(Boolean).map(line => JSON.parse(line)); }
  catch { return { invalid: "invalid test event stream", passed: [], failed: [] }; }
  const selected = events.filter(event => ["test:pass", "test:fail"].includes(event.type) && !event.todo && !event.skip);
  const failed = selected.filter(event => event.type === "test:fail" && event.error?.failureType !== "subtestsFailed");
  const passed = selected.filter(event => event.type === "test:pass").map(event => event.name);
  const summary = events.findLast(event => event.type === "test:summary" && !event.file);
  const invalid = run.error || run.signal || !summary && "incomplete test run"
    || summary.counts.cancelled && "cancelled tests"
    || (run.status === 0) !== summary.success && "process status disagrees with test summary"
    || !selected.length && "no active tests" || failed.some(event => !assertion(event.error)) && "non-assertion failure"
    || run.status !== 0 && !failed.length && "process failure without an assertion test";
  return { invalid, passed, failed: failed.map(event => ({ name: event.name, assertion: assertion(event.error),
    precondition:precondition(event.error) })), events };
}

export function mutationOutcome(run, distinguishingTests) {
  const result = testResults(run);
  if (result.invalid) return { outcome: "invalid", failedTests: [], reason: String(result.invalid) };
  if (run.status === 0) return { outcome: "survived", failedTests: [] };
  const failedTests = result.failed.map(event => event.name);
  if (failedTests.some(name => !distinguishingTests.includes(name)))
    return { outcome: "invalid", failedTests, reason: "failure outside the passing distinguishing tests" };
  if (result.failed.some(test => test.precondition)) return {outcome:"precondition", failedTests,
    reason:"a fixture precondition failed before its semantic clients could be checked"};
  return { outcome: "killed", failedTests };
}
