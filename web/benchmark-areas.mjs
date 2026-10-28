// The areas the declaration benchmark measures, as the benchmark page names
// them, and where each one's saved report is, in web/: the archive's keeps the
// name it had. The modules of each are benchmark-runner.mjs's benchmarkAreas.
export const areaLabels = Object.freeze({ library: "Library", archive: "Archive", tests: "Cubist tests" });
export function savedReport(area) {
  return area === "archive" ? "benchmark-results.json" : "benchmark-results-" + area + ".json";
}
export const repository = "https://github.com/KanHarI/cubist-math";
// Where a row's declaration is. A saved report records the revision it
// measured and each module's source path there, so its rows link to that
// source as it was then: the workspace shows today's sources, where a
// declaration measured then may be gone or changed. A run in this browser
// measures today's sources, and its rows open in the workspace.
export function declarationLink(report, row) {
  const path = report.revision && report.sources?.[row.module];
  return path ? `${repository}/blob/${report.revision}/${path}#L${row.line}`
    : `proof.html?proof=${encodeURIComponent(row.module)}&name=${encodeURIComponent(row.name)}`;
}
