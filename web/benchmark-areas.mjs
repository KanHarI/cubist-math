// The areas the declaration benchmark measures, as the benchmark page names
// them, and where each one's saved report is, in web/: the archive's keeps the
// name it had. The modules of each are benchmark-runner.mjs's benchmarkAreas.
export const areaLabels = Object.freeze({ library: "Library", archive: "Archive", tests: "Cubist tests" });
export function savedReport(area) {
  return area === "archive" ? "benchmark-results.json" : "benchmark-results-" + area + ".json";
}
export const repository = "https://github.com/KanHarI/cubist-math";
// Where a row's declaration is. A saved report records the revision it
// measured and, for each module it measured exactly as committed there, the
// source's path (tools/benchmark-cubical.mjs's pinnedSources): its rows link
// to that source as it was then, since the workspace shows today's sources,
// where a declaration measured then may be gone or changed. A row of a module
// measured from working changes has no link (null): no committed source is
// the one measured. A run in this browser measures today's sources, and its
// rows open in the workspace.
export function declarationLink(report, row) {
  if (!report.revision) return `proof.html?proof=${encodeURIComponent(row.module)}&name=${encodeURIComponent(row.name)}`;
  const source = report.sources?.[row.module];
  return source ? `${repository}/blob/${report.revision}/${source.path}#L${row.line}` : null;
}
