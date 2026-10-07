// The areas the declaration benchmark measures, as the benchmark page names
// them, and where each one's saved report is, in web/: the archive's keeps the
// name it had. The modules of each are benchmark-runner.mjs's benchmarkAreas.
export const areaLabels = Object.freeze({ library: "Library", archive: "Archive", tests: "Cubist tests" });
export function savedReport(area) {
  return area === "archive" ? "benchmark-results.json" : "benchmark-results-" + area + ".json";
}
