// JSON has no references: serializing a compact checked DAG can expand it
// exponentially. Stop before a raw inspector view allocates that tree.
export const syntaxDisplayLimitMessage =
  "Raw syntax exceeds the display limit. Inspect a smaller expression or use mathematical notation.";

export function boundedSyntaxJson(value, { maxNodes = 20000, maxCharacters = 1000000, maxDepth = 512 } = {}) {
  const limit = new Error("Syntax display limit");
  const depths = new WeakMap();
  let nodes = 0, estimatedCharacters = 0;
  try {
    const result = JSON.stringify(value, function (key, item) {
      const depth = (depths.get(this) ?? -1) + 1;
      if (depth > maxDepth) throw limit;
      if (item && typeof item === "object") {
        if (++nodes > maxNodes) throw limit;
        depths.set(item, depth);
      }
      // JSON escaping can use six characters per source character. Include
      // indentation and punctuation, then verify the actual result as well.
      estimatedCharacters += 20 + 4 * depth + 6 * (key.length +
        (typeof item === "string" ? item.length : 0));
      if (estimatedCharacters > maxCharacters) throw limit;
      return item;
    }, 2);
    return result.length <= maxCharacters ? result : null;
  } catch (error) {
    if (error === limit) return null;
    throw error;
  }
}
