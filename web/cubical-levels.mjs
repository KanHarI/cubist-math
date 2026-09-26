// Universe levels in JavaScript syntax (G0). A universe's level is a number,
// the tier-0 constant every universe carried before G0, or an object:
//   { tag: "LConst", tier, value }   the constant ω·tier + value
//   { tag: "LSucc", count, level }   level + count, count ≥ 1
//   { tag: "LMax", left, right }     the larger of two levels
//   { tag: "Var", name }             a universe variable
// The kernel decides equality and order of levels (kernel/src/levels.c);
// these functions only print them.

// A level in kernel notation: 3, ω + 2, ω·2, max(x, 1), x + 1.
export function levelText(level) {
  if (typeof level === "number") return String(level);
  switch (level?.tag) {
    case "LConst": {
      if (!level.tier) return String(level.value);
      const omega = level.tier === 1 ? "ω" : `ω·${level.tier}`;
      return level.value ? `${omega} + ${level.value}` : omega;
    }
    case "LSucc": return `${levelText(level.level)} + ${level.count}`;
    case "LMax": return `max(${levelText(level.left)}, ${levelText(level.right)})`;
    case "Var": return level.name;
    default: return "?";
  }
}

// A universe as the source writes it: U0 and U3 in tier 0, UU0 and UU3 in
// tier 1, one more U per tier; any other level as U(level).
export function universeText(level) {
  if (typeof level === "number") return `U${level}`;
  if (level?.tag === "LConst") return `${"U".repeat(level.tier + 1)}${level.value}`;
  return `U(${levelText(level)})`;
}
