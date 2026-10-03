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

// A level with each universe variable renamed, for printing under the same
// renaming as the term around it.
export function renameLevel(level, rename) {
  switch (level?.tag) {
    case "Var": return { ...level, name: rename(level.name) };
    case "LSucc": return { ...level, level: renameLevel(level.level, rename) };
    case "LMax": return { ...level, left: renameLevel(level.left, rename), right: renameLevel(level.right, rename) };
    default: return level;
  }
}

// A universe as the source writes it (G0 §1.4): U0 and U3 in tier 0, UU0
// and UU3 in tier 1, one more U per tier; a universe variable by its name;
// next(E) for a successor and max(E, F) for a maximum.
export function universeText(level) {
  if (typeof level === "number") return `U${level}`;
  switch (level?.tag) {
    case "LConst": return `${"U".repeat(level.tier + 1)}${level.value}`;
    case "Var": return level.name;
    case "LSucc": {
      let text = universeText(level.level);
      for (let i = 0; i < level.count; i++) text = `next(${text})`;
      return text;
    }
    case "LMax": return `max(${universeText(level.left)}, ${universeText(level.right)})`;
    default: return "U?";
  }
}

// The normal form of a kernel level node (G0 §2.4), read with read(id), which
// gives { kind, payload, children }: { tier, constant, offsets }, offsets
// mapping each variable's symbol to its offset. A finite form has tier 0; a
// constant of tier 1 or above has no variables. The kernel decides levels;
// the instruction driver uses this only to steer.
export function levelNormal(read, id) {
  const node = read(id);
  switch (node.kind) {
    case "LConst": return { tier: node.payload >>> 16, constant: node.payload & 0xffff, offsets: new Map() };
    case "Var": return { tier: 0, constant: 0, offsets: new Map([[node.payload, 0]]) };
    case "LSucc": {
      const inner = levelNormal(read, node.children[0]);
      return { tier: inner.tier, constant: inner.constant + node.payload,
        offsets: new Map([...inner.offsets].map(([key, offset]) => [key, offset + node.payload])) };
    }
    case "LMax": {
      const a = levelNormal(read, node.children[0]), b = levelNormal(read, node.children[1]);
      if (a.tier || b.tier) {
        const larger = !a.tier ? b : !b.tier ? a : a.tier > b.tier || (a.tier === b.tier && a.constant >= b.constant) ? a : b;
        return { tier: larger.tier, constant: larger.constant, offsets: new Map() };
      }
      const offsets = new Map(a.offsets);
      for (const [key, offset] of b.offsets) offsets.set(key, Math.max(offset, offsets.get(key) ?? 0));
      return { tier: 0, constant: Math.max(a.constant, b.constant), offsets };
    }
    default: throw new Error(`Expected a level, not ${node.kind}.`);
  }
}
