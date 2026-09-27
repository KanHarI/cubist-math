// Telemetry for the instruction driver's search (docs/roadmaps/
// learned-search.md, phases 1 and 2): choosers that make another chooser's
// moves while counting or recording them, and kernel work read as
// differences (CubicalKernel.work). Measurement only: a wrapped chooser
// makes exactly the moves of the one it wraps.
import { heuristicChooser } from "../web/cubical-instruction-driver.mjs";

// A move's name: normalize, descend, step:left:beta, step:both:delta,
// whnf:right, eta.
export const moveName = move => move.move === "step" ? `step:${move.side}:${move.rule}`
  : move.side ? `${move.move}:${move.side}` : move.move;

// Kernel steps of either kind.
export const kernelSteps = work => work.instructionSteps + work.querySteps;
// The work done between two readings, and a running total of such.
export const workSince = (before, after) => Object.fromEntries(Object.keys(after).map(key => [key, after[key] - before[key]]));
export function addWork(total, work) {
  for (const key of Object.keys(work)) total[key] = (total[key] ?? 0) + work[key];
  return total;
}

// A chooser making `inner`'s moves, with counts: branch points, listings
// (a point is listed again after a failed normalize or descend), and each
// move's outcomes by name.
export function countingChooser(inner = heuristicChooser) {
  const counts = { points: 0, listings: 0, moves: {} };
  return {
    name: inner.name, counts,
    rank(point) {
      if (point.round === 0) counts.points++;
      counts.listings++;
      return inner.rank(point);
    },
    observe(point, move, outcome) {
      const entry = counts.moves[moveName(move)] ??= {};
      entry[outcome] = (entry[outcome] ?? 0) + 1;
      inner.observe?.(point, move, outcome);
    },
  };
}

// A chooser making `inner`'s moves that records each branch point for
// `sink`, in the order reached: its depth (comparisons nest, as descending
// compares parts), the steps the comparison had taken, the kinds of the two
// heads, and each listing's open moves, the kernel steps spent choosing (the
// guide's queries), and the moves made with their outcomes and kernel steps.
// A move's steps include the comparisons nested in it. Reads the kernel's
// work before and after each move, so it costs more than counting.
export function recordingChooser(inner, kernel, sink) {
  const steps = () => kernelSteps(kernel.work());
  // Each point's record, and the kernel steps when choosing or moving began.
  const open = new WeakMap();
  return {
    name: inner.name,
    *rank(at) {
      let state = open.get(at);
      if (!state) {
        state = { record: { depth: at.depth, taken: at.taken, heads: [at.nx.kind, at.ny.kind], listings: [] } };
        open.set(at, state);
        sink(state.record);
      }
      const listing = { moves: at.moves.map(moveName), choosing: 0, made: [] };
      state.record.listings.push(listing);
      state.mark = steps();
      for (const move of inner.rank(at)) {
        state.before = steps();
        listing.choosing += state.before - state.mark;
        listing.made.push([moveName(move)]);
        yield move;
      }
      listing.choosing += steps() - state.mark;
    },
    observe(at, move, outcome) {
      const state = open.get(at), after = steps();
      state.record.listings.at(-1).made.at(-1).push(outcome, after - state.before);
      state.mark = after;
      inner.observe?.(at, move, outcome);
    },
  };
}
