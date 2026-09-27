// The instruction driver's exact behaviour on a fixture, independent of its
// chooser interface: every instruction it issues, with its operands, and every
// weak-head query its guide asks, in order. tests/driver-search.test.mjs
// compares this with a trace recorded from the driver before the choices
// were made explicit (tests/fixtures/driver-trace.json). The fixture covers
// normalizing a long closed computation, failed congruence, one-sided and
// two-sided unfolding, and weak heads that do not compute.
//   node tests/driver-trace.mjs [ROOT]   prints the trace summary for the tree at ROOT
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { pathToFileURL, fileURLToPath } from "node:url";

const repository = new URL("../", import.meta.url);
export const traceSource = `import naturals;

def lt(n, m : Nat) : U0 {
  exact exists k : Nat. succ(k) + n = m;
}

def lt_succ(n : Nat) : lt(n, succ(n)) {
  exact (0, refl(succ(n)));
}

def exists_greater_number : forall n : Nat. exists m : Nat. lt(n, m) {
  intro n;
  exact (succ(n), lt_succ(n));
}

def double(n : Nat) := n + n;
def twice(n : Nat) := double(n);
def twice_is_double(n : Nat) : twice(n) = double(n) {
  rfl;
}

def product : 12 * 12 = 144 {
  rfl;
}

def shifted(a, b : Nat) : (a + 0) + b = a + b {
  rw [nat_add_zero(a)];
}
`;

// `root` is a checkout's directory URL; its web/dist must be built.
export async function driverTrace(root = repository) {
  const load = path => import(new URL(path, root).href);
  const [{ default: createCubical }, { CubicalProgram }, { InstructionGraph }] = await Promise.all([
    load("web/dist/cubical.mjs"), load("web/cubical-program.mjs"), load("web/cubical-instructions.mjs")]);
  const hash = createHash("sha256"), counts = { issued: 0, heads: 0 };
  const { issue, head } = InstructionGraph.prototype;
  InstructionGraph.prototype.issue = function (name, ...operands) {
    counts.issued++;
    let result;
    try { result = issue.call(this, name, ...operands); }
    catch (error) { hash.update(`issue ${name} ${operands.join(",")} ! ${error.message}\n`); throw error; }
    hash.update(`issue ${name} ${operands.join(",")} = ${result}\n`);
    return result;
  };
  InstructionGraph.prototype.head = function (term, steps) {
    counts.heads++;
    const result = head.call(this, term, steps);
    hash.update(`head ${term} ${steps} = ${result}\n`);
    return result;
  };
  const read = path => readFile(new URL(path, repository), "utf8");
  const readLibrary = name => read(`library/${name}.cubist`)
    .catch(error => { if (error.code !== "ENOENT") throw error; return read(`archive/first-library/${name}.cubist`); });
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  try {
    const result = await program.check(traceSource, "trace");
    const failed = result.outputs.filter(output => !output.verified).map(output => `${output.name}: ${output.reason}`);
    return { ...counts, checked: result.outputs.length - failed.length, failed, sha256: hash.digest("hex") };
  } finally {
    program.dispose();
    Object.assign(InstructionGraph.prototype, { issue, head });
  }
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const root = process.argv[2] ? pathToFileURL(`${process.argv[2].replace(/\/$/, "")}/`) : repository;
  console.log(JSON.stringify(await driverTrace(root), null, 2));
}
