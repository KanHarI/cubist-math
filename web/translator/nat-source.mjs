// The source of the prelude module `nat` (library/nat.cubist),
// which CubicalProgram loads for a reader with no library.
// tests/cubical-program.test.mjs checks that it is that file.
export default "// Natural numbers, defined and checked from source like any other data type.\ninductive Nat : U0 {\n  zero;\n  succ(n : Nat);\n}\n";
