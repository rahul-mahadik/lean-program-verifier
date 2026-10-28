# Lean Program Verifier

An imperative-program verifier in Lean. The `MiniVerify` library contains
a proved verification-condition generator and an executable interpreter.

## Guarantees

For every supported command, state type, initial state, and postcondition,
discharged verification conditions imply:

- A finite successful execution satisfying the postcondition exists.
- Every sufficiently large interpreter budget returns that final state.
- No interpreter budget reports a runtime fault.

`vcgen_sound` proves total-correctness soundness. `verified_execution`
connects it to the interpreter. Execution is deterministic, and `run_sound`
connects interpreter success to the same big-step semantics.

Loop invariants and termination variants are ghost annotations: execution
does not consult them. The generator produces logical obligations to prove
in Lean; it does not automatically decide arbitrary specifications.

## Verified algorithms

All three are loop programs verified for arrays of arbitrary length.

- Binary search returns an index containing the target, or `none` exactly
  when it is absent, assuming nondecreasing input. Midpoint reads are
  checked; the termination variant is `hi - lo`.
- Reversal returns exactly the reversed input with the same length.
  It uses checked two-ended swaps and the variant `size / 2 - index`.
- Insertion sort returns a nondecreasing permutation of arbitrary input.
  It uses nested loops and checked adjacent swaps, with variants
  `size - i` and `j`. It calls no high-level sorting operation.

## Interfaces

The algorithms use `Cmd σ`, where typed record fields represent registers
and arrays. `Language.Stmt` supplies a named-variable frontend with integer
expressions, arrays, assignments, checked reads and writes, conditionals,
sequencing, and annotated loops. It rejects negative and oversized indices
and supports short-circuit Boolean conjunction. Both interfaces use the
same verifier and interpreter through `Language.lower`.

See [DESIGN.md](DESIGN.md) for semantics and VC rules, and
[TUTORIAL.md](TUTORIAL.md) for adding a verified program.

## Build and run

Install `elan`, a C toolchain, and Python 3. The project pins Lean
`v4.14.0` and its Mathlib revision in the toolchain and Lake configuration.

```sh
lake exe cache get
lake build MiniVerify miniverify MiniVerify.Tests
lake exe miniverify demo
```

```sh
lake exe miniverify reverse 1 -2 3 4 5
lake exe miniverify sort 5 2 4 2 -1
lake exe miniverify search 4 -1 2 2 4 5
```

The CLI checks binary search's sorted-input premise with a proved checker.
That validation is quadratic; the search loop uses midpoint reduction.
The CLI uses a finite budget and distinguishes timeout from fault. The
proofs guarantee a sufficient budget, without a tight complexity bound
for the CLI's default budget.

## Verification

```sh
./scripts/verify.sh
```

The script builds the project, checks exact regressions, runs the demo and
CLI tests, prints axiom dependencies, and scans project Lean sources for
proof holes and additional axioms. Reports are in
[verification/](verification/), including [audit.json](verification/audit.json),
[axioms.txt](verification/axioms.txt), and [cli-tests.json](verification/cli-tests.json).
Exact positive and adversarial cases are in [Tests.lean](MiniVerify/Tests.lean).

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
It rejects unfinished proofs and custom axioms in project Lean sources.

## Scope

Integers are unbounded mathematical integers. Writes and swaps preserve
array length. “In-place” describes single-array updates in this model;
no machine allocation or constant-memory bound is proved. Faults return
no final store or partial execution trace.

The proofs concern the defined Lean semantics. Running the native CLI
also relies on the Lean compiler, runtime, and host toolchain. This project
does not verify translations of C, Python, or Rust source.
