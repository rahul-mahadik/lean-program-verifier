# Annotation synthesis benchmark

An LLM proposes a loop invariant and a natural-number termination variant.
Lean checks the resulting verification conditions and derives total
correctness, eventual interpreter success, and absence of faults.

The twelve cases in [cases.json](benchmarks/cases.json) range from linear
counters and transfers to repeated-addition multiplication, triangular
sums, and squares. Programs, initial states, preconditions, and
postconditions are fixed in [Benchmarks.lean](MiniVerify/Benchmarks.lean).
Inputs `n` and `m` are arbitrary natural numbers; these are universal
proofs, not execution tests on a finite set of inputs.

## Protocol

Each first attempt starts a fresh Codex CLI process with an empty working
directory. Its prompt contains one case, the expression grammar, and the
response schema. No reference annotations or existing algorithm proofs
are included. User configuration, project instructions, bundled skills,
and supported tool features are disabled. Only model message and reasoning
items are accepted in the recorded event stream; any recorded tool use
invalidates the attempt. This audits observed use rather than establishing
an operating-system boundary against all file reads.

The model returns three strings: `invariant`, `variant`, and `solver`.
Expressions use a restricted Python-style grammar over `n`, `m`, and
`s.x`, `s.y`, `s.z`, `s.n`, `s.m`, `s.i`. Supported operations are `+`,
`-`, `*`, `//`, `%`, comparisons, and `and`/`or`/`not`. Numerals are
nonnegative; subtraction truncates at zero. Division and remainder use
Lean's Nat conventions, including division by zero. Calls, imports,
quantifiers, arbitrary Lean, and model-written tactics are rejected.

The solver field selects one of two fixed arithmetic recipes, using
`omega` or `omega`/`nlinarith` after normalization. The model proposes
annotations and selects a recipe; the trusted checker constructs the
proof. Acceptance requires a successful Lean process and axiom reports
for both the VC theorem and the execution theorem, containing only
`propext`, `Classical.choice`, and `Quot.sound`.

The attempt budget is fixed before collection. A failed candidate gets
one repair attempt containing the previous candidate and Lean diagnostics.
There are no manual candidate repairs. Every selected program remains in
the denominator, including malformed responses, timeouts, and failures.
First-attempt and within-budget counts are reported separately; these are
observed counts, not statistical pass-at-k estimates.

## Run

Install and sign in to the Codex CLI locally, and complete the Lean setup
in the main README. This uses saved local CLI authentication; credentials
are never copied into the project or benchmark artifacts. Choose a model
available to your account explicitly so the report records the requested
model identifier. The CLI does not expose an immutable backend snapshot.

```sh
lake build MiniVerify.Benchmarks
python3 scripts/llm_benchmark.py run --model YOUR_MODEL --effort medium \
  --max-attempts 2 --output benchmarks/runs/my-run
```

Each attempt saves its prompt, raw model response, JSON event stream,
provider diagnostics, generated Lean source, Lean diagnostics, and result.
The report records the model identifier, reasoning effort, CLI version
and binary hash, timings, usage, budgets, and source fingerprints.

Replay checks the saved responses without calling a model. Use the source
revision from the original run; fingerprints must match.

```sh
python3 scripts/llm_benchmark.py replay --run benchmarks/runs/my-run \
  --output benchmarks/replays/my-run
```

Hand-written [reference annotations](benchmarks/reference.json) are a
separate positive control, never model successes:

```sh
python3 scripts/llm_benchmark.py reference --output benchmarks/controls/my-control
MINIVERIFY_LEAN_INTEGRATION=1 python3 -m unittest discover -s tests
```

The integration tests also require rejection of a weak invariant and a
constant variant. Unit tests exercise injection attempts, timeouts,
unexpected axioms, missing proof reports, and forbidden model tool use.

## Interpretation

This is a small, self-authored suite of familiar arithmetic loops. The
annotation grammar and arithmetic tactics constrain the search space.
There is no held-out dataset, comparison against other synthesis systems,
or evidence of generalization to arrays, nested loops, or arbitrary
programs. The original manually verified array algorithms are separate
from this benchmark.

Codex runner behavior follows the [official noninteractive-mode
documentation](https://learn.chatgpt.com/docs/non-interactive-mode).
