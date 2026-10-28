# Semantics and proof design

## Commands and execution

`Cmd σ` has skip, partial primitive actions, sequencing, partial Boolean
tests, and while loops. A typed record supplies the state. This makes
the core reusable across independent program representations.

`Exec c s t` is an inductive big-step relation. Its action constructor
requires `step s = some t`; tests must evaluate to `some true` or
`some false`. The while rules are the ordinary exit rule and a body
execution followed by the remaining loop. Invariants and ranks occur
only as syntax annotations and impose no restriction on execution.

The interpreter returns one of `done state`, `fault`, or `timeout`.
Fuel bounds recursion depth, including sequence and loop recursion. It
is not a count of machine instructions. `Exec.run_result` proves that a
normal execution permits only timeout or the same final state at every
budget; `Exec.run_complete` supplies a bound above which it succeeds.
`run_sound` proves the converse direction for successful runs.

## VC rules

For a postcondition `Q`, `vcgen c Q` is a sufficient precondition:

- Skip produces `Q`.
- A primitive action produces `∃ t, step s = some t ∧ Q t`.
- Sequencing produces `vcgen first (vcgen second Q)`.
- A conditional requires safe test evaluation and the corresponding
  branch's generated condition.
- A while loop requires its invariant initially and the following
  obligations for **every** invariant state: the test succeeds; exit
  implies `Q`; continuing requires the body's generated conditions
  for invariant preservation and strict decrease of a natural variant.

The universal invariant-state clause is essential. Checking only the
initial state would miss later failures and would not establish a loop
induction rule.

`whileLocal` additionally lets the invariant refer to the immutable
state at loop entry. Its condition at initial state `s` uses the fixed
predicate `invariant s` throughout the proof. This supplies the frame
needed by insertion sort's inner loop: the insertion index `j` changes,
while the current outer index `i` remains equal to its entry value.

## Total-correctness proof

The theorem `vcgen_sound` proceeds by structural induction on commands.
The sequence case composes two successful executions. The conditional
case follows the safely evaluated branch. The loop cases use strong
induction on the natural variant: generated body conditions give a
successful body execution and a strictly smaller variant, allowing
the remaining execution to be constructed.

This proves termination as well as the postcondition. Interpreter
correspondence then establishes `verified_execution`: all sufficiently
large budgets succeed with the proved postcondition, and no budget
faults. The theorem is polymorphic over the state type and quantifies
over all commands and postconditions.

## Concrete language

`Language.Store` supplies named integer registers and named arrays.
Expression evaluation returns `Option`; negative array indices are
rejected before conversion to naturals. Array reads use checked option
lookup. Writes evaluate their index and value before any store update,
then check nonnegativity and bounds. Boolean conjunction short-circuits.

`lower` maps this explicit statement AST to core commands. Both
`Language.conditions` and `Language.run` use that same lowering, so its
public soundness theorem applies to the executable representation.

The larger examples instead use the typed `Cmd State` interface. Their
primitive functions perform only the indicated counter updates, checked
reads, and swaps. Their loop bodies do not call library search,
reversal, or sorting implementations.

## Algorithm invariants

Binary search maintains `0 ≤ lo ≤ hi ≤ size`, immutable input, values
left of `lo` below the target, and values at or right of `hi` at least
the target. Monotonicity of sorted input preserves these exclusions at
the midpoint. The measure `hi - lo` strictly decreases.

Reversal maintains exactly which array cells have reached their reversed
positions, with the untouched middle still equal to the original. A
checked swap grows the two completed ends and decreases the remaining
pair count. The invariant covers empty, singleton, odd, and even arrays.

Insertion sort's outer invariant is a sorted prefix and a permutation of
the original input. The inner invariant omits the moving key from the
prefix order, tracks that the key is below the suffix it has passed,
and preserves permutation. Adjacent swaps move the key left. Stopping
closes the gap and extends the sorted prefix. Entry-state framing allows
the outer variant to decrease after the inner loop finishes.
