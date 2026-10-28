# Adding a verified program

The named-variable interface is useful for small examples. A statement
is built as a Lean AST; a specification is a predicate on stores.

This example copies `x + 1` into `y` and proves the generated conditions.

```lean
import MiniVerify

open MiniVerify MiniVerify.Language

def increment : Stmt :=
  .assign "y" (.add (.var "x") (.lit 1))

theorem increment_vcs (s : Store) :
    conditions increment (fun t => t.vars "y" = s.vars "x" + 1) s := by
  refine ⟨s.setVar "y" (s.vars "x" + 1), ?_, ?_⟩
  · simp [increment, Language.assign, IExpr.eval]
  · simp [Store.setVar]
```

To connect discharged conditions to executable behavior, apply
`Language.verified_program`. Its conclusion supplies a final state and
a sufficient fuel bound, and excludes faults at every fuel level.

For a loop, supply an invariant and a natural-number variant:

```lean
-- Schematic construction: the user provides these four components.
-- .whileLoop test invariant variant body
```

After unfolding `conditions`, `lower`, and `vcgen`, the obligations are:
the invariant initially, safe test evaluation, the postcondition on
exit, and invariant preservation with variant decrease on continuation.
Use `whileLocal` when the invariant must mention the loop's entry state.

For larger programs, a typed record often makes proof statements easier
to read. `Examples.BinarySearch`, `Examples.Reverse`, and
`Examples.InsertionSort` show this interface. Start with the reversal
example for a single loop; insertion sort demonstrates nested loops and
entry-state-dependent invariants.

The API is deliberately honest about automation: the generator creates
the obligations structurally. Lean tactics such as `simp` and `omega`,
together with invariant lemmas, discharge them. A successful native run
is a demo; the universal theorem comes from the generated-condition
proof and the soundness theorem.
