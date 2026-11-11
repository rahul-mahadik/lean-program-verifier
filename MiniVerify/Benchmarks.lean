import MiniVerify.Interpreter

/-!
# Frozen single-loop annotation benchmarks

Only the loop invariant and natural-number variant are candidate supplied.
Initial states, loop guards, transition functions, input preconditions, and
postconditions are trusted definitions. All input parameters are universally
quantified; no bounded testing assumption occurs in the correctness theorem.
-/

namespace MiniVerify.Benchmarks

structure State where
  x : Nat := 0
  y : Nat := 0
  z : Nat := 0
  n : Nat := 0
  m : Nat := 0
  i : Nat := 0
  deriving Repr, DecidableEq

structure Case where
  initial : Nat → Nat → State
  guard : Nat → Nat → State → Bool
  step : Nat → Nat → State → State
  pre : Nat → Nat → Prop
  post : Nat → Nat → State → Prop

namespace Case

def program (c : Case) (n m : Nat) (inv : State → Prop) (rank : State → Nat) :
    Cmd State :=
  .whileLoop (fun s => some (c.guard n m s)) inv rank
    (.action (fun s => some (c.step n m s)))

/-- Candidate annotations are accepted only after their initialization,
preservation, strict progress, and exit obligations have been proved. -/
theorem verify (c : Case) (n m : Nat) (inv : State → Prop) (rank : State → Nat)
    (hinit : inv (c.initial n m))
    (hstep : ∀ s, inv s → c.guard n m s = true →
      inv (c.step n m s) ∧ rank (c.step n m s) < rank s)
    (hexit : ∀ s, inv s → c.guard n m s = false → c.post n m s) :
    vcgen (c.program n m inv rank) (c.post n m) (c.initial n m) := by
  refine ⟨hinit, ?_⟩
  intro s hs
  cases hg : c.guard n m s with
  | false => simpa only [hg] using hexit s hs hg
  | true =>
      simp only [hg]
      exact ⟨c.step n m s, rfl, hstep s hs hg⟩

theorem total_correct (c : Case) (n m : Nat) (inv : State → Prop) (rank : State → Nat)
    (hvcs : vcgen (c.program n m inv rank) (c.post n m) (c.initial n m)) :
    ∃ t, Exec (c.program n m inv rank) (c.initial n m) t ∧ c.post n m t :=
  vcgen_sound _ _ _ hvcs

/-- Acceptance implies eventual execution of the unchanged benchmark
program, the frozen postcondition, and absence of runtime faults. -/
theorem executable_correct (c : Case) (n m : Nat) (inv : State → Prop)
    (rank : State → Nat)
    (hvcs : vcgen (c.program n m inv rank) (c.post n m) (c.initial n m)) :
    (∃ t bound, c.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (c.program n m inv rank) (c.initial n m) = .done t) ∧
    (∀ fuel, run fuel (c.program n m inv rank) (c.initial n m) ≠ .fault) :=
  verified_execution _ _ _ hvcs

end Case

def countUp : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ _ s := { s with x := s.x + 1 }
  pre _ _ := True
  post n _ s := s.x = n

def countDown : Case where
  initial n m := { x := n, n := n, m := m }
  guard _ _ s := decide (0 < s.x)
  step _ _ s := { s with x := s.x - 1 }
  pre _ _ := True
  post _ _ s := s.x = 0

def transfer : Case where
  initial n m := { x := n, y := m, n := n, m := m }
  guard _ _ s := decide (0 < s.y)
  step _ _ s := { s with x := s.x + 1, y := s.y - 1 }
  pre _ _ := True
  post n m s := s.x = n + m ∧ s.y = 0

def doubleCount : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ _ s := { s with x := s.x + 1, y := s.y + 2 }
  pre _ _ := True
  post n _ s := s.x = n ∧ s.y = 2 * n

def strideTwo : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ _ s := { s with x := s.x + 2 }
  pre _ _ := True
  post n _ s := n ≤ s.x ∧ s.x < n + 2

def parityDown : Case where
  initial n m := { x := n, n := n, m := m }
  guard _ _ s := decide (1 < s.x)
  step _ _ s := { s with x := s.x - 2 }
  pre _ _ := True
  post n _ s := s.x ≤ 1 ∧ s.x % 2 = n % 2

def synchronized : Case where
  initial n m := { x := n, y := m, n := n, m := m }
  guard _ _ s := decide (0 < s.x ∧ 0 < s.y)
  step _ _ s := { s with x := s.x - 1, y := s.y - 1 }
  pre _ _ := True
  post n m s := s.x = n - m ∧ s.y = m - n

def boundedCopy : Case where
  initial n m := { y := n, n := n, m := m }
  guard _ m s := decide (s.x < m ∧ 0 < s.y)
  step _ _ s := { s with x := s.x + 1, y := s.y - 1 }
  pre _ _ := True
  post n m s := s.x = min n m ∧ s.x + s.y = n

def twoPhase : Case where
  initial n m := { x := n, y := m, n := n, m := m }
  guard _ _ s := decide (0 < s.x ∨ 0 < s.y)
  step _ _ s := if 0 < s.x then
      { s with x := s.x - 1, z := s.z + 1 }
    else { s with y := s.y - 1, z := s.z + 1 }
  pre _ _ := True
  post n m s := s.x = 0 ∧ s.y = 0 ∧ s.z = n + m

def multiply : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ m s := { s with x := s.x + 1, y := s.y + m }
  pre _ _ := True
  post n m s := s.x = n ∧ s.y = n * m

def triangular : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ _ s := { s with x := s.x + 1, y := s.y + s.x + 1 }
  pre _ _ := True
  post n _ s := s.x = n ∧ 2 * s.y = n * (n + 1)

def square : Case where
  initial n m := { n := n, m := m }
  guard n _ s := decide (s.x < n)
  step _ _ s := { s with x := s.x + 1, y := s.y + 2 * s.x + 1 }
  pre _ _ := True
  post n _ s := s.x = n ∧ s.y = n * n

end MiniVerify.Benchmarks
