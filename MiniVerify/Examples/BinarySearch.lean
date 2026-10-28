import MiniVerify.Interpreter

/-!
# Verified binary search

The executable program searches a sorted `Array Int` using a half-open interval.
Every lookup uses `Array.getElem?`; an out-of-bounds read in the loop is a failed
command. The proof therefore establishes memory safety as well as termination
and the usual present/absent specification.
-/

namespace MiniVerify.Examples.BinarySearch

structure State where
  data : Array Int
  target : Int
  lo : Nat
  hi : Nat
  result : Option Nat
  deriving Repr, DecidableEq

/-- The conventional nondecreasing ordering of the array's valid indices. -/
def Sorted (a : Array Int) : Prop :=
  Monotone (fun i : Fin a.size => a[i])

/-- An executable check of the precise sorted-input hypothesis. -/
def sortedCheck (a : Array Int) : Bool :=
  (List.finRange a.size).all fun i =>
    (List.finRange a.size).all fun j => decide (i ≤ j → a[i] ≤ a[j])

theorem sortedCheck_correct (a : Array Int) : sortedCheck a = true ↔ Sorted a := by
  simp only [sortedCheck, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq]
  rfl

def midpoint (s : State) : Nat := (s.lo + s.hi) / 2

def test (s : State) : Option Bool := some (decide (s.lo < s.hi))

/-- One genuine binary-search iteration, including the checked array read. -/
def step (s : State) : Option State := do
  let value ← s.data[midpoint s]?
  if value < s.target then
    pure { s with lo := midpoint s + 1 }
  else
    pure { s with hi := midpoint s }

/-- A checked read at the lower bound converts it into an optional match. -/
def finish (s : State) : Option State :=
  some { s with result := if s.data[s.lo]? = some s.target then some s.lo else none }

def initial (a : Array Int) (target : Int) : State :=
  ⟨a, target, 0, a.size, none⟩

/-- Values excluded on the left are too small; values excluded on the right
are at least the target. The original array and target remain immutable. -/
def invariant (a : Array Int) (target : Int) (s : State) : Prop :=
  s.data = a ∧ s.target = target ∧ s.lo ≤ s.hi ∧ s.hi ≤ a.size ∧
  (∀ i (h : i < a.size), i < s.lo → a[i] < target) ∧
  (∀ i (h : i < a.size), s.hi ≤ i → target ≤ a[i])

def rank (s : State) : Nat := s.hi - s.lo

/-- A returned index really points to the target; `none` is equivalent to
the absence of the target throughout the input array. -/
def Correct (a : Array Int) (target : Int) (s : State) : Prop :=
  s.data = a ∧ s.target = target ∧
  (∀ i : Nat, s.result = some i → a[i]? = some target) ∧
  (s.result = none ↔ ¬ ∃ i : Nat, a[i]? = some target)

theorem initial_invariant (a : Array Int) (target : Int) :
    invariant a target (initial a target) := by
  simp [invariant, initial]
  intro i hi h
  omega

theorem midpoint_bounds {a : Array Int} {target : Int} {s : State}
    (hs : invariant a target s) (hgo : s.lo < s.hi) :
    s.lo ≤ midpoint s ∧ midpoint s < s.hi ∧ midpoint s < a.size := by
  rcases hs with ⟨_, _, hlohi, hsize, _, _⟩
  dsimp [midpoint]
  omega

theorem step_preserves {a : Array Int} {target : Int} {s : State}
    (ha : Sorted a) (hs : invariant a target s) (hgo : s.lo < s.hi) :
    ∃ t, step s = some t ∧ invariant a target t ∧ rank t < rank s := by
  obtain ⟨hlo, hhi, hm⟩ := midpoint_bounds hs hgo
  rcases hs with ⟨hdata, htarget, hlohi, hsize, hleft, hright⟩
  have hread : s.data[midpoint s]? = some a[midpoint s] := by
    simp [hdata, Array.getElem?_eq_getElem hm]
  by_cases hlt : a[midpoint s] < target
  · refine ⟨{s with lo := midpoint s + 1}, ?_, ?_, ?_⟩
    · simp [step, hread, htarget, hlt]
    · refine ⟨hdata, htarget, by dsimp; omega, hsize, ?_, ?_⟩
      · intro i hi hilow
        by_cases hold : i < s.lo
        · exact hleft i hi hold
        · have him : i ≤ midpoint s := by dsimp at hilow; omega
          have hmono : a[i] ≤ a[midpoint s] :=
            ha (show (⟨i, hi⟩ : Fin a.size) ≤ ⟨midpoint s, hm⟩ from him)
          exact lt_of_le_of_lt hmono hlt
      · simpa using hright
    · dsimp [rank]
      omega
  · refine ⟨{s with hi := midpoint s}, ?_, ?_, ?_⟩
    · simp [step, hread, htarget, hlt]
    · refine ⟨hdata, htarget, hlo, by dsimp; omega, ?_, ?_⟩
      · simpa using hleft
      · intro i hi hupper
        have hmono : a[midpoint s] ≤ a[i] :=
          ha (show (⟨midpoint s, hm⟩ : Fin a.size) ≤ ⟨i, hi⟩ from hupper)
        exact le_trans (le_of_not_gt hlt) hmono
    · dsimp [rank]
      omega

theorem finish_correct {a : Array Int} {target : Int} {s : State}
    (ha : Sorted a) (hs : invariant a target s) (hdone : ¬ s.lo < s.hi) :
    ∃ t, finish s = some t ∧ Correct a target t := by
  rcases hs with ⟨hdata, htarget, hlohi, hsize, hleft, hright⟩
  have heq : s.lo = s.hi := by omega
  have occurrences_at_lower_bound :
      (∃ i : Nat, a[i]? = some target) ↔ a[s.lo]? = some target := by
    constructor
    · rintro ⟨i, hi⟩
      have hib : i < a.size := by
        by_contra h
        have : a[i]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
        simp [this] at hi
      have hvalue : a[i] = target := by
        simpa [Array.getElem?_eq_getElem hib] using hi
      have hnotleft : ¬ i < s.lo := by
        intro h
        have := hleft i hib h
        omega
      have hlob : s.lo < a.size := by omega
      have hge : target ≤ a[s.lo] := hright s.lo hlob (by omega)
      have hmono : a[s.lo] ≤ a[i] :=
        ha (show (⟨s.lo, hlob⟩ : Fin a.size) ≤ ⟨i, hib⟩ from Nat.le_of_not_gt hnotleft)
      have hvalueLo : a[s.lo] = target := le_antisymm (hvalue ▸ hmono) hge
      simpa [Array.getElem?_eq_getElem hlob] using hvalueLo
    · intro h
      exact ⟨s.lo, h⟩
  refine ⟨{ s with result := if s.data[s.lo]? = some s.target then some s.lo else none },
    rfl, hdata, htarget, ?_, ?_⟩
  · intro i hi
    dsimp [finish] at hi
    split at hi
    · have hil : s.lo = i := Option.some.inj hi
      simpa [← hil, hdata, htarget] using ‹s.data[s.lo]? = some s.target›
    · simp at hi
  · dsimp
    simp only [hdata, htarget]
    split <;> simp_all [occurrences_at_lower_bound]

/-- The search loop is an object-language `whileLoop`, followed by the
checked final lookup. The array/target parameters occur only in ghost
annotations; ordinary execution uses the fields of the runtime state. -/
def program (a : Array Int) (target : Int) : Cmd State :=
  .seq (.whileLoop test (invariant a target) rank (.action step)) (.action finish)

/-- All obligations generated by the generic verifier are discharged for
every sorted input, rather than for a fixed array or bounded search depth. -/
theorem verification_conditions {a : Array Int} {target : Int} (ha : Sorted a)
    {s : State} (hs : invariant a target s) :
    vcgen (program a target) (Correct a target) s := by
  refine ⟨hs, ?_⟩
  intro t ht
  by_cases hgo : t.lo < t.hi
  · simpa [test, hgo, vcgen] using step_preserves ha ht hgo
  · simpa [test, hgo, vcgen] using finish_correct ha ht hgo

/-- Total correctness, obtained by applying the verifier's general
soundness theorem to the generated obligations. -/
theorem program_total_correct {a : Array Int} {target : Int} (ha : Sorted a) :
    TotalCorrect (invariant a target) (program a target) (Correct a target) :=
  totalCorrect_of_vcs _ _ _ (fun _ hs => verification_conditions ha hs)

/-- Binary search always finishes without a failed checked read and
returns a correct present/absent answer on every sorted integer array. -/
theorem binary_search_correct (a : Array Int) (target : Int) (ha : Sorted a) :
    ∃ t, Exec (program a target) (initial a target) t ∧ Correct a target t :=
  program_total_correct ha _ (initial_invariant a target)

/-- The executable interpreter eventually returns the same correct result
for every sufficiently large budget, and cannot fault at any budget. -/
theorem executable_correct (a : Array Int) (target : Int) (ha : Sorted a) :
    (∃ t bound, Correct a target t ∧
      ∀ fuel, bound ≤ fuel → run fuel (program a target) (initial a target) = .done t) ∧
    (∀ fuel, run fuel (program a target) (initial a target) ≠ .fault) :=
  verified_execution _ _ _ (verification_conditions ha (initial_invariant a target))

end MiniVerify.Examples.BinarySearch
