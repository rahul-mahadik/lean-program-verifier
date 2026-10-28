import MiniVerify.Core
import MiniVerify.Interpreter
import Mathlib.Tactic

/-! An array-reversal loop with explicit bounds failure, a two-ended
loop invariant, and a natural-number termination variant. -/

namespace MiniVerify.Examples.Reverse

structure State where
  data : Array Int
  index : Nat
  deriving Repr, DecidableEq

/-- Bounds are checked before either read or write. `Array.swap` performs
two reads and two writes, using the resulting bounded indices. -/
def checkedSwap (a : Array Int) (i j : Nat) : Option (Array Int) :=
  if hi : i < a.size then
    if hj : j < a.size then some (a.swap ⟨i, hi⟩ ⟨j, hj⟩) else none
  else none

def step (s : State) : Option State := do
  let a ← checkedSwap s.data s.index (s.data.size - 1 - s.index)
  pure ⟨a, s.index + 1⟩

def test (s : State) : Option Bool := some (decide (s.index < s.data.size / 2))

def invariant (initial : Array Int) (s : State) : Prop :=
  s.data.size = initial.size ∧ s.index ≤ initial.size / 2 ∧
    ∀ k, s.data[k]? =
      if k < s.index ∨ initial.size - s.index ≤ k
      then initial.toList.reverse[k]? else initial[k]?

def post (initial : Array Int) (s : State) : Prop :=
  s.data.toList = initial.toList.reverse ∧ s.data.size = initial.size

def rank (s : State) : Nat := s.data.size / 2 - s.index

def program (initial : Array Int) : Cmd State :=
  .whileLoop test (invariant initial) rank (.action step)

theorem initial_invariant (a : Array Int) : invariant a ⟨a, 0⟩ := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  intro k
  by_cases hk : k < a.size
  · simp [hk, Nat.not_le.mpr hk]
  · have hge : a.size ≤ k := by omega
    have ha : a[k]? = none := Array.getElem?_eq_none_iff.mpr hge
    have hr : a.toList.reverse[k]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa using hge)
    simp [hge, ha, hr]

theorem invariant_exit {a : Array Int} {s : State}
    (hs : invariant a s) (hexit : ¬ s.index < s.data.size / 2) : post a s := by
  rcases hs with ⟨hsize, hi, hvalues⟩
  refine ⟨?_, hsize⟩
  apply List.ext_getElem?
  intro k
  rw [← Array.getElem?_eq_getElem?_toList, hvalues]
  split_ifs with hp
  · rfl
  · have hk : k < a.size := by omega
    have hmid : a.size - 1 - k = k := by omega
    rw [List.getElem?_reverse (by simpa using hk), ← Array.getElem?_eq_getElem?_toList]
    rw [hmid]

theorem invariant_step {a : Array Int} {s : State}
    (hs : invariant a s) (hgo : s.index < s.data.size / 2) :
    ∃ t, step s = some t ∧ invariant a t ∧ rank t < rank s := by
  rcases hs with ⟨hsize, hibound, hvalues⟩
  have hi : s.index < s.data.size := by omega
  have hj : s.data.size - 1 - s.index < s.data.size := by omega
  let t : State :=
    ⟨s.data.swap ⟨s.index, hi⟩ ⟨s.data.size - 1 - s.index, hj⟩, s.index + 1⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [step, checkedSwap, hi, hj, t]
  · refine ⟨by simpa [t] using hsize, by dsimp [t]; omega, ?_⟩
    intro k
    have hleft : ¬ (s.index < s.index ∨ a.size - s.index ≤ s.index) := by omega
    have hright : ¬ (s.data.size - 1 - s.index < s.index ∨
        a.size - s.index ≤ s.data.size - 1 - s.index) := by omega
    have hvleft : some s.data[s.index] = a[s.index]? := by
      calc
        _ = s.data[s.index]? := (Array.getElem?_eq_getElem hi).symm
        _ = _ := by rw [hvalues, if_neg hleft]
    have hvright : some s.data[s.data.size - 1 - s.index] =
        a[s.data.size - 1 - s.index]? := by
      calc
        _ = s.data[s.data.size - 1 - s.index]? := (Array.getElem?_eq_getElem hj).symm
        _ = _ := by rw [hvalues, if_neg hright]
    have hrevleft : a.toList.reverse[s.index]? = a[s.data.size - 1 - s.index]? := by
      rw [List.getElem?_reverse (by simpa [hsize] using hi),
        ← Array.getElem?_eq_getElem?_toList]
      simp only [Array.length_toList, hsize]
    have hrevright : a.toList.reverse[s.data.size - 1 - s.index]? = a[s.index]? := by
      rw [List.getElem?_reverse' (s.data.size - 1 - s.index) s.index
        (by simpa using (show s.data.size - 1 - s.index + s.index + 1 = a.size by omega)),
        ← Array.getElem?_eq_getElem?_toList]
    change (s.data.swap ⟨s.index, hi⟩ ⟨s.data.size - 1 - s.index, hj⟩)[k]? =
      if k < s.index + 1 ∨ a.size - (s.index + 1) ≤ k
      then a.toList.reverse[k]? else a[k]?
    rw [Array.getElem?_swap]
    by_cases hkright : s.data.size - 1 - s.index = k
    · subst k
      simp only [Fin.val_mk, ite_true]
      have hp : s.data.size - 1 - s.index < s.index + 1 ∨
          a.size - (s.index + 1) ≤ s.data.size - 1 - s.index := by omega
      rw [if_pos hp, hrevright]
      exact hvleft
    · by_cases hkleft : s.index = k
      · subst k
        simp only [Fin.val_mk, hkright, ite_false, ite_true]
        simp only [Nat.lt_succ_self, true_or, ite_true]
        rw [hrevleft]
        exact hvright
      · simp only [Fin.val_mk, hkright, hkleft, ite_false]
        rw [hvalues]
        have heq : (k < s.index ∨ a.size - s.index ≤ k) ↔
            (k < s.index + 1 ∨ a.size - (s.index + 1) ≤ k) := by omega
        by_cases hp : k < s.index ∨ a.size - s.index ≤ k
        · rw [if_pos hp, if_pos (heq.mp hp)]
        · rw [if_neg hp, if_neg (fun h => hp (heq.mpr h))]
  · simp [rank, t]
    omega

theorem verification_conditions (a : Array Int) :
    vcgen (program a) (post a) ⟨a, 0⟩ := by
  change invariant a ⟨a, 0⟩ ∧ _
  refine ⟨initial_invariant a, ?_⟩
  intro s hs
  by_cases hgo : s.index < s.data.size / 2
  · obtain ⟨t, ht, hti, htr⟩ := invariant_step hs hgo
    simp [test, hgo, vcgen, ht]
    exact ⟨hti, htr⟩
  · simpa [test, hgo] using invariant_exit hs hgo

/-- Arbitrary-length total correctness, including preservation of the
array length. This conclusion is obtained from the verifier's soundness. -/
theorem correct (a : Array Int) :
    ∃ t, Exec (program a) ⟨a, 0⟩ t ∧
      t.data.toList = a.toList.reverse ∧ t.data.size = a.size :=
  vcgen_sound (program a) (post a) ⟨a, 0⟩ (verification_conditions a)

/-- The executable interpreter eventually returns the reversed array
with enough fuel, and cannot report a bounds fault at any fuel level. -/
theorem executable_correct (a : Array Int) :
    (∃ t bound, (t.data.toList = a.toList.reverse ∧ t.data.size = a.size) ∧
      ∀ fuel, bound ≤ fuel → run fuel (program a) ⟨a, 0⟩ = .done t) ∧
    (∀ fuel, run fuel (program a) ⟨a, 0⟩ ≠ .fault) :=
  verified_execution (program a) (post a) ⟨a, 0⟩ (verification_conditions a)

end MiniVerify.Examples.Reverse
