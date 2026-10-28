import MiniVerify.Interpreter
import Mathlib.Data.Array.Lemmas
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace MiniVerify.Examples.InsertionSort

structure State where
  data : Array Int
  i : Nat
  j : Nat
  deriving Repr, DecidableEq

/-- All entries strictly before `n` are in increasing order. -/
def PrefixSorted (a : Array Int) (n : Nat) : Prop :=
  ∀ p q : Nat, p < q → q < n → a[p]! ≤ a[q]!

/-- The active prefix is sorted after ignoring the moving insertion key. -/
def GapSorted (a : Array Int) (i j : Nat) : Prop :=
  ∀ p q : Nat, p < q → q ≤ i → p ≠ j → q ≠ j → a[p]! ≤ a[q]!

/-- The key lies below everything it has already passed. -/
def KeyBelow (a : Array Int) (i j : Nat) : Prop :=
  ∀ q : Nat, j < q → q ≤ i → a[j]! ≤ a[q]!

def OuterInv (original : Array Int) (s : State) : Prop :=
  s.data.size = original.size ∧ s.i ≤ s.data.size ∧
  PrefixSorted s.data s.i ∧ s.data.toList.Perm original.toList

def InnerInv (original : Array Int) (s : State) : Prop :=
  s.data.size = original.size ∧ s.i < s.data.size ∧ s.j ≤ s.i ∧
  GapSorted s.data s.i s.j ∧ KeyBelow s.data s.i s.j ∧
  s.data.toList.Perm original.toList

def Post (original : Array Int) (s : State) : Prop :=
  s.data.toList.Sorted (· ≤ ·) ∧ s.data.toList.Perm original.toList

/-- A checked adjacent swap; the failed branch is a memory fault. -/
def swapStep (s : State) : Option State :=
  if h : 0 < s.j ∧ s.j < s.data.size then
    let swapped := s.data.swap ⟨s.j, h.2⟩ ⟨s.j - 1, by omega⟩
    some { s with data := swapped, j := s.j - 1 }
  else none

def innerTest (s : State) : Option Bool :=
  if s.j = 0 then some false
  else if h : s.j < s.data.size then
    some (decide (s.data[s.j] < s.data[s.j - 1]))
  else none

def outerTest (s : State) : Option Bool := some (decide (s.i < s.data.size))

def program (original : Array Int) : Cmd State :=
  .seq (.action fun s => some {s with i := min 1 s.data.size})
    (.whileLoop outerTest (OuterInv original) (fun s => s.data.size - s.i)
      (.seq (.action fun s => some {s with j := s.i})
        (.seq (.whileLocal innerTest (fun entry s => InnerInv original s ∧ s.i = entry.i)
            (·.j) (.action swapStep))
          (.action fun s => some {s with i := s.i + 1}))))

private theorem set_adjacent_perm (l : List Int) (k : Nat) (h : k + 1 < l.length) :
    ((l.set (k + 1) l[k]).set k l[k + 1]).Perm l := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l => simpa using List.Perm.swap a b l
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons a l =>
      simpa using (ih l (by simpa using h)).cons a

private theorem swap_perm (a : Array Int) (j : Nat) (hpos : 0 < j) (hj : j < a.size) :
    (a.swap ⟨j, hj⟩ ⟨j - 1, by omega⟩).toList.Perm a.toList := by
  have heq : j - 1 + 1 = j := by omega
  have h := set_adjacent_perm a.toList (j - 1) (by simpa [heq] using hj)
  simpa [Array.toList_swap, Array.get_eq_getElem, heq] using h

private theorem swap_get (a : Array Int) (j : Nat) (hpos : 0 < j) (hj : j < a.size)
    (k : Nat) (hk : k < a.size) :
    (a.swap ⟨j, hj⟩ ⟨j - 1, by omega⟩)[k]! =
      if k = j then a[j - 1]! else if k = j - 1 then a[j]! else a[k]! := by
  rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_swap' a _ _ k hk]
  simp only [Fin.val_mk, getElem!_pos a j hj, getElem!_pos a k hk,
    getElem!_pos a (j - 1) (show j - 1 < a.size by omega), Fin.getElem_fin]

private theorem gap_swap (a : Array Int) (i j : Nat) (hj : j < a.size) (hpos : 0 < j)
    (hi : i < a.size) (hji : j ≤ i) (hg : GapSorted a i j) :
    GapSorted (a.swap ⟨j, hj⟩ ⟨j - 1, by omega⟩) i (j - 1) := by
  intro p q hpq hqi hp hq
  rw [swap_get a j hpos hj p (by omega), swap_get a j hpos hj q (by omega)]
  by_cases hpj : p = j
  · subst p
    simp only [if_pos rfl, if_neg (show q ≠ j by omega), if_neg hq]
    exact hg (j - 1) q (by omega) hqi (by omega) (by omega)
  · by_cases hqj : q = j
    · subst q
      simp only [if_neg hpj, if_neg hp, if_pos rfl]
      exact hg p (j - 1) (by omega) (by omega) hpj (by omega)
    · simp only [if_neg hpj, if_neg hp, if_neg hqj, if_neg hq]
      exact hg p q hpq hqi hpj hqj

private theorem key_swap (a : Array Int) (i j : Nat) (hj : j < a.size) (hpos : 0 < j)
    (hi : i < a.size) (hkey : KeyBelow a i j) (hlt : a[j]! < a[j - 1]!) :
    KeyBelow (a.swap ⟨j, hj⟩ ⟨j - 1, by omega⟩) i (j - 1) := by
  intro q hjq hqi
  rw [swap_get a j hpos hj (j - 1) (by omega), swap_get a j hpos hj q (by omega)]
  simp only [if_neg (show j - 1 ≠ j by omega), if_pos rfl,
    if_neg (show q ≠ j - 1 by omega)]
  by_cases heq : q = j
  · simp only [if_pos heq]
    exact hlt.le
  · simp only [if_neg heq]
    exact hkey q (by omega) hqi

private theorem gap_closed (a : Array Int) (i j : Nat) (hg : GapSorted a i j)
    (hk : KeyBelow a i j) (hstop : j = 0 ∨ a[j - 1]! ≤ a[j]!) :
    PrefixSorted a (i + 1) := by
  intro p q hpq hqi
  by_cases hpj : p = j
  · subst p
    exact hk q hpq (by omega)
  · by_cases hqj : q = j
    · subst q
      rcases hstop with hj | hle
      · omega
      · by_cases hp : p = j - 1
        · simpa [hp] using hle
        · exact le_trans (hg p (j - 1) (by omega) (by omega) hpj (by omega)) hle
    · exact hg p q hpq (by omega) hpj hqj

private theorem prefix_sorted_toList (a : Array Int) (h : PrefixSorted a a.size) :
    a.toList.Sorted (· ≤ ·) := by
  rw [List.Sorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hh := h i j hij (by simpa using hj)
  simpa [getElem!_pos a i (show i < a.size by simpa using hi),
    getElem!_pos a j (show j < a.size by simpa using hj)] using hh

theorem swap_preserves (original : Array Int) (s : State)
    (hs : InnerInv original s) (hpos : 0 < s.j)
    (hlt : s.data[s.j]! < s.data[s.j - 1]!) :
    ∃ t, swapStep s = some t ∧ InnerInv original t ∧ t.i = s.i ∧ t.j < s.j := by
  rcases hs with ⟨hsize, hi, hji, hg, hk, hp⟩
  have hj : s.j < s.data.size := by omega
  let b := s.data.swap ⟨s.j, hj⟩ ⟨s.j - 1, by omega⟩
  refine ⟨{s with data := b, j := s.j - 1}, ?_, ?_, rfl, by dsimp; omega⟩
  · have hbnd : 0 < s.j ∧ s.j < s.data.size := ⟨hpos, hj⟩
    simp only [swapStep, dif_pos hbnd]
  · refine ⟨by simpa [b] using hsize, by simpa [b] using hi, by dsimp; omega,
      gap_swap s.data s.i s.j hj hpos hi hji hg,
      key_swap s.data s.i s.j hj hpos hi hk hlt,
      (swap_perm s.data s.j hpos hj).trans hp⟩

theorem inner_exit_sorted (original : Array Int) (s : State)
    (hs : InnerInv original s) (hstop : innerTest s = some false) :
    PrefixSorted s.data (s.i + 1) := by
  rcases hs with ⟨_, hi, hji, hg, hk, _⟩
  apply gap_closed s.data s.i s.j hg hk
  by_cases hz : s.j = 0
  · exact Or.inl hz
  · right
    have hj : s.j < s.data.size := by omega
    simp only [innerTest, if_neg hz, dif_pos hj, Option.some.injEq,
      decide_eq_false_iff_not, not_lt] at hstop
    simpa only [getElem!_pos s.data s.j hj,
      getElem!_pos s.data (s.j - 1) (by omega)] using hstop

theorem inner_test_true (original : Array Int) (s : State)
    (hs : InnerInv original s) :
    innerTest s = some true ↔ 0 < s.j ∧ s.data[s.j]! < s.data[s.j - 1]! := by
  have hj : s.j < s.data.size := lt_of_le_of_lt hs.2.2.1 hs.2.1
  by_cases hz : s.j = 0
  · simp [innerTest, hz]
  · simp [innerTest, hz, hj, getElem!_pos s.data s.j hj,
      getElem!_pos s.data (s.j - 1) (by omega), Nat.pos_iff_ne_zero]

theorem inner_test_safe (original : Array Int) (s : State)
    (hs : InnerInv original s) : ∃ b, innerTest s = some b := by
  have hj : s.j < s.data.size := lt_of_le_of_lt hs.2.2.1 hs.2.1
  by_cases hz : s.j = 0 <;> simp [innerTest, hz, hj]

theorem enter_inner (original : Array Int) (s : State)
    (hs : OuterInv original s) (hgo : s.i < s.data.size) :
    InnerInv original {s with j := s.i} := by
  rcases hs with ⟨hsize, _, hsorted, hperm⟩
  refine ⟨hsize, hgo, le_refl _, ?_, ?_, hperm⟩
  · change GapSorted s.data s.i s.i
    intro p q hpq hqi _ hq
    exact hsorted p q hpq (by omega)
  · change KeyBelow s.data s.i s.i
    intro q hiq hqi
    omega

theorem leave_inner (original : Array Int) (entry s : State)
    (he : OuterInv original entry) (hs : InnerInv original s)
    (hframe : s.i = entry.i) (hstop : innerTest s = some false) :
    OuterInv original {s with i := s.i + 1} ∧
      ({s with i := s.i + 1} : State).data.size -
          ({s with i := s.i + 1} : State).i < entry.data.size - entry.i := by
  rcases hs with ⟨hsize, hi, _, _, _, hperm⟩
  refine ⟨⟨hsize, by dsimp; omega,
    inner_exit_sorted original s ⟨hsize, hi, by tauto⟩ hstop, hperm⟩, ?_⟩
  dsimp
  have hesize := he.1
  omega

theorem exit_outer (original : Array Int) (s : State)
    (hs : OuterInv original s) (hstop : ¬ s.i < s.data.size) : Post original s := by
  have hieq : s.i = s.data.size := by have := hs.2.1; omega
  refine ⟨prefix_sorted_toList s.data ?_, hs.2.2.2⟩
  simpa only [hieq] using hs.2.2.1

theorem initialize_invariant (original : Array Int) (s : State) (hdata : s.data = original) :
    OuterInv original {s with i := min 1 s.data.size} := by
  refine ⟨by simp [hdata], min_le_right _ _, ?_, ?_⟩
  · change PrefixSorted s.data (min 1 s.data.size)
    intro p q hpq hqi
    have hle : min 1 s.data.size ≤ 1 := min_le_left _ _
    omega
  · simp only [hdata]
    exact List.Perm.refl _

/-- The inner loop discharges VCs for any continuation implied by its
exit invariant. The frozen entry index supplies the outer-loop frame. -/
theorem inner_vcs (original : Array Int) (entry : State) (post : State → Prop)
    (hs : InnerInv original entry)
    (hexit : ∀ t, InnerInv original t → t.i = entry.i →
      innerTest t = some false → post t) :
    vcgen (.whileLocal innerTest
      (fun start t => InnerInv original t ∧ t.i = start.i)
      (·.j) (.action swapStep)) post entry := by
  refine ⟨⟨hs, rfl⟩, ?_⟩
  intro t ht
  rcases ht with ⟨ht, hframe⟩
  obtain ⟨b, hb⟩ := inner_test_safe original t ht
  cases b with
  | false => simpa only [hb] using hexit t ht hframe hb
  | true =>
    have hgo := (inner_test_true original t ht).mp hb
    obtain ⟨u, hu, hui, huframe, hurank⟩ := swap_preserves original t ht hgo.1 hgo.2
    simp only [hb]
    exact ⟨u, hu, ⟨hui, huframe.trans hframe⟩, hurank⟩

/-- The outer loop's generated conditions: bounded testing, preserved
sorted prefix and permutation, and strict decrease of `size - i`. -/
theorem outer_vcs (original : Array Int) (start : State) (hs : OuterInv original start) :
    vcgen (.whileLoop outerTest (OuterInv original) (fun s => s.data.size - s.i)
      (.seq (.action fun s => some {s with j := s.i})
        (.seq (.whileLocal innerTest (fun entry s => InnerInv original s ∧ s.i = entry.i)
            (·.j) (.action swapStep))
          (.action fun s => some {s with i := s.i + 1})))) (Post original) start := by
  refine ⟨hs, ?_⟩
  intro s hs
  by_cases hgo : s.i < s.data.size
  · simp only [outerTest, hgo, decide_True]
    refine ⟨{s with j := s.i}, rfl, ?_⟩
    apply inner_vcs original _ _ (enter_inner original s hs hgo)
    intro t ht hframe hstop
    refine ⟨{t with i := t.i + 1}, rfl, ?_⟩
    exact leave_inner original s t hs ht hframe hstop
  · simpa only [outerTest, hgo, decide_False] using exit_outer original s hs hgo

/-- All generated VCs hold for every initial array. No ordering premise
is imposed on the input, and no high-level sorting operation is called. -/
theorem vcs (original : Array Int) (s : State) (hdata : s.data = original) :
    vcgen (program original) (Post original) s := by
  refine ⟨{s with i := min 1 s.data.size}, rfl, ?_⟩
  exact outer_vcs original _ (initialize_invariant original s hdata)

def initial (a : Array Int) : State := ⟨a, 0, 0⟩

/-- In-place adjacent-swap insertion sort terminates without a memory
fault and returns a sorted permutation of its arbitrary input array. -/
theorem correct (a : Array Int) :
    ∃ t, Exec (program a) (initial a) t ∧
      t.data.toList.Sorted (· ≤ ·) ∧ t.data.toList.Perm a.toList :=
  vcgen_sound (program a) (Post a) (initial a) (vcs a (initial a) rfl)

theorem totalCorrect (a : Array Int) :
    TotalCorrect (fun s => s.data = a) (program a) (Post a) :=
  totalCorrect_of_vcs _ _ _ (vcs a)

/-- The verified relational result is reached by the actual interpreter
for every sufficiently large fuel budget; no budget produces a fault. -/
theorem executable_correct (a : Array Int) :
    (∃ t bound, Post a t ∧
      ∀ fuel, bound ≤ fuel → run fuel (program a) (initial a) = .done t) ∧
      (∀ fuel, run fuel (program a) (initial a) ≠ .fault) :=
  verified_execution (program a) (Post a) (initial a) (vcs a (initial a) rfl)

end MiniVerify.Examples.InsertionSort
