import MiniVerify.Core

/-!
# Executable, fault-aware interpreter

Fuel bounds recursion depth. `timeout` is distinct from a runtime fault.
Loop annotations are ignored by this interpreter. Its agreement with
the relational semantics connects the VC theorem to executable code.
-/

namespace MiniVerify

inductive Outcome (σ : Type u) where
  | done (state : σ)
  | fault
  | timeout
  deriving Repr, DecidableEq

/-- Execute the program with a recursion-depth budget. -/
def run : Nat → Cmd σ → σ → Outcome σ
  | 0, _, _ => .timeout
  | _n + 1, .skip, s => .done s
  | _n + 1, .action step, s =>
      match step s with
      | none => .fault
      | some t => .done t
  | n + 1, .seq first second, s =>
      match run n first s with
      | .done m => run n second m
      | .fault => .fault
      | .timeout => .timeout
  | n + 1, .ite test yes no, s =>
      match test s with
      | none => .fault
      | some true => run n yes s
      | some false => run n no s
  | n + 1, c@(.whileLoop test _ _ body), s =>
      match test s with
      | none => .fault
      | some false => .done s
      | some true =>
          match run n body s with
          | .done m => run n c m
          | .fault => .fault
          | .timeout => .timeout
  | n + 1, c@(.whileLocal test _ _ body), s =>
      match test s with
      | none => .fault
      | some false => .done s
      | some true =>
          match run n body s with
          | .done m => run n c m
          | .fault => .fault
          | .timeout => .timeout

/-- Any finite normal execution agrees with every interpreter budget:
the interpreter either times out or returns exactly that final state.
In particular, it never reports a fault on a verified execution. -/
theorem Exec.run_result (h : Exec c s t) (fuel : Nat) :
    run fuel c s = .timeout ∨ run fuel c s = .done t := by
  induction h generalizing fuel with
  | skip => cases fuel <;> simp [run]
  | action hstep => cases fuel <;> simp [run, hstep]
  | seq hfirst hsecond ihfirst ihsecond =>
      cases fuel with
      | zero => simp [run]
      | succ n =>
          rcases ihfirst n with hf | hf
          · simp [run, hf]
          · simpa [run, hf] using ihsecond n
  | ite_true htest hyes ih =>
      cases fuel with
      | zero => simp [run]
      | succ n => simpa [run, htest] using ih n
  | ite_false htest hno ih =>
      cases fuel with
      | zero => simp [run]
      | succ n => simpa [run, htest] using ih n
  | while_false htest => cases fuel <;> simp [run, htest]
  | while_true htest hbody hrest ihbody ihrest =>
      cases fuel with
      | zero => simp [run]
      | succ n =>
          rcases ihbody n with hb | hb
          · simp [run, htest, hb]
          · simpa [run, htest, hb] using ihrest n
  | whileLocal_false htest => cases fuel <;> simp [run, htest]
  | whileLocal_true htest hbody hrest ihbody ihrest =>
      cases fuel with
      | zero => simp [run]
      | succ n =>
          rcases ihbody n with hb | hb
          · simp [run, htest, hb]
          · simpa [run, htest, hb] using ihrest n

/-- Finite executions are deterministic. -/
theorem Exec.deterministic (h : Exec c s t) (h' : Exec c s t') : t = t' := by
  induction h generalizing t' with
  | skip => cases h'; rfl
  | action hs =>
      cases h' with
      | action hs' => exact Option.some.inj (hs.symm.trans hs')
  | seq h1 h2 ih1 ih2 =>
      cases h' with
      | seq h1' h2' =>
          have hm := ih1 h1'
          subst hm
          exact ih2 h2'
  | ite_true ht hy ih =>
      cases h' with
      | ite_true _ hy' => exact ih hy'
      | ite_false hf _ => simp [ht] at hf
  | ite_false ht hn ih =>
      cases h' with
      | ite_false _ hn' => exact ih hn'
      | ite_true hf _ => simp [ht] at hf
  | while_false ht =>
      cases h' with
      | while_false => rfl
      | while_true hf _ _ => simp [ht] at hf
  | while_true ht hb hr ihb ihr =>
      cases h' with
      | while_false hf => simp [ht] at hf
      | while_true _ hb' hr' =>
          have hm := ihb hb'
          subst hm
          exact ihr hr'
  | whileLocal_false ht =>
      cases h' with
      | whileLocal_false => rfl
      | whileLocal_true hf _ _ => simp [ht] at hf
  | whileLocal_true ht hb hr ihb ihr =>
      cases h' with
      | whileLocal_false hf => simp [ht] at hf
      | whileLocal_true _ hb' hr' =>
          have hm := ihb hb'
          subst hm
          exact ihr hr'

/-- A finite execution has a sufficient interpreter budget; every
larger budget returns its final state. -/
theorem Exec.run_complete (h : Exec c s t) :
    ∃ bound : Nat, ∀ fuel, bound ≤ fuel → run fuel c s = .done t := by
  induction h with
  | skip =>
      refine ⟨1, fun fuel hf => ?_⟩
      cases fuel <;> simp_all [run]
  | action hstep =>
      refine ⟨1, fun fuel hf => ?_⟩
      cases fuel <;> simp_all [run]
  | seq hfirst hsecond ihfirst ihsecond =>
      obtain ⟨a, ha⟩ := ihfirst
      obtain ⟨b, hb⟩ := ihsecond
      refine ⟨max a b + 1, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ n => simp [run, ha n (by omega), hb n (by omega)]
  | ite_true htest hyes ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + 1, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ n => simp [run, htest, ha n (by omega)]
  | ite_false htest hno ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + 1, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ n => simp [run, htest, ha n (by omega)]
  | while_false htest =>
      refine ⟨1, fun fuel hf => ?_⟩
      cases fuel <;> simp_all [run]
  | while_true htest hbody hrest ihbody ihrest =>
      obtain ⟨a, ha⟩ := ihbody
      obtain ⟨b, hb⟩ := ihrest
      refine ⟨max a b + 1, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ n => simp [run, htest, ha n (by omega), hb n (by omega)]
  | whileLocal_false htest =>
      refine ⟨1, fun fuel hf => ?_⟩
      cases fuel <;> simp_all [run]
  | whileLocal_true htest hbody hrest ihbody ihrest =>
      obtain ⟨a, ha⟩ := ihbody
      obtain ⟨b, hb⟩ := ihrest
      refine ⟨max a b + 1, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ n => simp [run, htest, ha n (by omega), hb n (by omega)]

/-- Interpreter success certifies a normal execution of the same program. -/
theorem run_sound (fuel : Nat) (c : Cmd σ) (s t : σ)
    (h : run fuel c s = .done t) : Exec c s t := by
  induction fuel generalizing c s t with
  | zero => simp [run] at h
  | succ n ih =>
      cases c with
      | skip =>
          have ht : s = t := by simpa [run] using h
          subst ht
          exact .skip
      | action step =>
          cases hs : step s with
          | none => simp [run, hs] at h
          | some a =>
              have ht : a = t := by simpa [run, hs] using h
              subst ht
              exact .action hs
      | seq first second =>
          cases hs : run n first s with
          | fault => simp [run, hs] at h
          | timeout => simp [run, hs] at h
          | done m =>
              exact .seq (ih first s m hs) (ih second m t (by simpa [run, hs] using h))
      | ite test yes no =>
          cases hs : test s with
          | none => simp [run, hs] at h
          | some b =>
              cases b with
              | false => exact .ite_false hs (ih no s t (by simpa [run, hs] using h))
              | true => exact .ite_true hs (ih yes s t (by simpa [run, hs] using h))
      | whileLoop test invariant rank body =>
          cases hs : test s with
          | none => simp [run, hs] at h
          | some b =>
              cases b with
              | false =>
                  have ht : s = t := by simpa [run, hs] using h
                  subst ht
                  exact .while_false hs
              | true =>
                  cases hb : run n body s with
                  | fault => simp [run, hs, hb] at h
                  | timeout => simp [run, hs, hb] at h
                  | done m =>
                      exact .while_true hs (ih body s m hb)
                        (ih _ m t (by simpa [run, hs, hb] using h))
      | whileLocal test invariant rank body =>
          cases hs : test s with
          | none => simp [run, hs] at h
          | some b =>
              cases b with
              | false =>
                  have ht : s = t := by simpa [run, hs] using h
                  subst ht
                  exact .whileLocal_false hs
              | true =>
                  cases hb : run n body s with
                  | fault => simp [run, hs, hb] at h
                  | timeout => simp [run, hs, hb] at h
                  | done m =>
                      exact .whileLocal_true hs (ih body s m hb)
                        (ih _ m t (by simpa [run, hs, hb] using h))

/-- End-to-end total correctness for the executable interpreter. -/
theorem verified_execution (c : Cmd σ) (post : Assertion σ) (s : σ)
    (hvc : vcgen c post s) :
    (∃ t bound, post t ∧ ∀ fuel, bound ≤ fuel → run fuel c s = .done t) ∧
      (∀ fuel, run fuel c s ≠ .fault) := by
  obtain ⟨t, hexec, hp⟩ := vcgen_sound c post s hvc
  obtain ⟨bound, hb⟩ := hexec.run_complete
  refine ⟨⟨t, bound, hp, hb⟩, fun fuel => ?_⟩
  rcases hexec.run_result fuel with hto | hdone
  · simp [hto]
  · simp [hdone]

end MiniVerify
