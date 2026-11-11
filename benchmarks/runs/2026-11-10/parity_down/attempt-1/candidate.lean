import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x % 2) = (n % 2))))
def candidateVariant (n m : Nat) (s : State) : Nat := (s.x)

theorem candidate_vcs (n m : Nat) (hp : parityDown.pre n m) :
    vcgen (parityDown.program n m (candidateInvariant n m) (candidateVariant n m))
      (parityDown.post n m) (parityDown.initial n m) := by
  apply Case.verify parityDown n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, parityDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : parityDown.pre n m) :
    (∃ t bound, parityDown.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (parityDown.program n m (candidateInvariant n m) (candidateVariant n m))
        (parityDown.initial n m) = .done t) ∧
    (∀ fuel, run fuel (parityDown.program n m (candidateInvariant n m) (candidateVariant n m))
      (parityDown.initial n m) ≠ .fault) :=
  Case.executable_correct parityDown n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
