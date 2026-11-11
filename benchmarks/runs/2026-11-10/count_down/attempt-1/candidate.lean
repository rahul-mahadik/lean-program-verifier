import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := (True)
def candidateVariant (n m : Nat) (s : State) : Nat := (s.x)

theorem candidate_vcs (n m : Nat) (hp : countDown.pre n m) :
    vcgen (countDown.program n m (candidateInvariant n m) (candidateVariant n m))
      (countDown.post n m) (countDown.initial n m) := by
  apply Case.verify countDown n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, countDown, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : countDown.pre n m) :
    (∃ t bound, countDown.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (countDown.program n m (candidateInvariant n m) (candidateVariant n m))
        (countDown.initial n m) = .done t) ∧
    (∀ fuel, run fuel (countDown.program n m (candidateInvariant n m) (candidateVariant n m))
      (countDown.initial n m) ≠ .fault) :=
  Case.executable_correct countDown n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
