import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x ≤ n)) ∧ ((s.y = (2 * s.x)))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((n - s.x))

theorem candidate_vcs (n m : Nat) (hp : doubleCount.pre n m) :
    vcgen (doubleCount.program n m (candidateInvariant n m) (candidateVariant n m))
      (doubleCount.post n m) (doubleCount.initial n m) := by
  apply Case.verify doubleCount n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, doubleCount, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : doubleCount.pre n m) :
    (∃ t bound, doubleCount.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (doubleCount.program n m (candidateInvariant n m) (candidateVariant n m))
        (doubleCount.initial n m) = .done t) ∧
    (∀ fuel, run fuel (doubleCount.program n m (candidateInvariant n m) (candidateVariant n m))
      (doubleCount.initial n m) ≠ .fault) :=
  Case.executable_correct doubleCount n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
