import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x < (n + 2))) ∧ ((s.n = n))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((n - s.x))

theorem candidate_vcs (n m : Nat) (hp : strideTwo.pre n m) :
    vcgen (strideTwo.program n m (candidateInvariant n m) (candidateVariant n m))
      (strideTwo.post n m) (strideTwo.initial n m) := by
  apply Case.verify strideTwo n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, strideTwo, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : strideTwo.pre n m) :
    (∃ t bound, strideTwo.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (strideTwo.program n m (candidateInvariant n m) (candidateVariant n m))
        (strideTwo.initial n m) = .done t) ∧
    (∀ fuel, run fuel (strideTwo.program n m (candidateInvariant n m) (candidateVariant n m))
      (strideTwo.initial n m) ≠ .fault) :=
  Case.executable_correct strideTwo n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
