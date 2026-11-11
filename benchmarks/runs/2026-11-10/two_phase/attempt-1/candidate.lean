import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := (((((s.x + s.y) + s.z) = (n + m))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((s.x + s.y))

theorem candidate_vcs (n m : Nat) (hp : twoPhase.pre n m) :
    vcgen (twoPhase.program n m (candidateInvariant n m) (candidateVariant n m))
      (twoPhase.post n m) (twoPhase.initial n m) := by
  apply Case.verify twoPhase n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, twoPhase, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : twoPhase.pre n m) :
    (∃ t bound, twoPhase.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (twoPhase.program n m (candidateInvariant n m) (candidateVariant n m))
        (twoPhase.initial n m) = .done t) ∧
    (∀ fuel, run fuel (twoPhase.program n m (candidateInvariant n m) (candidateVariant n m))
      (twoPhase.initial n m) ≠ .fault) :=
  Case.executable_correct twoPhase n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
