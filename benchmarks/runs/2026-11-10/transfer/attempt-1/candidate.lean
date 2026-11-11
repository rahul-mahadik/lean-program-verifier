import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x + s.y) = (n + m))))
def candidateVariant (n m : Nat) (s : State) : Nat := (s.y)

theorem candidate_vcs (n m : Nat) (hp : transfer.pre n m) :
    vcgen (transfer.program n m (candidateInvariant n m) (candidateVariant n m))
      (transfer.post n m) (transfer.initial n m) := by
  apply Case.verify transfer n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, transfer, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : transfer.pre n m) :
    (∃ t bound, transfer.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (transfer.program n m (candidateInvariant n m) (candidateVariant n m))
        (transfer.initial n m) = .done t) ∧
    (∀ fuel, run fuel (transfer.program n m (candidateInvariant n m) (candidateVariant n m))
      (transfer.initial n m) ≠ .fault) :=
  Case.executable_correct transfer n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
