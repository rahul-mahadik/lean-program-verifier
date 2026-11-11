import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x ≤ n)) ∧ (((2 * s.y) = (s.x * (s.x + 1))))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((n - s.x))

theorem candidate_vcs (n m : Nat) (hp : triangular.pre n m) :
    vcgen (triangular.program n m (candidateInvariant n m) (candidateVariant n m))
      (triangular.post n m) (triangular.initial n m) := by
  apply Case.verify triangular n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, triangular, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith

theorem candidate_correct (n m : Nat) (hp : triangular.pre n m) :
    (∃ t bound, triangular.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (triangular.program n m (candidateInvariant n m) (candidateVariant n m))
        (triangular.initial n m) = .done t) ∧
    (∀ fuel, run fuel (triangular.program n m (candidateInvariant n m) (candidateVariant n m))
      (triangular.initial n m) ≠ .fault) :=
  Case.executable_correct triangular n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
