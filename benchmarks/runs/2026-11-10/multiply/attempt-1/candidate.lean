import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.n = n)) ∧ ((s.m = m)) ∧ ((s.x ≤ n)) ∧ ((s.y = (s.x * m)))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((n - s.x))

theorem candidate_vcs (n m : Nat) (hp : multiply.pre n m) :
    vcgen (multiply.program n m (candidateInvariant n m) (candidateVariant n m))
      (multiply.post n m) (multiply.initial n m) := by
  apply Case.verify multiply n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, multiply, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith

theorem candidate_correct (n m : Nat) (hp : multiply.pre n m) :
    (∃ t bound, multiply.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (multiply.program n m (candidateInvariant n m) (candidateVariant n m))
        (multiply.initial n m) = .done t) ∧
    (∀ fuel, run fuel (multiply.program n m (candidateInvariant n m) (candidateVariant n m))
      (multiply.initial n m) ≠ .fault) :=
  Case.executable_correct multiply n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
