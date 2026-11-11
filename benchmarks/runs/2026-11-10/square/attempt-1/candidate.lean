import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := ((((s.x ≤ n)) ∧ ((s.y = (s.x * s.x)))))
def candidateVariant (n m : Nat) (s : State) : Nat := ((n - s.x))

theorem candidate_vcs (n m : Nat) (hp : square.pre n m) :
    vcgen (square.program n m (candidateInvariant n m) (candidateVariant n m))
      (square.post n m) (square.initial n m) := by
  apply Case.verify square n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, square, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals first | omega | nlinarith

theorem candidate_correct (n m : Nat) (hp : square.pre n m) :
    (∃ t bound, square.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (square.program n m (candidateInvariant n m) (candidateVariant n m))
        (square.initial n m) = .done t) ∧
    (∀ fuel, run fuel (square.program n m (candidateInvariant n m) (candidateVariant n m))
      (square.initial n m) ≠ .fault) :=
  Case.executable_correct square n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
