import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := (((((s.x + s.y) = n)) ∧ ((s.x ≤ m)) ∧ ((s.n = n)) ∧ ((s.m = m))))
def candidateVariant (n m : Nat) (s : State) : Nat := (s.y)

theorem candidate_vcs (n m : Nat) (hp : boundedCopy.pre n m) :
    vcgen (boundedCopy.program n m (candidateInvariant n m) (candidateVariant n m))
      (boundedCopy.post n m) (boundedCopy.initial n m) := by
  apply Case.verify boundedCopy n m (candidateInvariant n m) (candidateVariant n m)
  ·
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega
  · intro s hs hg
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [candidateInvariant, candidateVariant, boundedCopy, Nat.add_mul, Nat.mul_add])
    all_goals (repeat' apply And.intro)
    all_goals omega

theorem candidate_correct (n m : Nat) (hp : boundedCopy.pre n m) :
    (∃ t bound, boundedCopy.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel (boundedCopy.program n m (candidateInvariant n m) (candidateVariant n m))
        (boundedCopy.initial n m) = .done t) ∧
    (∀ fuel, run fuel (boundedCopy.program n m (candidateInvariant n m) (candidateVariant n m))
      (boundedCopy.initial n m) ≠ .fault) :=
  Case.executable_correct boundedCopy n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
