import MiniVerify

/-! Exact kernel-reduced execution regressions and adversarial VC tests.
The universal correctness proofs live in the implementation modules. -/

namespace MiniVerify.Tests

private def reverseOutput (a : Array Int) : Option (Array Int) :=
  match run 64 (Examples.Reverse.program a) ⟨a, 0⟩ with
  | .done t => some t.data
  | _ => none

private def sortOutput (a : Array Int) : Option (Array Int) :=
  match run 128 (Examples.InsertionSort.program a) (Examples.InsertionSort.initial a) with
  | .done t => some t.data
  | _ => none

private def searchOutput (a : Array Int) (target : Int) : Option (Option Nat) :=
  match run 32 (Examples.BinarySearch.program a target) (Examples.BinarySearch.initial a target) with
  | .done t => some t.result
  | _ => none

example : reverseOutput #[] = some #[] := by decide
example : reverseOutput #[7] = some #[7] := by decide
example : reverseOutput #[1, 2, 3, 4] = some #[4, 3, 2, 1] := by decide
example : reverseOutput #[1, -2, 3, 4, 5] = some #[5, 4, 3, -2, 1] := by decide
example : sortOutput #[] = some #[] := by decide
example : sortOutput #[7] = some #[7] := by decide
example : sortOutput #[5, 2, 4, 2, -1] = some #[-1, 2, 2, 4, 5] := by decide
example : sortOutput #[4, 3, 2, 1] = some #[1, 2, 3, 4] := by decide
example : searchOutput #[1, 3, 5, 7, 9] 7 = some (some 3) := by decide
example : searchOutput #[1, 3, 5, 7, 9] 6 = some none := by decide
example : searchOutput #[] 2 = some none := by decide
example : searchOutput #[1, 3, 3, 3, 8] 3 = some (some 1) := by decide

-- A rejected action is a fault, while absent fuel is a timeout.
example : run 1 (.action fun (_ : Unit) => none) () = .fault := by rfl
example : run 0 (.action fun (_ : Unit) => none) () = .timeout := by rfl
example : ¬ vcgen (.action fun (_ : Unit) => none) (fun _ => True) () := by
  simp [vcgen]

-- An always-true loop with a constant variant cannot discharge its VCs.
example : ¬ vcgen
    (.whileLoop (fun (_ : Unit) => some true) (fun _ => True) (fun _ => 0) .skip)
    (fun _ => True) () := by simp [vcgen]

-- The same protection applies to entry-state-dependent invariants.
example : ¬ vcgen
    (.whileLocal (fun (_ : Unit) => some true) (fun _ _ => True) (fun _ => 0) .skip)
    (fun _ => True) () := by simp [vcgen]

private def store : Language.Store :=
  (Language.Store.empty.setVar "x" (-7)).setArray "a" #[10, 20]

example : Language.IExpr.eval (.read "a" (.lit (-1))) store = none := by decide
example : Language.IExpr.eval (.read "a" (.lit 2)) store = none := by decide
example : Language.IExpr.eval (.read "a" (.lit 1)) store = some 20 := by decide
example : Language.run 4 (.write "a" (.lit (-1)) (.lit 99)) store = .fault := by rfl
example : Language.run 4 (.write "a" (.lit 2) (.lit 99)) store = .fault := by rfl
example : ¬ Language.conditions (.write "a" (.lit 2) (.lit 99)) (fun _ => True) store := by
  simp [Language.conditions, Language.lower, vcgen, Language.write,
    Language.IExpr.eval, store, Language.Store.setArray]

-- A false left operand short-circuits an otherwise invalid read.
example : Language.BExpr.eval
    (.and (.lt (.lit 1) (.lit 0)) (.eq (.read "a" (.lit 9)) (.lit 0))) store
      = some false := by decide

example : (match Language.run 8 Language.absoluteValue store with
    | .done t => some (t.vars "y")
    | _ => none) = some 7 := by decide

end MiniVerify.Tests
