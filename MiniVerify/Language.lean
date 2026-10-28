import MiniVerify.Interpreter

/-!
# A concrete integer-and-array language

This frontend supplies an expression and statement AST over named integer
variables and named integer arrays. Expressions and writes use checked array
indices, including an explicit check against negative integer indices.
Lowering gives the generic verifier its concrete primitive operations.
-/

namespace MiniVerify.Language

structure Store where
  vars : String → Int
  arrays : String → Array Int

namespace Store

/-- Uninitialized integer variables are zero; arrays are empty. -/
def empty : Store := ⟨fun _ => 0, fun _ => #[]⟩

def setVar (s : Store) (name : String) (value : Int) : Store :=
  { s with vars := Function.update s.vars name value }

def setArray (s : Store) (name : String) (value : Array Int) : Store :=
  { s with arrays := Function.update s.arrays name value }

end Store

inductive IExpr where
  | lit (value : Int)
  | var (name : String)
  | add (left right : IExpr)
  | sub (left right : IExpr)
  | mul (left right : IExpr)
  | length (name : String)
  | read (name : String) (index : IExpr)
  deriving Repr

namespace IExpr

/-- Checked expression evaluation. Negative or oversized indices fail. -/
def eval : IExpr → Store → Option Int
  | .lit value, _ => some value
  | .var name, s => some (s.vars name)
  | .add left right, s => do
      let a ← eval left s
      let b ← eval right s
      pure (a + b)
  | .sub left right, s => do
      let a ← eval left s
      let b ← eval right s
      pure (a - b)
  | .mul left right, s => do
      let a ← eval left s
      let b ← eval right s
      pure (a * b)
  | .length name, s => some (Int.ofNat (s.arrays name).size)
  | .read name index, s => do
      let i ← eval index s
      if 0 ≤ i then (s.arrays name)[i.toNat]? else none

end IExpr

inductive BExpr where
  | eq (left right : IExpr)
  | lt (left right : IExpr)
  | le (left right : IExpr)
  | not (value : BExpr)
  | and (left right : BExpr)
  deriving Repr

namespace BExpr

/-- Conjunction short-circuits, so its right operand is evaluated only
when its left operand is true. Other expression failures propagate. -/
def eval : BExpr → Store → Option Bool
  | .eq left right, s => do
      let a ← left.eval s
      let b ← right.eval s
      pure (decide (a = b))
  | .lt left right, s => do
      let a ← left.eval s
      let b ← right.eval s
      pure (decide (a < b))
  | .le left right, s => do
      let a ← left.eval s
      let b ← right.eval s
      pure (decide (a ≤ b))
  | .not value, s => do
      let b ← eval value s
      pure (!b)
  | .and left right, s => do
      let b ← eval left s
      if b then eval right s else some false

end BExpr

inductive Stmt where
  | skip
  | assign (name : String) (value : IExpr)
  | write (name : String) (index value : IExpr)
  | seq (first second : Stmt)
  | ite (test : BExpr) (yes no : Stmt)
  | whileLoop (test : BExpr) (invariant : Store → Prop)
      (rank : Store → Nat) (body : Stmt)
  | whileLocal (test : BExpr) (invariant : Store → Store → Prop)
      (rank : Store → Nat) (body : Stmt)

/-- Assignment evaluates its expression before updating the named variable. -/
def assign (name : String) (value : IExpr) (s : Store) : Option Store := do
  let v ← value.eval s
  pure (s.setVar name v)

/-- Array writes reject negative indices and indices at or beyond the
array's size. A write preserves the array's length. -/
def write (name : String) (index value : IExpr) (s : Store) : Option Store := do
  let i ← index.eval s
  let v ← value.eval s
  if 0 ≤ i then
    if hi : i.toNat < (s.arrays name).size then
      pure (s.setArray name ((s.arrays name).set ⟨i.toNat, hi⟩ v))
    else none
  else none

/-- Concrete statement semantics, expressed through the verified generic
command language. Loop annotations remain ghost data. -/
def lower : Stmt → Cmd Store
  | .skip => .skip
  | .assign name value => .action (assign name value)
  | .write name index value => .action (write name index value)
  | .seq first second => .seq (lower first) (lower second)
  | .ite test yes no => .ite test.eval (lower yes) (lower no)
  | .whileLoop test invariant rank body =>
      .whileLoop test.eval invariant rank (lower body)
  | .whileLocal test invariant rank body =>
      .whileLocal test.eval invariant rank (lower body)

/-- Verification conditions for the concrete language. -/
def conditions (p : Stmt) (post : Store → Prop) : Store → Prop :=
  vcgen (lower p) post

/-- The executable surface-language interpreter shares the generic
interpreter's separate success, fault, and timeout outcomes. -/
def run (fuel : Nat) (p : Stmt) (s : Store) : Outcome Store :=
  MiniVerify.run fuel (lower p) s

/-- Discharged surface-language VCs imply eventual executable success
and exclude faults even for insufficient fuel budgets. -/
theorem verified_program (p : Stmt) (post : Store → Prop) (s : Store)
    (hvc : conditions p post s) :
    (∃ t bound, post t ∧ ∀ fuel, bound ≤ fuel → run fuel p s = .done t) ∧
      (∀ fuel, run fuel p s ≠ .fault) :=
  verified_execution (lower p) post s hvc

/-- A surface-language program with a genuine conditional and integer
assignment. Its input is `x` and its output is `y`. -/
def absoluteValue : Stmt :=
  .ite (.lt (.var "x") (.lit 0))
    (.assign "y" (.sub (.lit 0) (.var "x")))
    (.assign "y" (.var "x"))

theorem absoluteValue_conditions (s : Store) :
    conditions absoluteValue
      (fun t => t.vars "x" = s.vars "x" ∧ t.vars "y" = |s.vars "x"|) s := by
  by_cases hx : s.vars "x" < 0
  · simp [conditions, absoluteValue, lower, vcgen, BExpr.eval, IExpr.eval, hx]
    refine ⟨s.setVar "y" (-(s.vars "x")), ?_, ?_⟩
    · simp [assign, IExpr.eval]
    · simp [Store.setVar, abs_of_neg hx]
  · simp [conditions, absoluteValue, lower, vcgen, BExpr.eval, IExpr.eval, hx]
    refine ⟨s.setVar "y" (s.vars "x"), ?_, ?_⟩
    · simp [assign, IExpr.eval]
    · simp [Store.setVar, abs_of_nonneg (le_of_not_gt hx)]

/-- The concrete integer-language example is connected to executable
code by the same general soundness theorem as the larger examples. -/
theorem absoluteValue_verified (s : Store) :
    (∃ t bound, (t.vars "x" = s.vars "x" ∧ t.vars "y" = |s.vars "x"|) ∧
      ∀ fuel, bound ≤ fuel → run fuel absoluteValue s = .done t) ∧
      (∀ fuel, run fuel absoluteValue s ≠ .fault) :=
  verified_program _ _ _ (absoluteValue_conditions s)

end MiniVerify.Language
