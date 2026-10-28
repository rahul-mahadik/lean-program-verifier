import MiniVerify

open MiniVerify

private def report (label : String) (render : σ → String) (outcome : Outcome σ) : IO UInt32 := do
  match outcome with
  | .done s => IO.println s!"{label}: {render s}"; pure 0
  | .fault => IO.eprintln s!"{label}: runtime fault"; pure 2
  | .timeout => IO.eprintln s!"{label}: interpreter budget exhausted"; pure 3

private def reverseArray (a : Array Int) : IO UInt32 :=
  report "reverse" (fun s => reprStr s.data)
    (run (4 * (a.size + 1) ^ 2 + 20) (Examples.Reverse.program a) ⟨a, 0⟩)

private def sortArray (a : Array Int) : IO UInt32 :=
  report "insertion sort" (fun s => reprStr s.data)
    (run (4 * (a.size + 1) ^ 2 + 20)
      (Examples.InsertionSort.program a) (Examples.InsertionSort.initial a))

private def searchArray (a : Array Int) (target : Int) : IO UInt32 := do
  if Examples.BinarySearch.sortedCheck a then
    report s!"search {target}" (fun (s : Examples.BinarySearch.State) => reprStr s.result)
      (run (4 * (a.size + 1) ^ 2 + 20)
        (Examples.BinarySearch.program a target) (Examples.BinarySearch.initial a target))
  else
    IO.eprintln "search: input must be sorted in nondecreasing order"
    pure 1

private def demo : IO UInt32 := do
  IO.println "MiniVerify: executable programs with proved total correctness"
  let c1 ← reverseArray #[1, 2, 3, 4, 5]
  let c2 ← sortArray #[5, 2, 4, 2, -1]
  let c3 ← searchArray #[-1, 2, 2, 4, 5] 4
  let c4 ← searchArray #[-1, 2, 2, 4, 5] 3
  let c5 ← report "surface-language abs(-7)" (fun s => toString (s.vars "y"))
    (Language.run 8 Language.absoluteValue (Language.Store.empty.setVar "x" (-7)))
  pure (if [c1, c2, c3, c4, c5].all (· == 0) then 0 else 1)

private def parseInts : List String → Except String (List Int)
  | [] => .ok []
  | arg :: rest => do
      let value ← match arg.toInt? with
        | some value => .ok value
        | none => .error s!"invalid integer: {arg}"
      let tail ← parseInts rest
      pure (value :: tail)

private def usage : IO Unit := do
  IO.println "Usage: miniverify [demo | reverse <integers...> | sort <integers...> | search <target> <sorted integers...>]"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["demo"] => demo
  | "reverse" :: values =>
      match parseInts values with
      | .ok values => reverseArray values.toArray
      | .error message => IO.eprintln message; pure 1
  | "sort" :: values =>
      match parseInts values with
      | .ok values => sortArray values.toArray
      | .error message => IO.eprintln message; pure 1
  | "search" :: target :: values =>
      match parseInts (target :: values) with
      | .ok (target :: values) => searchArray values.toArray target
      | .ok [] => usage; pure 1
      | .error message => IO.eprintln message; pure 1
  | _ => usage; pure 1
