import Flapjack.RiscV.Heuristics

/-! Executable regressions for CakeML's Word heuristic summary and priorities. -/

namespace Flapjack

def heuristicValue (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : WordHeuristicCounts :=
  match lookupNatInfo name counts with
  | some value => value
  | none => wordHeuristicZero

example :
    heuristicValue 0
      (wordHeuristic 7 (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat) ([], [])).1 =
      { lhsConst := 0, lhsReg := 1, lhsMem := 0, rhsReg := 0, rhsMem := 0 } := by
  native_decide

example :
    heuristicValue 3
      (wordHeuristic 7 (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat) ([], [])).1 =
      { lhsConst := 0, lhsReg := 0, lhsMem := 0, rhsReg := 1, rhsMem := 0 } := by
  native_decide

example :
    heuristicValue 9
      (wordHeuristic 7
        (.seq (.move 5 [(9, 10)]) (.inst (.mem .store32 9 12)) : WordProg Nat)
          ([], [])).1 =
      { lhsConst := 0, lhsReg := 1, lhsMem := 0, rhsReg := 0, rhsMem := 1 } := by
  native_decide

example :
    heuristicValue 4
      (wordHeuristic 7
        (.ite .equal 4 (.reg 5) (.get 4 .currHeap) (.get 4 .currHeap) : WordProg Nat)
          ([], [])).1 =
      { lhsConst := 0, lhsReg := 0, lhsMem := 1, rhsReg := 1, rhsMem := 0 } := by
  native_decide

example :
    wordProgPrioritizedMoves
        (.seq (.move 7 [(1, 2)]) (.assign 3 (.var 4)) : WordProg Nat) =
      [{ priority := 7, left := 1, right := 2 },
       { priority := 0, left := 3, right := 4 }] := by
  native_decide

example :
    (wordAllocateGraphProgramWithPriorities
      (.move 9 [(0, 1)] : WordProg Nat) [] 13 26).isSome = true := by
  native_decide

end Flapjack
