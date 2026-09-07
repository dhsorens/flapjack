import Flapjack.RiscV.SpillCosts

/-! Regression coverage for CakeML spill costs and canonicalized moves. -/

namespace Flapjack

example :
    wordGetSpillCost
      { lhsConst := 1, lhsReg := 2, lhsMem := 3, rhsReg := 4, rhsMem := 5 }
      false = 45 := by
  native_decide

example :
    wordGetSpillCost
      { lhsConst := 1, lhsReg := 2, lhsMem := 3, rhsReg := 4, rhsMem := 5 }
      true = 225 := by
  native_decide

example :
    wordCanonicalizeMoves
        [{ priority := 4, left := 7, right := 2 },
         { priority := 9, left := 2, right := 7 },
         { priority := 3, left := 1, right := 0 }] =
      [{ count := 2, maxPriority := 9, left := 2, right := 7 },
       { count := 1, maxPriority := 3, left := 0, right := 1 }] := by
  native_decide

example :
    (wordGetHeuristics 1 7 (.move 9 [(1, 2)] : WordProg Nat)).1 =
      [{ priority := 102, left := 1, right := 2 }] := by
  native_decide

example :
    (wordGetHeuristics 2 7 (.move 9 [(1, 2)] : WordProg Nat)).1 =
      [{ priority := 9, left := 1, right := 2 }] := by
  native_decide

example :
    (wordGetHeuristics 1 7 (.move 9 [(1, 2)] : WordProg Nat)).2.isSome = true := by
  native_decide

example :
    (wordAllocateGraphFunctionWithHeuristics
      [] (.move 9 [(0, 1)] : WordProg Nat) [] 1 7 13 26).isSome = true := by
  native_decide

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg Nat)
    (halloc : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true := by
  exact (wordAllocateGraphFunctionWithHeuristics_sound parameters program
    fixedSources algorithm currentFunction colours stackStart state
    renamedParameters allocation renamedProgram halloc).1

end Flapjack
