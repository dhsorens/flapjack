import Flapjack.RiscV.SpillCosts

/-! Regression coverage for CakeML spill costs and canonicalized moves. -/

namespace Flapjack

example :
    wordGetSpillCost
      { lhsConst := 1, lhsReg := 2, lhsMem := 3, rhsReg := 4, rhsMem := 5 }
      false = 45 := by
  decide

example :
    wordGetSpillCost
      { lhsConst := 1, lhsReg := 2, lhsMem := 3, rhsReg := 4, rhsMem := 5 }
      true = 225 := by
  decide

example :
    wordRaChooseSpillNodeByDegree [(3, 2), (5, 5), (7, 4)] 3 [5, 7] = 5 := by
  decide

example :
    wordRaChooseSpillNode [(3, 100), (5, 20), (7, 30)] [(3, 10), (5, 1), (7, 2)] 3 [5, 7] = 3 := by
  decide

example :
    wordCanonicalizeMoves
        [{ priority := 4, left := 7, right := 2 },
         { priority := 9, left := 2, right := 7 },
         { priority := 3, left := 1, right := 0 }] =
      [{ count := 2, maxPriority := 9, left := 2, right := 7 },
       { count := 1, maxPriority := 3, left := 0, right := 1 }] := by
  decide

example :
    (wordGetHeuristics 1 7 (.move 9 [(1, 2)] : WordProg Nat)).1 =
      [{ priority := 102, left := 1, right := 2 }] := by
  decide +kernel

example :
    (wordGetHeuristics 2 7 (.move 9 [(1, 2)] : WordProg Nat)).1 =
      [{ priority := 9, left := 1, right := 2 }] := by
  decide +kernel

example :
    (wordGetHeuristics 1 7 (.move 9 [(1, 2)] : WordProg Nat)).2.isSome = true := by
  decide

example :
    (wordAllocateGraphFunctionWithHeuristics
      [] (.move 9 [(0, 1)] : WordProg Nat) [] 1 7 13 26).isSome = true := by
  decide +kernel

example :
    (wordAllocateGraphFunctionWithHeuristics
      [] (.move 9 [(0, 1)] : WordProg Nat) [] 0 7 13 26).isSome = true := by
  decide +kernel

example :
    (wordAllocateGraphFunctionWithHeuristics
      [] (.move 9 [(0, 1)] : WordProg Nat) [] 2 7 13 26).isSome = true := by
  decide +kernel

example :
    (wordAllocateGraphFunctionWithHeuristicsEntryRenamed
      [] (.move 9 [(0, 1)] : WordProg Nat) [] 1 7 13 26).isSome = true := by
  decide +kernel

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

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg Nat)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true := by
  exact (wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound parameters program
    fixedSources algorithm currentFunction colours stackStart state
    renamedParameters allocation renamedProgram halloc).1

end Flapjack
