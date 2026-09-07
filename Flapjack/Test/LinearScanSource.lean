import Flapjack.RiscV.LinearScanSource

/-! Regression coverage for the source-faithful linear-scan checks. -/

namespace Flapjack

def linearScanSourceShape : WordClashTree → Bool
  | .seq (.delta writes reads) (.set names) =>
      writes == [1] && reads == [3] && names == [5]
  | _ => false

def linearScanSecondColour :
    Option (WordLinearScanState × List Nat × WordLinearScanState) → Bool
  | some (_, [3], second) =>
      (lookupNatInfo 3 second.colours == some 2)
  | _ => false

def linearScanSourceAllocationShape : Option WordLinearScanSourceAllocation → Bool
  | some allocation =>
      allocation.normalizedRegisters == [3, 1] &&
        allocation.stackRegisters == [3] &&
        lookupNatInfo 5 allocation.colouring == some 0 &&
        lookupNatInfo 7 allocation.colouring == some 2
  | _ => false

example :
    wordFixDomination (.reads [1, 2]) =
      .seq (.writes [1, 2]) (.reads [1, 2]) := by
  decide +kernel

example :
    wordCheckNumberProperty (fun _ _ => true)
      (.branch (.reads [1]) (.writes [2])) 4 [] = true := by
  decide +kernel

example :
    wordCheckNumberPropertyStrong (fun _ _ => true)
      (.seq (.reads [1]) (.writes [2])) 4 [] = true := by
  decide +kernel

example :
    wordCheckStartLive (.writes [1]) 2 [(1, 0)] [(1, 4)] 0 = true := by
  decide +kernel

example :
    wordPointInsideInterval (2, 5) 4 = true := by
  decide

example :
    wordCheckIntervals (fun _ => 0) [(1, 0), (2, 1)] [(1, 3), (2, 2)] = false := by
  decide

example :
    let state := wordLinearScanBijection
      (.delta [5] [7] : WordClashTree)
    lookupNatInfo 5 state.toNode = some 1 &&
      lookupNatInfo 7 state.toNode = some 3 &&
      state.nextAlloc = 5 && state.nextStack = 7 := by
  decide +kernel

example :
    let state := wordLinearScanBijection
      (.delta [10] [3] : WordClashTree)
    lookupNatInfo 10 state.toNode = some 10 &&
      lookupNatInfo 3 state.toNode = some 3 &&
      state.nextAlloc = 1 && state.nextStack = 7 := by
  decide +kernel

example :
    let tree := .seq (.delta [5] [7]) (.set [1])
    let state := wordLinearScanBijection (tree : WordClashTree)
    linearScanSourceShape (wordLinearScanApplyBijectionTree tree state) = true := by
  decide +kernel

example :
    let state := wordLinearScanBijection
      (.delta [5] [7] : WordClashTree)
    wordLinearScanApplyBijectionForced state [(5, 7)] = [(1, 3)] := by
  decide +kernel

example :
    wordLinearScanAdjacency [(1, 2)] =
      [(2, [1]), (1, [2])] := by
  decide

example :
    (wordLinearScanTwoPass 2 [] [] [1, 3]
      [(1, 0), (3, 1)] [(1, 2), (3, 3)]).isSome = true := by
  decide +kernel

example :
    linearScanSecondColour (wordLinearScanTwoPass 2 [] [] [1, 3]
      [(1, 0), (3, 1)] [(1, 2), (3, 3)]) = true := by
  decide +kernel

example :
    wordLinearScanSortRegistersSource
      [(1, 0), (2, 0), (3, -1)] [2, 1, 3] = [3, 1, 2] := by
  decide +kernel

example :
    wordLinearScanSortMovesSource
      [{ priority := 3, left := 1, right := 2 },
       { priority := 1, left := 3, right := 4 }] =
      [{ priority := 1, left := 3, right := 4 },
       { priority := 3, left := 1, right := 2 }] := by
  decide +kernel

example :
    linearScanSourceAllocationShape
      (wordLinearScanAllocateSource 2 [] []
        (.delta [5] [7] : WordClashTree)) = true := by
  decide +kernel

example :
    let state :=
      { (wordLinearScanInitialState 3 3) with
        colours := [(2, 1), (4, 0)] }
    let exchanged := wordLinearScanApplyRegisterExchange [2, 4] state
    lookupNatInfo 2 exchanged.colours = some 1 &&
      lookupNatInfo 4 exchanged.colours = some 2 := by
  decide

end Flapjack
