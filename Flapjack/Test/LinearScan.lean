import Flapjack.RiscV.LinearScan

/-! Regression coverage for the linear-scan live-tree boundary. -/

namespace Flapjack

example :
    wordGetLiveTree
      (.delta [1, 2] [3] : WordClashTree) =
      .seq (.reads [3]) (.writes [1, 2]) := by
  native_decide

example :
    wordGetLiveBackward
      (.seq (.writes [1]) (.reads [1, 2])) [] = [2] := by
  native_decide

example :
    wordLiveTreeRegisters
      (.branch (.reads [1, 2]) (.writes [2, 3])) = [1, 2, 3] := by
  native_decide

example :
    wordIntervalAddIfLt [4] 3 [(4, 5)] =
      [(4, 3)] := by
  native_decide

example :
    wordIntervalAddIfGt [4] 7 [(4, 5)] =
      [(4, 7)] := by
  native_decide

example :
    wordGetIntervals
      (.seq (.reads [1]) (.writes [1])) 2 [] [] =
      (0, [(1, 2)], [(1, 2)]) := by
  native_decide

example :
    wordIntervalIntersect (2, 5) (4, 8) = true := by
  native_decide

example :
    wordLinearScanSortRegisters [(1, 2), (5, 0)] [1, 5] = [5, 1] := by
  native_decide

example :
    let state := wordLinearScanStep [] [] 1 0 5 false
      (wordLinearScanInitialState 1 0)
    lookupNatInfo 1 state.colours = some 0 := by
  native_decide

example :
    let state := wordLinearScanStep [] [] 1 0 5 false
      (wordLinearScanInitialState 1 0)
    let state := wordLinearScanStep [] [] 5 1 3 false state
    lookupNatInfo 1 state.locations = some (.stack 0) &&
      lookupNatInfo 5 state.locations = some (.register 2) := by
  native_decide

example :
    (wordLinearScanAllocateRegisters
      (fun _ => []) (fun _ => []) [1, 5]
      [(1, 0), (5, 1)] [(1, 5), (5, 3)]
      (wordLinearScanInitialState 1 0)).isSome = true := by
  native_decide

example :
    let state := wordLinearScanInitialState 2 0
    let state := { state with colours := [(2, 0), (4, 1)] }
    wordLinearScanForcedColours [(1, 2), (1, 4)] 1 state = [0, 1] := by
  native_decide

example :
    let state := wordLinearScanInitialState 2 0
    let state := { state with colours := [(2, 0)] }
    wordLinearScanPreferredColours
      [{ priority := 7, left := 1, right := 2 }] 1 state = [0] := by
  native_decide

example :
    (wordLinearScanAllocateClashTree 2 0
      (.seq (.delta [1] []) (.delta [5] []))
      [] []).isSome = true := by
  native_decide

example :
    (wordCheckLiveTree id (.seq (.reads [1, 2]) (.writes [1])) [] []).isSome =
      true := by
  native_decide

example :
    wordFixLiveTree (.reads [1, 2]) =
      .seq (.writes [1, 2]) (.reads [1, 2]) := by
  native_decide

end Flapjack
