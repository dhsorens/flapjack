import Flapjack.RiscV.LinearScanSource

/-! Regression coverage for the source-faithful linear-scan checks. -/

namespace Flapjack

def linearScanSourceShape : WordClashTree → Bool
  | .seq (.delta writes reads) (.set names) =>
      writes == [1] && reads == [3] && names == [5]
  | _ => false

example :
    wordFixDomination (.reads [1, 2]) =
      .seq (.writes [1, 2]) (.reads [1, 2]) := by
  native_decide

example :
    wordCheckNumberProperty (fun _ _ => true)
      (.branch (.reads [1]) (.writes [2])) 4 [] = true := by
  native_decide

example :
    wordCheckNumberPropertyStrong (fun _ _ => true)
      (.seq (.reads [1]) (.writes [2])) 4 [] = true := by
  native_decide

example :
    wordCheckStartLive (.writes [1]) 2 [(1, 0)] [(1, 4)] 0 = true := by
  native_decide

example :
    wordPointInsideInterval (2, 5) 4 = true := by
  native_decide

example :
    wordCheckIntervals (fun _ => 0) [(1, 0), (2, 1)] [(1, 3), (2, 2)] = false := by
  native_decide

example :
    let state := wordLinearScanBijection
      (.delta [5] [7] : WordClashTree)
    lookupNatInfo 5 state.toNode = some 1 &&
      lookupNatInfo 7 state.toNode = some 3 &&
      state.nextAlloc = 5 && state.nextStack = 7 := by
  native_decide

example :
    let state := wordLinearScanBijection
      (.delta [10] [3] : WordClashTree)
    lookupNatInfo 10 state.toNode = some 10 &&
      lookupNatInfo 3 state.toNode = some 3 &&
      state.nextAlloc = 1 && state.nextStack = 7 := by
  native_decide

example :
    let tree := .seq (.delta [5] [7]) (.set [1])
    let state := wordLinearScanBijection (tree : WordClashTree)
    linearScanSourceShape (wordLinearScanApplyBijectionTree tree state) = true := by
  native_decide

example :
    let state := wordLinearScanBijection
      (.delta [5] [7] : WordClashTree)
    wordLinearScanApplyBijectionForced state [(5, 7)] = [(1, 3)] := by
  native_decide

end Flapjack
