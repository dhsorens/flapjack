import Flapjack.RiscV.LinearScanSource

/-! Regression coverage for the source-faithful linear-scan checks. -/

namespace Flapjack

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

end Flapjack
