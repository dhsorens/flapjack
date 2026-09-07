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
    (wordCheckLiveTree id (.seq (.reads [1, 2]) (.writes [1])) [] []).isSome =
      true := by
  native_decide

example :
    wordFixLiveTree (.reads [1, 2]) =
      .seq (.writes [1, 2]) (.reads [1, 2]) := by
  native_decide

end Flapjack
