import Flapjack.RiscV.Allocator

namespace Flapjack

/-! Regression for the CakeML cut-set shape of call clash trees. -/

example :
    wordClashTree
        (.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8] none : WordProg Nat) [] =
      .seq (.set [5, 6]) (.set [8, 6]) := by
  simp [wordClashTree, wordClashTreeCallSet, 
    List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordClashTree
        (.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8]
          (some (9, .return 0 [10], 0, 0)) : WordProg Nat) [] =
      .branch (some [6, 8])
        (.seq (.set [5, 6]) (.set [6, 8]))
        (.seq (.set [9, 6]) (.delta [] [10])) := by
  simp [wordClashTree, wordClashTreeCallSet, wordClashTreeCallCutSet,
    List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

end Flapjack
