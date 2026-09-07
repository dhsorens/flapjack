import Flapjack.RiscV.Allocator

namespace Flapjack

/-! Regression for the CakeML cut-set shape of call clash trees. -/

example :
    wordClashTree
        (.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8] none : WordProg Nat) [] =
      .seq (.set [6, 8])
        (.seq (.set [5, 6]) (.delta [] [])) := by
  simp [wordClashTree, wordClashTreeCallSet, wordClashTreeCallCutSet,
    List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordClashTree
        (.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8]
          (some (9, .return 0 [10], 0, 0)) : WordProg Nat) [] =
      .branch (some [6, 8])
        (.seq (.set [5, 6]) (.delta [] []))
        (.seq (.set [9, 6]) (.delta [] [10])) := by
  simp [wordClashTree, wordClashTreeCallSet, wordClashTreeCallCutSet,
    List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordClashTree
        (.alloc 3 ([4], [5, 6]) : WordProg Nat) [] =
      .seq (.delta [] [3]) (.set [4, 5, 6]) := by
  simp [wordClashTree, wordClashTreeCallSet, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordClashTree
        (.storeConsts 1 2 3 4 [] : WordProg Nat) [] =
      .delta [1, 2, 3, 4] [3, 4] := by
  simp [wordClashTree]

example :
    wordClashTree
        (.install 1 2 3 4 ([5], [6]) : WordProg Nat) [] =
      .seq (.delta [] [4, 3, 2, 1])
        (.seq (.set [5, 6]) (.delta [1] [])) := by
  simp [wordClashTree, wordClashTreeCallSet, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordClashTree
        (.ffi "f" 1 2 3 4 ([5], [6]) : WordProg Nat) [] =
      .seq (.delta [] [1, 2, 3, 4]) (.set [5, 6]) := by
  simp [wordClashTree, wordClashTreeCallSet, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

end Flapjack
