import Flapjack.Test.Pipeline

namespace Flapjack

open RiscV

example :
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
        (wordStackInitialBitmaps false)
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some ([], wordStackInitialBitmaps false) := by
  rfl

#guard
    (compileFlapjackRiscVViaAllocatedStackWithBitmaps (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineStackAddDeclarations).isSome

end Flapjack
