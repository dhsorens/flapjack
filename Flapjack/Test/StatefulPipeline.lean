import Flapjack.Pipeline

namespace Flapjack

open RiscV

/-! A small pair of Loop functions exercises the stateful allocator pipeline
    at the same list boundary used by the end-to-end compiler entry point. -/
def statefulPipelineFunctions :
    List (Nat × List Nat × LoopProg (RiscV.Word 64)) :=
  [(0, [], (.assign 1 (.const (BitVec.ofNat 64 7)) : LoopProg (RiscV.Word 64))),
   (1, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64)))]

example :
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
        (wordStackInitialBitmaps false)
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some ([], wordStackInitialBitmaps false) := by
  rfl

#guard
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
        (wordStackInitialBitmaps false) statefulPipelineFunctions |>.isSome

example :
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
        (wordStackInitialBitmaps false)
        (statefulPipelineFunctions ++ []) =
      match pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
          (wordStackInitialBitmaps false) statefulPipelineFunctions with
      | none => none
      | some (compiled, bitmaps) => some (compiled ++ [], bitmaps) := by
  exact pipelineWordFunctionsAllocatedWithSpillsAndBitmaps_append _ _ _

end Flapjack
