import Flapjack.RiscV.AllocationModePipeline

/-! Regression coverage for CakeML numeric allocation-mode dispatch. -/

namespace Flapjack

example : wordAllocationAlgorithmOfNat 0 = .simple := by
  decide

example : wordAllocationAlgorithmOfNat 3 = .ircHeuristic := by
  decide

example : wordAllocationAlgorithmOfNat 19 = .linearScan := by
  decide

example :
    wordAllocationAlgorithmUsesHeuristics
      (wordAllocationAlgorithmOfNat 3) = true := by
  decide

example :
    wordAllocationAlgorithmIsLinearScanNat 4 = true := by
  decide

example :
    pipelineWordFunctionsAllocatedWithSourceAlgorithm 4
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithSourceAlgorithm 2
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

end Flapjack
