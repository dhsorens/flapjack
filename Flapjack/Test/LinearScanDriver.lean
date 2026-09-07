import Flapjack.RiscV.LinearScanPipeline

/-! Regression coverage for function-level linear-scan pipeline integration. -/

namespace Flapjack

example :
    (wordAllocateLinearScanFunction [] (.skip : WordProg Nat) 2 0).isSome =
      true := by
  native_decide

example :
    pipelineWordFunctionsAllocatedWithLinearScan
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithLinearScan
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  native_decide

end Flapjack
