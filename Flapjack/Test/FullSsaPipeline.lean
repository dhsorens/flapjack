import Flapjack.Pipeline

namespace Flapjack

open RiscV

/-! Regression for the full-SSA entry sequence through graph allocation and
    Word-to-Stack lowering. -/

#guard
    (pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

example :
    pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) = some [] := by
  rfl

end Flapjack
