import Flapjack.RiscV.HeuristicPipeline

/-! Regression coverage for the heuristic-allocated RISC-V pipeline. -/

namespace Flapjack

example :
    pipelineWordFunctionsAllocatedWithHeuristics 1
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithHeuristics 1
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

#guard
    (pipelineWordFunctionsAllocatedWithHeuristics 1
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome = true

end Flapjack
