import Flapjack.RiscV.LinearScanPipeline

/-! Regression coverage for function-level linear-scan pipeline integration. -/

namespace Flapjack

example :
    (wordAllocateLinearScanFunction [] (.skip : WordProg Nat) 2 0).isSome =
      true := by
  decide +kernel

example :
    (wordAllocateLinearScanFunctionWithEntry [] (.skip : WordProg Nat) 2 0).isSome =
      true := by
  decide +kernel

example :
    pipelineWordFunctionsAllocatedWithLinearScan
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithLinearScan
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

example
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunction parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  exact wordAllocateLinearScanFunction_maps_parameters
    parameters program colours stackStart state renamedParameters allocation
    renamedProgram halloc

example
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunctionWithEntry parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  exact wordAllocateLinearScanFunctionWithEntry_maps_parameters
    parameters program colours stackStart state renamedParameters allocation
    renamedProgram halloc

end Flapjack
