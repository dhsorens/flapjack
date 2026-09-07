import Flapjack.Test.CorrectnessLoopHandlers

/-!
Regression for loop-control propagation after a foreign call.  The FFI
action completes normally, while the following `break` must be propagated by
both evaluators and remain related at the loop boundary.
-/

namespace Flapjack

open RiscV

theorem loopFfi_break_control_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.broke loopFfiSimulationLoopState 0)
      (.broke loopFfiSimulationWordState 0) := by
  apply loopToWord_seq_loop_control_simulation
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [])
    (wordFunctions := [])
    (loopState := loopFfiSimulationLoopState)
    (wordState := loopFfiSimulationWordState)
    (loopHandler := loopFfiSimulationLoopHandler)
    (wordHandler := loopFfiSimulationWordHandler)
    (fuel := 3)
    (first := .ffi "identity" 1 2 3 4 [])
    (second := .break 0)
    (loopResult := .broke loopFfiSimulationLoopState 0)
    (wordResult := .broke loopFfiSimulationWordState 0)
    (hfirst := by
      intro firstResult firstWordResult hloop hword
      cases firstResult with
      | normal loopResult =>
          cases firstWordResult with
          | normal wordResult =>
              exact loopToWord_ffi_loop_simulation
                (context := ({ vars := [] } : WordContext))
                (primitive := fun _ _ => none)
                (functions := [])
                (wordFunctions := [])
                (loopState := loopFfiSimulationLoopState)
                (wordState := loopFfiSimulationWordState)
                (loopHandler := loopFfiSimulationLoopHandler)
                (wordHandler := loopFfiSimulationWordHandler)
                (handler_agrees := by
                  intro function configuration configurationLength array arrayLength
                    loopInput wordInput loopOutput wordOutput hlocals hloop hword
                  simp [loopFfiSimulationLoopHandler, loopFfiSimulationWordHandler]
                    at hloop hword
                  cases hloop
                  cases hword
                  exact hlocals)
                (function := "identity")
                (configuration := 1)
                (configurationLength := 2)
                (array := 3)
                (arrayLength := 4)
                (live := [])
                (fuel := 2)
                (hlocals := by
                  exact loopFfi_simulation_mapped_locals)
                loopResult wordResult hloop hword
          | returned wordState values =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
                lookupNatInfo, loopFfiSimulationWordState, writeRegister,
                ] at hword
          | raised wordState exception =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
                lookupNatInfo, loopFfiSimulationWordState, writeRegister,
                ] at hword
          | broke wordState label =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
                lookupNatInfo, loopFfiSimulationWordState, writeRegister,
                ] at hword
          | continued wordState label =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
                lookupNatInfo, loopFfiSimulationWordState, writeRegister,
                ] at hword
      | returned loopState values =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi,
            loopFfiSimulationLoopHandler, loopFfiSimulationLoopState] at hloop
      | raised loopState exception =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi,
            loopFfiSimulationLoopHandler, loopFfiSimulationLoopState] at hloop
      | broke loopState label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi,
            loopFfiSimulationLoopHandler, loopFfiSimulationLoopState] at hloop
      | continued loopState label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi,
            loopFfiSimulationLoopHandler, loopFfiSimulationLoopState] at hloop)
    (hsecond := by
      intro middleLoop middleWord secondResult secondWordResult hlocals hloop hword
      cases secondResult <;> cases secondWordResult <;>
        simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
          loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
          ] at hloop hword ⊢ <;>
        rcases hloop with ⟨rfl, rfl⟩ <;>
        rcases hword with ⟨rfl, rfl⟩ <;>
        exact ⟨rfl, hlocals⟩)
    (hloop := by
      simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
        loopFfiSimulationLoopHandler, loopFfiSimulationLoopState])
    (hword := by
      simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
        loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
        lookupNatInfo])

end Flapjack
