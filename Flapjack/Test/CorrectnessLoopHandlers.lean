import Flapjack.RiscV.CorrectnessFfi

/-!
Regression for the loop-aware FFI simulation boundary.  The source side uses
the fully composed Loop evaluator, while the target side uses the control-
result Word loop evaluator introduced for calls and foreign actions in loop
bodies.
-/

namespace Flapjack

open RiscV

def loopFfiSimulationLoopState : LoopState (Word 64) :=
  { locals := fun name =>
      if name = 1 then some (BitVec.ofNat 64 10)
      else if name = 2 then some (BitVec.ofNat 64 1)
      else if name = 3 then some (BitVec.ofNat 64 20)
      else if name = 4 then some (BitVec.ofNat 64 2)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiSimulationWordState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 1 10) 2 1) 3 20) 4 2

def loopFfiSimulationLoopHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun _ _ _ _ _ state => some state

def loopFfiSimulationWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun _ _ _ _ _ state => some state

theorem loopFfi_simulation_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      loopFfiSimulationLoopState.locals loopFfiSimulationWordState := by
  apply loopToWord_ffi_loop_simulation
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
      simp [loopFfiSimulationLoopHandler, loopFfiSimulationWordHandler] at hloop hword
      cases hloop
      cases hword
      exact hlocals)
    (function := "identity")
    (configuration := 1)
    (configurationLength := 2)
    (array := 3)
    (arrayLength := 4)
    (live := [])
    (fuel := 3)
    (hlocals := by
      intro name value hvalue
      by_cases h1 : name = 1
      · subst name
        refine ⟨1, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
        simpa [loopFfiSimulationLoopState, loopFfiSimulationWordState,
          readRegister, writeRegister] using hvalue
      · by_cases h2 : name = 2
        · subst name
          refine ⟨2, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
          simpa [loopFfiSimulationLoopState, loopFfiSimulationWordState,
            readRegister, writeRegister] using hvalue
        · by_cases h3 : name = 3
          · subst name
            refine ⟨3, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
            simpa [loopFfiSimulationLoopState, loopFfiSimulationWordState,
              readRegister, writeRegister] using hvalue
          · by_cases h4 : name = 4
            · subst name
              refine ⟨4, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
              simpa [loopFfiSimulationLoopState, loopFfiSimulationWordState,
                readRegister, writeRegister] using hvalue
            · simp [loopFfiSimulationLoopState, h1, h2, h3, h4] at hvalue)
  · simp [evalLoopProgWithPrimitiveCallsAndFfi,
      loopFfiSimulationLoopHandler, loopFfiSimulationLoopState]
  · simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
      loopFfiSimulationWordHandler, registerOfNat, wordFindVar,
      lookupNatInfo]

end Flapjack
