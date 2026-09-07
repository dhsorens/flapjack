import Flapjack.RiscV.CorrectnessFfi

/-!
Regression for a loop-control result crossing a handler-free call boundary.
The callee immediately breaks, so the caller must receive the same break
label and the caller's mapped locals must remain intact.
-/

namespace Flapjack

open RiscV

def loopCallControlLoopState : LoopState (Word 64) :=
  { locals := fun name => if name = 2 then some (BitVec.ofNat 64 9) else none
    globals := fun _ => none
    memory := fun _ => none }

def loopCallControlWordState : State 64 :=
  writeRegister (zeroState 64) 2 9

theorem loopCallControl_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      loopCallControlLoopState.locals loopCallControlWordState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    refine ⟨2, by native_decide, ?_⟩
    simpa [loopCallControlLoopState, loopCallControlWordState,
      readRegister, writeRegister] using hvalue
  · simp [loopCallControlLoopState, hname] at hvalue

theorem loopCallControl_break_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.broke loopCallControlLoopState 0)
      (.broke loopCallControlWordState 0) := by
  apply loopToWord_call_loop_control_simulation_single_parameter
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], (.break 0 : LoopProg (Word 64)))])
    (wordFunctions := [(1, [10], (.break 0 : WordProg (Word 64)))])
    (loopState := loopCallControlLoopState)
    (wordState := loopCallControlWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (argumentValue := BitVec.ofNat 64 9)
    (fuel := 3)
    (loopBody := (.break 0 : LoopProg (Word 64)))
    (parameterRegister := 10)
    (loopResult := .broke loopCallControlLoopState 0)
    (wordResult := .broke loopCallControlWordState 0)
    (hlookupLoop := by simp [lookupLoopFunction])
    (hlookupWord := by simp [lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg])
    (hparameter := by native_decide)
    (hparameter_nonzero := by decide)
    (hargument := by simp [loopCallControlLoopState])
    (hbody := by
      intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
      cases bodyResult <;> cases bodyWordResult <;>
        simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
          loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi] at hloop hword ⊢ <;>
        rcases hloop with ⟨rfl, rfl⟩ <;>
        rcases hword with ⟨rfl, rfl⟩ <;>
        exact ⟨rfl, hcallee⟩)
    (hlocals := loopCallControl_mapped_locals)
    (hloop := by
      simp [evalLoopCallWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
        lookupLoopFunction, loopCallControlLoopState, loopReadLocals,
        loopBindParameters])
    (hword := by
      simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
        loopCallControlWordState, writeRegister,
        readRegister, RiscV.readWordRegisters, RiscV.bindWordRegisters,
        RiscV.clearWordRegisters, registerOfNat, wordFindVar, lookupNatInfo])

def loopCallFfiBody : LoopProg (Word 64) :=
  .ffi "identity" 10 10 10 10 []

theorem loopCallFfi_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.normal loopCallControlLoopState)
      (.normal loopCallControlWordState) := by
  apply loopToWord_call_loop_control_simulation_single_parameter
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], loopCallFfiBody)])
    (wordFunctions := [(1, [10], loopToWordProg
      ({ vars := [] } : WordContext) loopCallFfiBody)])
    (loopState := loopCallControlLoopState)
    (wordState := loopCallControlWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (argumentValue := BitVec.ofNat 64 9)
    (fuel := 3)
    (loopBody := loopCallFfiBody)
    (parameterRegister := 10)
    (loopResult := .normal loopCallControlLoopState)
    (wordResult := .normal loopCallControlWordState)
    (hlookupLoop := by simp [lookupLoopFunction, loopCallFfiBody])
    (hlookupWord := by simp [lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg, loopCallFfiBody])
    (hparameter := by native_decide)
    (hparameter_nonzero := by decide)
    (hargument := by simp [loopCallControlLoopState])
    (hbody := by
      intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
      cases bodyResult with
      | normal loopResult =>
          cases bodyWordResult with
          | normal wordResult =>
              exact loopToWord_ffi_loop_simulation
                (context := ({ vars := [] } : WordContext))
                (primitive := fun _ _ => none)
                (functions := [(1, [10], loopCallFfiBody)])
                (wordFunctions := [(1, [10], loopToWordProg
                  ({ vars := [] } : WordContext) loopCallFfiBody)])
                (loopState := calleeLoop)
                (wordState := calleeWord)
                (loopHandler := fun _ _ _ _ _ state => some state)
                (wordHandler := fun _ _ _ _ _ state => some state)
                (handler_agrees := by
                  intro function configuration configurationLength array arrayLength
                    loopInput wordInput loopOutput wordOutput hlocals hloop hword
                  simp at hloop hword
                  cases hloop
                  cases hword
                  exact hlocals)
                (function := "identity")
                (configuration := 10)
                (configurationLength := 10)
                (array := 10)
                (arrayLength := 10)
                (live := [])
                (fuel := 2)
                (hlocals := hcallee)
                loopResult wordResult hloop hword
          | returned wordState values =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | raised wordState exception =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | broke wordState label =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | continued wordState label =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
      | returned loopState values =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | raised loopState exception =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | broke loopState label =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | continued loopState label =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop)
    (hlocals := loopCallControl_mapped_locals)
    (hloop := by
      simp [evalLoopCallWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, 
        lookupLoopFunction, loopCallFfiBody, loopCallControlLoopState,
        loopReadLocals, loopBindParameters, updateLoopLocal])
    (hword := by
      simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
        loopToWordProg, loopCallFfiBody, loopCallControlWordState,
        writeRegister, readRegister, RiscV.readWordRegisters,
        RiscV.bindWordRegisters, RiscV.clearWordRegisters,
        registerOfNat, wordFindVar, lookupNatInfo])

end Flapjack
