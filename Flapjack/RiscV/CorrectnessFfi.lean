import Flapjack.Correctness

/-!
Simulation boundary for foreign calls.

The RISC-V model cannot determine the effect of an external function.  This
file therefore states the exact contract needed by `loop_to_word`: whenever
the Loop-side and Word-side host handlers agree on their four arguments and
start from related states, their resulting states remain related.  Under
that contract, the one-step FFI evaluators agree on all mapped locals.
-/

namespace Flapjack.RiscV

theorem loopToWord_ffi_single_simulation [NeZero width]
    (context : WordContext)
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopFfi loopHandler 1 loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFfi wordHandler 1 wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (wordResult, []) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none => simp [evalLoopFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none => simp [evalLoopFfi, hconfig, hconfigLength, harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none => simp [evalLoopFfi, hconfig, hconfigLength, harray, harrayLength] at hloop
              | some arrayLengthValue =>
                  rcases hlocals configuration configurationValue hconfig with
                    ⟨configurationRegister, hconfigurationRegister, hconfigurationValue⟩
                  rcases hlocals configurationLength configurationLengthValue hconfigLength with
                    ⟨configurationLengthRegister, hconfigurationLengthRegister,
                      hconfigurationLengthValue⟩
                  rcases hlocals array arrayValue harray with
                    ⟨arrayRegister, harrayRegister, harrayValue⟩
                  rcases hlocals arrayLength arrayLengthValue harrayLength with
                    ⟨arrayLengthRegister, harrayLengthRegister, harrayLengthValue⟩
                  have hloop' :
                      (loopHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue loopState).bind
                        (fun state => some (LoopResult.normal state)) =
                        some (LoopResult.normal loopResult) := by
                    simpa [evalLoopFfi, hconfig, hconfigLength, harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state => some (state, ([] : List (Word width)))) =
                        some (wordResult, ([] : List (Word width))) := by
                    simpa [loopToWordProg, evalWordFfi,
                      hconfigurationRegister, hconfigurationLengthRegister,
                      harrayRegister, harrayLengthRegister,
                      hconfigurationValue, hconfigurationLengthValue,
                      harrayValue, harrayLengthValue] using hword
                  cases hloopHandler : loopHandler function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue loopState with
                  | none => simp [hloopHandler] at hloop'
                  | some loopOutput =>
                      cases hwordHandler : wordHandler function configurationValue
                          configurationLengthValue arrayValue arrayLengthValue wordState with
                      | none => simp [hwordHandler] at hword'
                      | some wordOutput =>
                          have hloopOutput : loopResult = loopOutput := by
                            simpa [hloopHandler] using hloop'.symm
                          have hwordOutput : wordResult = wordOutput := by
                            simpa [hwordHandler] using hword'.symm
                          subst loopResult
                          subst wordResult
                          exact handler_agrees function configurationValue
                            configurationLengthValue arrayValue arrayLengthValue
                            loopState wordState loopOutput wordOutput hlocals
                            hloopHandler hwordHandler

/-!
The same boundary stated against the combined evaluators is the interface
used once a function body may contain both ordinary calls and foreign calls.
For the one-step FFI constructor the call tables are intentionally
irrelevant, but keeping them in the theorem makes the result compose with
the call-aware induction without changing the state relation.
-/
theorem loopToWord_ffi_single_combined_simulation [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithCallsAndFfi functions loopHandler 1 loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFunctionWithHandlersAndFfi [] wordHandler 1 wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopProgWithCallsAndFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none => simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none => simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength, harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none =>
                  simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength,
                    harray, harrayLength] at hloop
              | some arrayLengthValue =>
                  rcases hlocals configuration configurationValue hconfig with
                    ⟨configurationRegister, hconfigurationRegister,
                      hconfigurationValue⟩
                  rcases hlocals configurationLength configurationLengthValue hconfigLength with
                    ⟨configurationLengthRegister, hconfigurationLengthRegister,
                      hconfigurationLengthValue⟩
                  rcases hlocals array arrayValue harray with
                    ⟨arrayRegister, harrayRegister, harrayValue⟩
                  rcases hlocals arrayLength arrayLengthValue harrayLength with
                    ⟨arrayLengthRegister, harrayLengthRegister,
                      harrayLengthValue⟩
                  have hloop' :
                      (loopHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue loopState).bind
                        (fun state => some (LoopResult.normal state)) =
                        some (LoopResult.normal loopResult) := by
                    simpa [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength,
                      harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state => some (WordControlResult.normal state)) =
                        some (WordControlResult.normal wordResult) := by
                    simpa [loopToWordProg,
                      evalWordFunctionWithHandlersAndFfi,
                      hconfigurationRegister, hconfigurationLengthRegister,
                      harrayRegister, harrayLengthRegister,
                      hconfigurationValue, hconfigurationLengthValue,
                      harrayValue, harrayLengthValue] using hword
                  cases hloopHandler : loopHandler function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue loopState with
                  | none => simp [hloopHandler] at hloop'
                  | some loopOutput =>
                      cases hwordHandler : wordHandler function configurationValue
                          configurationLengthValue arrayValue arrayLengthValue wordState with
                      | none => simp [hwordHandler] at hword'
                      | some wordOutput =>
                          have hloopOutput : loopResult = loopOutput := by
                            simpa [hloopHandler] using hloop'.symm
                          have hwordOutput : wordResult = wordOutput := by
                            simpa [hwordHandler] using hword'.symm
                          subst loopResult
                          subst wordResult
                          exact handler_agrees function configurationValue
                            configurationLengthValue arrayValue arrayLengthValue
                            loopState wordState loopOutput wordOutput hlocals
                            hloopHandler hwordHandler

/-!
The FFI constructor itself does not consume the available fuel.  Expose that
fact at the simulation boundary so callers composing an FFI action with a
larger call-aware computation can choose any positive fuel budget.
-/
theorem loopToWord_ffi_single_combined_simulation_fuel [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (fuel : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithCallsAndFfi functions loopHandler (fuel + 1) loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler (fuel + 1) wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  apply loopToWord_ffi_single_combined_simulation context functions loopState wordState
    loopHandler wordHandler handler_agrees function configuration configurationLength array
    arrayLength live hlocals
  · simpa [evalLoopProgWithCallsAndFfi] using hloop
  · simpa [loopToWordProg, evalWordFunctionWithHandlersAndFfi] using hword

/-!
Compose two normal-returning programs under the call/FFI evaluators.  This is
the sequencing rule needed to resume a caller after an external action.  The
component hypotheses are intentionally explicit: later pass-specific proofs
can supply them for calls, FFI, loops, or ordinary instructions without this
generic rule depending on a particular backend lowering.
-/
theorem loopToWord_seq_combined_simulation [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (finalLoop : LoopState (Word width))
    (finalWord : State width)
    (hfirst : ∀ middleLoop middleWord,
      evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first =
        some (.normal middleLoop) →
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel wordState
        (loopToWordProg context first) = some (.normal middleWord) →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond : ∀ middleLoop middleWord,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      ∀ finalLoop finalWord,
        evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
          some (.normal finalLoop) →
        evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel middleWord
          (loopToWordProg context second) = some (.normal finalWord) →
        loopLocalsMappedToRiscV context finalLoop.locals finalWord)
    (hloop :
      evalLoopProgWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        (.seq first second) = some (.normal finalLoop))
    (hword :
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler (fuel + 1) wordState
        (loopToWordProg context (.seq first second)) = some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases hfirstLoop : evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
                some (.normal finalLoop) := by
            simpa [evalLoopProgWithCallsAndFfi, hfirstLoop] using hloop
          cases hfirstWord :
              evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel wordState
                (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondWord :
                      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                        middleWord (loopToWordProg context second) =
                        some (.normal finalWord) := by
                    simpa [loopToWordProg, evalWordFunctionWithHandlersAndFfi,
                      hfirstWord] using hword
                  exact hsecond middleLoop middleWord
                    (hfirst middleLoop middleWord hfirstLoop hfirstWord)
                    finalLoop finalWord hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
              | raised middleWord exception =>
                  simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
      | returned middleLoop values =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | broke middleLoop label =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | continued middleLoop label =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop

/-!
The loop-aware Word evaluator uses a distinct control-result carrier so that
an FFI action in a loop body can be followed by `break`/`continue` or can be
interrupted by a return or raise.  The one-step FFI rule preserves the same
mapped-local relation when reached through the fully composed Loop evaluator.
-/
theorem loopToWord_ffi_loop_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (fuel : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none =>
              simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig, hconfigLength,
                harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none =>
                  simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig,
                    hconfigLength, harray, harrayLength] at hloop
              | some arrayLengthValue =>
                  rcases hlocals configuration configurationValue hconfig with
                    ⟨configurationRegister, hconfigurationRegister,
                      hconfigurationValue⟩
                  rcases hlocals configurationLength configurationLengthValue hconfigLength with
                    ⟨configurationLengthRegister, hconfigurationLengthRegister,
                      hconfigurationLengthValue⟩
                  rcases hlocals array arrayValue harray with
                    ⟨arrayRegister, harrayRegister, harrayValue⟩
                  rcases hlocals arrayLength arrayLengthValue harrayLength with
                    ⟨arrayLengthRegister, harrayLengthRegister,
                      harrayLengthValue⟩
                  have hloop' :
                      (loopHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue loopState).bind
                        (fun state => some (LoopResult.normal state)) =
                        some (LoopResult.normal loopResult) := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hconfig,
                      hconfigLength, harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state =>
                          some (RiscV.WordLoopControlResult.normal state)) =
                        some (RiscV.WordLoopControlResult.normal wordResult) := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi,
                      hconfigurationRegister, hconfigurationLengthRegister,
                      harrayRegister, harrayLengthRegister,
                      hconfigurationValue, hconfigurationLengthValue,
                      harrayValue, harrayLengthValue] using hword
                  cases hloopHandler : loopHandler function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue loopState with
                  | none => simp [hloopHandler] at hloop'
                  | some loopOutput =>
                      cases hwordHandler : wordHandler function configurationValue
                          configurationLengthValue arrayValue arrayLengthValue wordState with
                      | none => simp [hwordHandler] at hword'
                      | some wordOutput =>
                          have hloopOutput : loopResult = loopOutput := by
                            simpa [hloopHandler] using hloop'.symm
                          have hwordOutput : wordResult = wordOutput := by
                            simpa [hwordHandler] using hword'.symm
                          subst loopResult
                          subst wordResult
                          exact handler_agrees function configurationValue
                            configurationLengthValue arrayValue arrayLengthValue
                            loopState wordState loopOutput wordOutput hlocals
                            hloopHandler hwordHandler

/-!
Normal completion composes through a sequence in the loop-aware evaluator.
This is the control-flow rule used to resume a loop body after an FFI action;
the hypotheses remain abstract so the same rule can later be instantiated for
calls and primitive instructions.
-/
theorem loopToWord_seq_loop_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (finalLoop : LoopState (Word width))
    (finalWord : State width)
    (hfirst : ∀ middleLoop middleWord,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          loopState first = some (.normal middleLoop) →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          wordState (loopToWordProg context first) = some (.normal middleWord) →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond : ∀ middleLoop middleWord,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      ∀ finalLoop finalWord,
        evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
            middleLoop second = some (.normal finalLoop) →
        RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            middleWord (loopToWordProg context second) = some (.normal finalWord) →
        loopLocalsMappedToRiscV context finalLoop.locals finalWord)
    (hloop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState (.seq first second) = some (.normal finalLoop))
    (hword :
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState (loopToWordProg context (.seq first second)) =
        some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases hfirstLoop : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
                  middleLoop second = some (.normal finalLoop) := by
            simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
          cases hfirstWord :
              RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondWord :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                        middleWord (loopToWordProg context second) =
                        some (.normal finalWord) := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  exact hsecond middleLoop middleWord
                    (hfirst middleLoop middleWord hfirstLoop hfirstWord)
                    finalLoop finalWord hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | raised middleWord exception =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | broke middleWord label =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | continued middleWord label =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
      | returned middleLoop values =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | broke middleLoop label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | continued middleLoop label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop

/-!
The loop-aware evaluator carries all five control outcomes.  This relation
extends the ordinary mapped-local observation with return values,
exceptions, and loop labels so that a sequence can be simulated even when
its first component does not complete normally.
-/
def loopResultMappedToWordLoop [NeZero width] (context : WordContext) :
    LoopResult (Word width) → RiscV.WordLoopControlResult width → Prop
  | .normal loopState, .normal wordState =>
      loopLocalsMappedToRiscV context loopState.locals wordState
  | .returned loopState loopValues, .returned wordState wordValues =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordValues = loopValues
  | .raised loopState loopException, .raised wordState wordException =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordException = loopException
  | .broke loopState loopLabel, .broke wordState wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals wordState
  | .continued loopState loopLabel, .continued wordState wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals wordState
  | _, _ => False

/-!
Sequence composition for the complete loop evaluator.  The first component
may terminate normally, in which case the second component is simulated from
the related intermediate states, or it may propagate any other loop control
result unchanged.
-/
theorem loopToWord_seq_loop_control_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (loopResult : LoopResult (Word width))
    (wordResult : RiscV.WordLoopControlResult width)
    (hfirst : ∀ firstResult firstWordResult,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          loopState first = some firstResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          wordState (loopToWordProg context first) = some firstWordResult →
      loopResultMappedToWordLoop context firstResult firstWordResult)
    (hsecond : ∀ middleLoop middleWord secondResult secondWordResult,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          middleLoop second = some secondResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          middleWord (loopToWordProg context second) = some secondWordResult →
      loopResultMappedToWordLoop context secondResult secondWordResult)
    (hloop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState (.seq first second) = some loopResult)
    (hword :
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState (loopToWordProg context (.seq first second)) = some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  cases hfirstLoop : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases hfirstWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            wordState (loopToWordProg context first) with
      | none =>
          simp [loopToWordProg,
            RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
      | some firstWordResult =>
          have hfirstResult := hfirst firstResult firstWordResult hfirstLoop hfirstWord
          cases firstResult with
          | normal middleLoop =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondLoop :
                      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
                          middleLoop second = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hsecondWord :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                          middleWord (loopToWordProg context second) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  exact hsecond middleLoop middleWord loopResult wordResult
                    hfirstResult hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | returned middleLoop values =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord wordValues =>
                  have hloop' :
                      some (.returned middleLoop values) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.returned middleWord wordValues) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | raised middleLoop exception =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord wordException =>
                  have hloop' :
                      some (.raised middleLoop exception) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.raised middleWord wordException) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | broke middleLoop label =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord wordLabel =>
                  have hloop' :
                      some (.broke middleLoop label) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.broke middleWord wordLabel) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | continued middleWord wordLabel =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | continued middleLoop label =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord wordLabel =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord wordLabel =>
                  have hloop' :
                      some (.continued middleLoop label) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.continued middleWord wordLabel) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult

/-!
Handler-free single-parameter calls at a loop boundary.  The callee may
itself use the fully composed primitive/call/FFI evaluator; the abstract
body hypothesis supplies the corresponding five-way Loop/Word relation.
The call dispatcher then proves the caller-frame transition and propagates
all control outcomes.
-/
theorem loopToWord_call_loop_control_simulation_single_parameter [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (target parameter argument : Nat) (argumentValue : Word width)
    (fuel : Nat) (loopBody : LoopProg (Word width))
    (parameterRegister : Fin 32)
    (loopResult : LoopResult (Word width))
    (wordResult : WordLoopControlResult width)
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hbody : ∀ calleeLoop calleeWord bodyResult bodyWordResult,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          calleeLoop loopBody = some bodyResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          calleeWord (loopToWordProg context loopBody) = some bodyWordResult →
      loopResultMappedToWordLoop context bodyResult bodyWordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithPrimitiveCallsAndFfi primitive functions loopHandler
        (fuel + 1) loopState none (some target) [argument] none =
        some loopResult)
    (hword :
      RiscV.evalWordLoopCallWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState none (some target)
        [wordFindVar context argument] none = some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  rcases hlocals argument argumentValue hargument with
    ⟨argumentRegister, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, hcallee⟩
  cases hbodyLoop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop, hreadLoop,
        hcalleeBind, hbodyLoop] at hloop
  | some bodyResult =>
      cases hbodyWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            calleeWord (loopToWordProg context loopBody) with
      | none =>
          simp [RiscV.evalWordLoopCallWithHandlersAndFfi, hlookupWord,
            harguments, hwordBind, hbodyWord] at hword
      | some bodyWordResult =>
          have hbodyResult := hbody { loopState with locals := calleeLocals } calleeWord
            bodyResult bodyWordResult hcallee hbodyLoop hbodyWord
          have callerMapped : ∀ (bodyWordState : State width),
              loopLocalsMappedToRiscV context loopState.locals bodyWordState →
              loopLocalsMappedToRiscV context loopState.locals bodyWordState :=
            fun _ h => h
          cases bodyResult with
          | normal bodyLoopState =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hloop' :
                      some (.normal loopState) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.normal returnedWordState) = some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact callerMapped returnedWordState hlocals
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | returned bodyLoopState values =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState wordValues =>
                  have hloop' :
                      some (.returned loopState values) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.returned returnedWordState wordValues) =
                        some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | raised bodyLoopState exception =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState wordException =>
                  have hloop' :
                      some (.raised loopState exception) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.raised returnedWordState wordException) =
                        some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | broke bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  have hloop' :
                      some (.broke loopState label) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.broke returnedWordState wordLabel) = some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
              | continued bodyWordState wordLabel =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | continued bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState wordLabel =>
                  have hloop' :
                      some (.continued loopState label) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.continued returnedWordState wordLabel) =
                        some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩

/-!
The same call boundary with an exception handler.  The callee still has the
full five-way control relation, while a raised callee result is resumed by
the source and Word handler bodies from related caller states.
-/
theorem loopToWord_call_loop_control_simulation_single_parameter_with_handler
    [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (target parameter argument exception : Nat) (argumentValue : Word width)
    (fuel : Nat) (loopBody handlerBody : LoopProg (Word width))
    (parameterRegister exceptionRegister : Fin 32)
    (loopResult : LoopResult (Word width))
    (wordResult : WordLoopControlResult width)
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hexception :
      RiscV.registerOfNat (wordFindVar context exception) =
        some exceptionRegister)
    (hexception_nonzero : exceptionRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hnoalias :
      ∀ name, name ≠ exception →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ exceptionRegister)
    (hbody : ∀ calleeLoop calleeWord bodyResult bodyWordResult,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          calleeLoop loopBody = some bodyResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          calleeWord (loopToWordProg context loopBody) = some bodyWordResult →
      loopResultMappedToWordLoop context bodyResult bodyWordResult)
    (hhandler : ∀ exceptionValue
        (_handlerLoopState : LoopState (Word width))
        (handlerWordState : State width)
        (handlerResult : LoopResult (Word width))
        (handlerWordResult : WordLoopControlResult width),
      loopLocalsMappedToRiscV context
          (updateLoopLocal loopState.locals exception exceptionValue)
          handlerWordState →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          { loopState with
            locals := updateLoopLocal loopState.locals exception exceptionValue }
          handlerBody = some handlerResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          handlerWordState (loopToWordProg context handlerBody) =
            some handlerWordResult →
      loopResultMappedToWordLoop context handlerResult handlerWordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithPrimitiveCallsAndFfi primitive functions loopHandler
        (fuel + 1) loopState none (some target) [argument]
        (some (exception, handlerBody, .skip, [])) = some loopResult)
    (hword :
      RiscV.evalWordLoopCallWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState none (some target)
        [wordFindVar context argument]
        (some (wordFindVar context exception, loopToWordProg context handlerBody,
          0, 0)) =
          some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  rcases hlocals argument argumentValue hargument with
    ⟨argumentRegister, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, hcallee⟩
  cases hbodyLoop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop, hreadLoop,
        hcalleeBind, hbodyLoop] at hloop
  | some bodyResult =>
      cases hbodyWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            calleeWord (loopToWordProg context loopBody) with
      | none =>
          simp [RiscV.evalWordLoopCallWithHandlersAndFfi, hlookupWord,
            harguments, hwordBind, hbodyWord] at hword
      | some bodyWordResult =>
          have hbodyResult := hbody { loopState with locals := calleeLocals }
            calleeWord bodyResult bodyWordResult hcallee hbodyLoop hbodyWord
          have callerMapped : ∀ (bodyWordState : State width),
              loopLocalsMappedToRiscV context loopState.locals bodyWordState →
              loopLocalsMappedToRiscV context loopState.locals bodyWordState :=
            fun _ h => h
          cases bodyResult with
          | normal bodyLoopState =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hloop' :
                      some (.normal loopState) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.normal returnedWordState) = some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact callerMapped returnedWordState hlocals
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | returned bodyLoopState values =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState wordValues =>
                  have hloop' :
                      some (.returned loopState values) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.returned returnedWordState wordValues) =
                        some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | broke bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  have hloop' :
                      some (.broke loopState label) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.broke returnedWordState wordLabel) = some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | continued bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState wordLabel =>
                  have hloop' :
                      some (.continued loopState label) = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.continued returnedWordState wordLabel) =
                        some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] using hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
          | raised bodyLoopState sourceException =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState targetException =>
                  have hloopHandler :
                      evalLoopProgWithPrimitiveCallsAndFfi primitive functions
                        loopHandler fuel
                        { loopState with
                          locals := updateLoopLocal loopState.locals exception
                            sourceException }
                        handlerBody = some loopResult := by
                    simpa [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hexceptionValue : sourceException = targetException :=
                    hbodyResult.2.symm
                  have hwordHandler :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions
                        wordHandler fuel
                        (RiscV.writeRegister returnedWordState exceptionRegister
                          sourceException)
                        (loopToWordProg context handlerBody) = some wordResult := by
                    simpa [RiscV.evalWordLoopCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord, hexception,
                      hexceptionValue] using hword
                  have hreturnedLocals :
                      loopLocalsMappedToRiscV context loopState.locals
                        returnedWordState := by
                    intro name value hvalue
                    rcases hlocals name value hvalue with
                      ⟨register, hregister, hregisterValue⟩
                    exact ⟨register, hregister, hregisterValue⟩
                  have hhandlerLocals :=
                    loopLocalsMappedToRiscV_update context loopState.locals
                      returnedWordState exception exceptionRegister sourceException
                      hreturnedLocals hexception hexception_nonzero hnoalias
                  exact hhandler sourceException
                    { loopState with
                      locals := updateLoopLocal loopState.locals exception
                        sourceException }
                    (RiscV.writeRegister returnedWordState exceptionRegister
                      sourceException)
                    loopResult wordResult hhandlerLocals hloopHandler hwordHandler
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult

end Flapjack.RiscV
