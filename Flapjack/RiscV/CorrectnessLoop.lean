import Flapjack.RiscV.CorrectnessFfi

/-!
Loop-repeat preservation for the fully composed Loop and Word evaluators.
The theorem is kept separate from the operation-specific correctness file so
that loop control can be reused by later handler and allocator proofs.
-/

namespace Flapjack.RiscV

open Flapjack

theorem loopToWord_repeat_loop_control_simulation [NeZero width]
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
    (body : LoopProg (Word width))
    (fuel : Nat)
    (loopResult : LoopResult (Word width))
    (wordResult : WordLoopControlResult width)
    (hbody : ∀ bodyFuel bodyLoop bodyWord bodyResult bodyWordResult,
      loopLocalsMappedToRiscV context bodyLoop.locals bodyWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler bodyFuel
        bodyLoop body = some bodyResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler bodyFuel
        bodyWord (loopToWordProg context body) = some bodyWordResult →
      loopResultMappedToWordLoop context bodyResult bodyWordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopRepeatWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
        loopState body = some loopResult)
    (hword :
      RiscV.evalWordLoopRepeatWithHandlersAndFfi wordFunctions wordHandler fuel
        wordState (loopToWordProg context body) = some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  induction fuel generalizing loopState wordState loopResult wordResult with
  | zero =>
      simp [evalLoopRepeatWithPrimitiveCallsAndFfi,
        RiscV.evalWordLoopRepeatWithHandlersAndFfi] at hloop
  | succ fuel ih =>
      cases hbodyLoop :
          evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
            loopState body with
      | none =>
          simp [evalLoopRepeatWithPrimitiveCallsAndFfi, hbodyLoop] at hloop
      | some bodyResult =>
          cases hbodyWord :
              RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context body) with
          | none =>
              simp [RiscV.evalWordLoopRepeatWithHandlersAndFfi, hbodyWord] at hword
          | some bodyWordResult =>
              have hbodyResult := hbody fuel loopState wordState
                bodyResult bodyWordResult hlocals hbodyLoop hbodyWord
              cases bodyResult with
              | normal middleLoop =>
                  cases bodyWordResult with
                  | normal middleWord =>
                      apply ih middleLoop middleWord loopResult wordResult hbodyResult
                      · simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                          hbodyLoop] using hloop
                      · simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                          hbodyWord] using hword
                  | returned middleWord values =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | raised middleWord exception =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | broke middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | continued middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
              | returned middleLoop values =>
                  cases bodyWordResult with
                  | normal middleWord =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | returned middleWord wordValues =>
                      have hloop' :
                          some (.returned middleLoop values) = some loopResult := by
                        simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                          hbodyLoop] using hloop
                      have hword' :
                          some (.returned middleWord wordValues) =
                            some wordResult := by
                        simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                          hbodyWord] using hword
                      cases hloop'
                      cases hword'
                      exact ⟨hbodyResult.1, hbodyResult.2⟩
                  | raised middleWord exception =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | broke middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | continued middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
              | raised middleLoop exception =>
                  cases bodyWordResult with
                  | normal middleWord =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | returned middleWord values =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | raised middleWord wordException =>
                      have hloop' :
                          some (.raised middleLoop exception) = some loopResult := by
                        simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                          hbodyLoop] using hloop
                      have hword' :
                          some (.raised middleWord wordException) =
                            some wordResult := by
                        simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                          hbodyWord] using hword
                      cases hloop'
                      cases hword'
                      exact ⟨hbodyResult.1, hbodyResult.2⟩
                  | broke middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | continued middleWord label =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
              | broke middleLoop label =>
                  cases bodyWordResult with
                  | normal middleWord =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | returned middleWord values =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | raised middleWord exception =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | continued middleWord wordLabel =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | broke middleWord wordLabel =>
                      have hlabel : label = wordLabel := hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordZero : wordLabel = 0 := hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        have hloop' :
                            some (.normal middleLoop) = some loopResult := by
                          simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                            hbodyLoop] using hloop
                        have hword' :
                            some (.normal middleWord) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                            hbodyWord] using hword
                        cases hloop'
                        cases hword'
                        exact hlocals'
                      · have hwordNonzero : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.broke middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                            hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.broke middleWord wordLabel) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                            hbodyWord, hwordNonzero] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩
              | continued middleLoop label =>
                  cases bodyWordResult with
                  | normal middleWord =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | returned middleWord values =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | raised middleWord exception =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | broke middleWord wordLabel =>
                      exact False.elim (by
                        simp [loopResultMappedToWordLoop] at hbodyResult)
                  | continued middleWord wordLabel =>
                      have hlabel : label = wordLabel := hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordZero : wordLabel = 0 := hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        apply ih middleLoop middleWord loopResult wordResult
                          hlocals'
                        · simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                            hbodyLoop] using hloop
                        · simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                            hbodyWord] using hword
                      · have hwordNonzero : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.continued middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeatWithPrimitiveCallsAndFfi,
                            hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.continued middleWord wordLabel) =
                              some wordResult := by
                          simpa [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
                            hbodyWord, hwordNonzero] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩

end Flapjack.RiscV
