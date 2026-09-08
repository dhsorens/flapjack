import Flapjack.Correctness

/-!
# Loop-to-Word call-entry contracts

The Loop evaluator reads a list of local names before entering a callee.  The
Word evaluator performs the same operation after mapping those names to
registers.  This file exposes that list-level agreement independently of any
particular callee body, so later call proofs can reuse it without duplicating
the recursive option reasoning.
-/

namespace Flapjack

theorem loopReadLocals_wordMapVars_agreement [NeZero width]
    (context : WordContext)
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (names : List Nat) (values : List (RiscV.Word width))
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hread : loopReadLocals loopState.locals names = some values) :
    (wordMapVars context names).mapM (fun name => do
      let register ← RiscV.registerOfNat name
      pure (RiscV.readRegister wordState register)) = some values := by
  induction names generalizing values with
  | nil =>
      have hread' : values = [] := by
        simpa [loopReadLocals] using hread
      subst values
      simp [wordMapVars]
  | cons name names ih =>
      cases hlocal : loopState.locals name with
      | none =>
          simp [loopReadLocals, hlocal] at hread
      | some value =>
          cases hrest : loopReadLocals loopState.locals names with
          | none =>
              simp [loopReadLocals, hlocal, hrest] at hread
          | some rest =>
              have hread' : values = value :: rest := by
                simpa [loopReadLocals, hlocal, hrest] using hread.symm
              subst values
              rcases hlocals name value hlocal with
                ⟨register, hregister, hvalue⟩
              have htail := ih rest hrest
              have htail' :
                  (wordMapVars context names).mapM (fun name =>
                    (RiscV.registerOfNat name).bind (fun register =>
                      some (RiscV.readRegister wordState register))) = some rest := by
                simpa using htail
              simp [wordMapVars, hregister, hvalue]
              rw [htail']
              simp

/-!
The call evaluator has the same correspondence once its two binding steps are
exposed.  Keeping those bindings as hypotheses makes this theorem useful for
both the current simple allocator and the later spill-aware allocator: the
allocator-specific proof only has to establish the two state witnesses.
-/
theorem loopToWord_call_tail_simulation_general [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (target : Nat) (parameters arguments : List Nat)
    (argumentValues : List (RiscV.Word width))
    (loopBody : LoopProg (RiscV.Word width)) (fuel : Nat)
    (calleeLocals : Nat → Option (RiscV.Word width))
    (calleeWord : RiscV.State width)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (loopResultValues wordResultValues : List (RiscV.Word width))
    (hlookupLoop :
      lookupLoopFunction target functions = some (parameters, loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some (wordMapVars context parameters, loopToWordProg context loopBody))
    (hread : loopReadLocals loopState.locals arguments = some argumentValues)
    (hloopBind :
      loopBindParameters parameters argumentValues (fun _ => none) =
        some calleeLocals)
    (hwordBind :
      RiscV.bindWordRegisters wordState (wordMapVars context parameters)
        argumentValues = some calleeWord)
    (hcallee :
      loopLocalsMappedToRiscV context calleeLocals calleeWord)
    (hbody : ∀ calleeLoop calleeWord' bodyLoop bodyWord loopValues wordValues,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord' →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel calleeLoop loopBody =
        some (.returned bodyLoop loopValues) →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        calleeWord' (loopToWordProg context loopBody) =
        some (.returned bodyWord wordValues) →
      wordValues = loopValues)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        none (some target) arguments none =
        some (.returned finalLoop loopResultValues))
    (hword :
      RiscV.evalWordCallWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState none (some target) (wordMapVars context arguments) none =
        some (.returned finalWord wordResultValues)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord ∧
      wordResultValues = loopResultValues := by
  have harguments' := loopReadLocals_wordMapVars_agreement context loopState
    wordState arguments argumentValues hlocals hread
  have harguments :
      RiscV.readWordRegisters wordState (wordMapVars context arguments) =
        some argumentValues := by
    have hreader : ∀ names : List Nat,
        RiscV.readWordRegisters wordState names =
          names.mapM (fun name => do
            let register ← RiscV.registerOfNat name
            pure (RiscV.readRegister wordState register)) := by
      intro names
      induction names with
      | nil => simp [RiscV.readWordRegisters]
      | cons name names ih =>
          simp [RiscV.readWordRegisters, ih, Option.bind_assoc]
    rw [hreader]
    exact harguments'
  cases hbodyLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
        hbodyLoop] at hloop
  | some bodyLoopResult =>
      cases bodyLoopResult with
      | normal bodyLoopState =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | broke bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | continued bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | raised bodyLoopState exception =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | returned bodyLoopState bodyValues =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                    harguments, hwordBind, hbodyWord] at hword
              | raised bodyWordState exception =>
                  simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                    harguments, hwordBind, hbodyWord] at hword
              | returned bodyWordState bodyValues' =>
                  have hvalues := hbody
                    { loopState with locals := calleeLocals } calleeWord
                    bodyLoopState bodyWordState bodyValues bodyValues'
                    hcallee hbodyLoop hbodyWord
                  have hloop' :
                      some (LoopResult.returned loopState bodyValues) =
                        some (LoopResult.returned finalLoop loopResultValues) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hread, hloopBind, hbodyLoop] using hloop
                  have hword' :
                      some (RiscV.WordControlResult.returned
                        { wordState with
                          memory := bodyWordState.memory
                          privilege := bodyWordState.privilege
                          mode := bodyWordState.mode }
                        bodyValues') =
                        some (RiscV.WordControlResult.returned finalWord
                          wordResultValues) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord] using hword
                  injection hloop' with hloopReturned
                  injection hloopReturned with hfinalLoop hloopValues
                  injection hword' with hwordReturned
                  injection hwordReturned with hfinalWord hwordValues
                  subst finalLoop
                  subst finalWord
                  subst loopResultValues
                  subst wordResultValues
                  exact ⟨hlocals, hvalues⟩

/-!
The exceptional call boundary uses the same arbitrary-list entry contract.
The exception register and the handler body remain explicit obligations: this
keeps the theorem independent of a particular allocator or handler lowering.
-/
theorem loopToWord_call_handler_simulation_general [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (target : Nat) (parameters arguments : List Nat) (exception : Nat)
    (argumentValues : List (RiscV.Word width))
    (fuel : Nat) (loopBody handlerBody : LoopProg (RiscV.Word width))
    (calleeLocals : Nat → Option (RiscV.Word width))
    (calleeWord : RiscV.State width)
    (exceptionRegister : Fin 32)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hlookupLoop :
      lookupLoopFunction target functions = some (parameters, loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some (wordMapVars context parameters, loopToWordProg context loopBody))
    (hread : loopReadLocals loopState.locals arguments = some argumentValues)
    (hloopBind :
      loopBindParameters parameters argumentValues (fun _ => none) =
        some calleeLocals)
    (hwordBind :
      RiscV.bindWordRegisters wordState (wordMapVars context parameters)
        argumentValues = some calleeWord)
    (hcalleeZero : RiscV.readRegister calleeWord 0 = 0)
    (hexception :
      RiscV.registerOfNat (wordFindVar context exception) =
        some exceptionRegister)
    (hexception_nonzero : exceptionRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ exception →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ exceptionRegister)
    (hbody : ∀ calleeLoop calleeWord' loopResult wordResult,
      RiscV.readRegister calleeWord' 0 = 0 →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel calleeLoop loopBody =
        some loopResult →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        calleeWord' (loopToWordProg context loopBody) = some wordResult →
      loopCallBodyResultCompatible loopResult wordResult)
    (hhandler : ∀ exceptionValue handlerWord handlerLoop handlerFinalWord,
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals exception exceptionValue) handlerWord →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
          { loopState with
            locals := updateLoopLocal loopState.locals exception exceptionValue }
          handlerBody = some (.normal handlerLoop) →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
          handlerWord (loopToWordProg context handlerBody) =
            some (.normal handlerFinalWord) →
      loopLocalsMappedToRiscV context handlerLoop.locals handlerFinalWord)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        none (some target) arguments
        (some (exception, handlerBody, .skip, [])) =
          some (.normal finalLoop))
    (hword :
      RiscV.evalWordCallWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState none (some target) (wordMapVars context arguments)
        (some (wordFindVar context exception, loopToWordProg context handlerBody,
          0, 0)) =
          some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  have harguments' := loopReadLocals_wordMapVars_agreement context loopState
    wordState arguments argumentValues hlocals hread
  have harguments :
      RiscV.readWordRegisters wordState (wordMapVars context arguments) =
        some argumentValues := by
    have hreader : ∀ names : List Nat,
        RiscV.readWordRegisters wordState names =
          names.mapM (fun name => do
            let register ← RiscV.registerOfNat name
            pure (RiscV.readRegister wordState register)) := by
      intro names
      induction names with
      | nil => simp [RiscV.readWordRegisters]
      | cons name names ih =>
          simp [RiscV.readWordRegisters, ih, Option.bind_assoc]
    rw [hreader]
    exact harguments'
  cases hbodyLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
        hbodyLoop] at hloop
  | some bodyLoopResult =>
      cases bodyLoopResult with
      | normal bodyLoopState =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState) (.normal bodyWordState)
                    hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
                  have hloop' :
                      some (LoopResult.normal loopState) =
                        some (LoopResult.normal finalLoop) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hread, hloopBind, hbodyLoop] using hloop
                  have hword' :
                      some (RiscV.WordControlResult.normal
                        { wordState with
                          memory := bodyWordState.memory
                          privilege := bodyWordState.privilege
                          mode := bodyWordState.mode }) =
                        some (RiscV.WordControlResult.normal finalWord) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord] using hword
                  injection hloop' with hloopResult
                  injection hloopResult with hfinalLoop
                  injection hword' with hwordResult
                  injection hwordResult with hfinalWord
                  subst finalLoop
                  subst finalWord
                  intro name value hvalue
                  rcases hlocals name value hvalue with
                    ⟨register, hregister, hregisterValue⟩
                  exact ⟨register, hregister, hregisterValue⟩
              | returned bodyWordState values =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.returned bodyWordState values) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | raised bodyWordState value =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.raised bodyWordState value) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
      | broke bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | continued bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | returned bodyLoopState values =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hread, hloopBind,
            hbodyLoop] at hloop
      | raised bodyLoopState sourceException =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.normal bodyWordState) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | returned bodyWordState values =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.returned bodyWordState values) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | raised bodyWordState targetException =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.raised bodyWordState targetException) hcalleeZero hbodyLoop hbodyWord
                  have hexceptionValue : sourceException = targetException := by
                    simpa [loopCallBodyResultCompatible] using hcompatible
                  have hloopHandler :
                      evalLoopProgWithCallsAndFfi functions loopHandler fuel
                        { loopState with
                          locals := updateLoopLocal loopState.locals exception
                            sourceException }
                        handlerBody = some (.normal finalLoop) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hread, hloopBind, hbodyLoop] using hloop
                  let returnedWordState : RiscV.State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hwordHandler :
                      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions
                        wordHandler fuel
                        (RiscV.writeRegister returnedWordState
                          exceptionRegister sourceException)
                        (loopToWordProg context handlerBody) =
                          some (.normal finalWord) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
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
                    (RiscV.writeRegister returnedWordState exceptionRegister
                      sourceException) finalLoop finalWord hhandlerLocals hloopHandler
                    hwordHandler

end Flapjack
