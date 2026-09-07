import Flapjack.Correctness

namespace Flapjack

open RiscV

def handlerCallBody : LoopProg (Word 8) :=
  .seq (.assign 5 (.const 7)) (.raise 5)

def handlerCallLoopState : LoopState (Word 8) :=
  { locals := fun name => if name = 2 then some 9 else none
    globals := fun _ => none
    memory := fun _ => none }

def handlerCallWordState : State 8 :=
  writeRegister (zeroState 8) 2 9

def handlerCallFinalLoop : LoopState (Word 8) :=
  { handlerCallLoopState with
    locals := updateLoopLocal handlerCallLoopState.locals 5 7 }

def handlerCallFinalWord : State 8 :=
  writeRegister handlerCallWordState 5 7

def handlerCallLoopHandler : FunName → Word 8 → Word 8 → Word 8 → Word 8 →
    LoopState (Word 8) → Option (LoopState (Word 8)) :=
  fun _ _ _ _ _ state => some state

def handlerCallWordHandler : FunName → Word 8 → Word 8 → Word 8 → Word 8 →
    State 8 → Option (State 8) :=
  fun _ _ _ _ _ state => some state

theorem handlerCall_mappedLocals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      handlerCallLoopState.locals handlerCallWordState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    refine ⟨2, by decide, ?_⟩
    simpa [handlerCallLoopState, handlerCallWordState, readRegister,
      writeRegister] using hvalue
  · simp [handlerCallLoopState, hname] at hvalue

theorem handlerCall_skip_handler {fuel : Nat}
    (exceptionValue : Word 8) (handlerWord : State 8)
    (handlerLoop : LoopState (Word 8)) (handlerFinalWord : State 8)
    (hlocals : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      (updateLoopLocal handlerCallLoopState.locals 5 exceptionValue) handlerWord)
    (hloop :
      evalLoopProgWithCallsAndFfi
        [(1, [10], handlerCallBody)] handlerCallLoopHandler fuel
        { handlerCallLoopState with
          locals := updateLoopLocal handlerCallLoopState.locals 5 exceptionValue }
        (.skip : LoopProg (Word 8)) = some (.normal handlerLoop))
    (hword :
      evalWordFunctionWithHandlersAndFfi
        [(1, [10], loopToWordProg ({ vars := [] } : WordContext) handlerCallBody)]
        handlerCallWordHandler fuel handlerWord (.skip : WordProg (Word 8)) =
          some (.normal handlerFinalWord)) :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      handlerLoop.locals handlerFinalWord := by
  cases fuel with
  | zero =>
      simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ fuel =>
      have hloop' :
          some (LoopResult.normal
            { handlerCallLoopState with
              locals := updateLoopLocal handlerCallLoopState.locals 5
                exceptionValue }) = some (LoopResult.normal handlerLoop) := by
        simpa [evalLoopProgWithCallsAndFfi, evalLoopProg] using hloop
      have hword' :
          some (RiscV.WordControlResult.normal handlerWord) =
            some (RiscV.WordControlResult.normal handlerFinalWord) := by
        simpa [RiscV.evalWordFunctionWithHandlersAndFfi,
          RiscV.evalWordFunction] using hword
      injection hloop' with hloopResult
      injection hloopResult with hhandlerLoop
      injection hword' with hwordResult
      injection hwordResult with hhandlerWord
      subst handlerLoop
      subst handlerFinalWord
      exact hlocals

example : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    handlerCallFinalLoop.locals handlerCallFinalWord := by
  apply loopToWord_call_handler_simulation_single_parameter
    (context := ({ vars := [] } : WordContext))
    (functions := [(1, [10], handlerCallBody)])
    (wordFunctions := [(1, [10],
      loopToWordProg ({ vars := [] } : WordContext) handlerCallBody)])
    (loopState := handlerCallLoopState)
    (wordState := handlerCallWordState)
    (loopHandler := handlerCallLoopHandler)
    (wordHandler := handlerCallWordHandler)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (exception := 5)
    (argumentValue := 9)
    (fuel := 2)
    (loopBody := handlerCallBody)
    (handlerBody := .skip)
    (parameterRegister := 10)
    (exceptionRegister := 5)
    (finalLoop := handlerCallFinalLoop)
    (finalWord := handlerCallFinalWord)
    (hlookupLoop := by simp [lookupLoopFunction, handlerCallBody])
    (hlookupWord := by simp [RiscV.lookupWordFunction, loopToWordProg,
      handlerCallBody, wordFindVar, lookupNatInfo, wordCompileExp])
    (hparameter := by decide)
    (hparameter_nonzero := by decide)
    (hexception := by decide)
    (hexception_nonzero := by decide)
    (hargument := by simp [handlerCallLoopState])
    (hnoalias := by
      intro name hname register hregister
      have hfive : RiscV.registerOfNat 5 = some (5 : Fin 32) := by
        decide
      intro heq
      have hsame := RiscV.registerOfNat_injective hregister hfive heq
      exact hname hsame)
    (hbody := by
      intro calleeLoop calleeWord loopResult wordResult hzero hloop hword
      change calleeWord.registers 0 = 0 at hzero
      simp [handlerCallBody, loopToWordProg, wordCompileExp,
        wordFindVar, lookupNatInfo, lookupLoopFunction, RiscV.lookupWordFunction,
        evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi, evalLoopProg,
        evalLoopExp, loopReadLocals, loopBindParameters, updateLoopLocal,
        RiscV.evalWordFunctionWithHandlersAndFfi, RiscV.evalWordFunction,
        RiscV.evalWordProg, RiscV.wordExpToInstructions,
        RiscV.wordExpToInstruction, RiscV.wordInstToInstruction,
        RiscV.executeInstructions, RiscV.execute, RiscV.nextPc,
        RiscV.registerOfNat, RiscV.readRegister, RiscV.writeRegister, hzero,
        loopCallBodyResultCompatible] at hloop hword
      cases hloop
      cases hword
      simp [loopCallBodyResultCompatible])
    (hhandler := by
      simpa [loopToWordProg] using
        (handlerCall_skip_handler (fuel := 2)))
    (hlocals := handlerCall_mappedLocals)
  · simp [evalLoopCallWithCallsAndFfi, evalLoopProgWithCallsAndFfi,
      evalLoopProg, evalLoopExp, loopReadLocals, loopBindParameters,
      lookupLoopFunction, handlerCallBody, handlerCallLoopState,
      handlerCallFinalLoop, handlerCallLoopHandler, updateLoopLocal]
  · simp [RiscV.evalWordCallWithHandlersAndFfi, RiscV.lookupWordFunction,
      RiscV.readWordRegisters, RiscV.bindWordRegisters,
      RiscV.clearWordRegisters, handlerCallBody,
      handlerCallWordState, handlerCallFinalWord, loopToWordProg,
      wordCompileExp, wordFindVar, lookupNatInfo,
      RiscV.evalWordFunctionWithHandlersAndFfi, RiscV.evalWordFunction,
      RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.wordInstToInstruction,
      RiscV.executeInstructions, RiscV.execute, RiscV.nextPc,
      RiscV.registerOfNat, RiscV.readRegister, RiscV.writeRegister,
      handlerCallWordHandler]

end Flapjack
