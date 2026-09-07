import Flapjack.WordSemantics

/-!
Regression coverage for the combined Word call equations.  The callee and
handler are compound programs, which exercises the explicit evaluated-state
boundary instead of relying on a leaf constructor reduction.
-/

namespace Flapjack.RiscV

def wordCallEquationState : State 8 :=
  writeRegister (zeroState 8) 2 9

def wordCallEquationCalleeState : State 8 :=
  writeRegister (clearWordRegisters wordCallEquationState) 2 9

def wordCallEquationHost : FunName → Word 8 → Word 8 → Word 8 → Word 8 →
    State 8 → Option (State 8) :=
  fun _ _ _ _ _ state => some state

def wordCallEquationReturnBody : WordProg (Word 8) :=
  .seq .skip (.return 0 [2])

def wordCallEquationRaiseBody : WordProg (Word 8) :=
  .seq .skip (.raise 2)

def wordCallEquationHandlerBody : WordProg (Word 8) :=
  .seq .skip (.return 0 [3])

example :
    evalWordCallWithHandlersAndFfi
        [(7, [2], wordCallEquationReturnBody)] wordCallEquationHost 5
        wordCallEquationState none (some 7) [2] none =
      some (.returned wordCallEquationState [9]) := by
  apply evalWordCallWithHandlersAndFfi_return_of_eval
    (functions := [(7, [2], wordCallEquationReturnBody)])
    (ffiHandler := wordCallEquationHost) (fuel := 4)
    (state := wordCallEquationState)
    (calleeState := wordCallEquationCalleeState)
    (bodyState := wordCallEquationCalleeState) (target := 7)
    (parameters := [2]) (arguments := [2])
    (body := wordCallEquationReturnBody) (values := [9])
    (returnValues := [9])
  · rfl
  · simp [wordCallEquationState, readWordRegisters, registerOfNat,
      readRegister, writeRegister]
  · simp [wordCallEquationState, wordCallEquationCalleeState,
      bindWordRegisters, clearWordRegisters, registerOfNat, writeRegister]
  · simp [wordCallEquationReturnBody,
      wordCallEquationState, wordCallEquationCalleeState,
      evalWordFunctionWithHandlersAndFfi, evalWordFunction,
      registerOfNat, readRegister, writeRegister]

example :
    evalWordCallWithHandlersAndFfi
        [(7, [2], wordCallEquationRaiseBody)] wordCallEquationHost 5
        wordCallEquationState
        (some ([], ([], []), .skip, 0, 0)) (some 7) [2]
        (some (3, wordCallEquationHandlerBody, 11, 12)) =
      some (.returned (writeRegister wordCallEquationState 3 9) [9]) := by
  apply evalWordCallWithHandlersAndFfi_raise_handler_of_eval
    (functions := [(7, [2], wordCallEquationRaiseBody)])
    (ffiHandler := wordCallEquationHost) (fuel := 4)
    (state := wordCallEquationState)
    (calleeState := wordCallEquationCalleeState)
    (bodyState := wordCallEquationCalleeState) (target := 7)
    (parameters := [2]) (arguments := [2])
    (body := wordCallEquationRaiseBody) (values := [9])
    (exceptionValue := 9) (handlerName := 3) (handlerLabel := 11)
    (entryLabel := 12) (handlerBody := wordCallEquationHandlerBody)
    (handlerRegister := 3)
    (handlerResult := .returned (writeRegister wordCallEquationState 3 9) [9])
  · rfl
  · simp [wordCallEquationState, readWordRegisters, registerOfNat,
      readRegister, writeRegister]
  · simp [wordCallEquationState, wordCallEquationCalleeState,
      bindWordRegisters, clearWordRegisters, registerOfNat, writeRegister]
  · simp [wordCallEquationRaiseBody,
      wordCallEquationState, wordCallEquationCalleeState,
      evalWordFunctionWithHandlersAndFfi, evalWordFunction,
      registerOfNat, readRegister, writeRegister]
  · decide
  · simp [wordCallEquationHandlerBody,
      wordCallEquationState, wordCallEquationCalleeState,
      evalWordFunctionWithHandlersAndFfi, evalWordFunction,
      registerOfNat, readRegister, writeRegister, clearWordRegisters]

end Flapjack.RiscV
