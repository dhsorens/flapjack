import Flapjack.WordSemantics

/-!
Regression coverage for handler-aware Word loop execution.  These examples
exercise the two effects that were previously unavailable inside a Word loop:
an FFI action and a returning call followed by loop control.
-/

namespace Flapjack

def wordLoopHandlerTestState : RiscV.State 64 := RiscV.zeroState 64

def wordLoopHandlerTestFfi :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      RiscV.State 64 → Option (RiscV.State 64) :=
  fun _ _ _ _ _ state => some (RiscV.writeRegister state 7 (BitVec.ofNat 64 9))

example :
    RiscV.evalWordLoopProgWithHandlersAndFfi [] wordLoopHandlerTestFfi 4
        wordLoopHandlerTestState
        (.loop []
          (.seq
            (.ffi "bump" 2 3 4 5 ([], []))
            (.break 0)) []) =
      some (RiscV.WordLoopControlResult.normal
        (RiscV.writeRegister wordLoopHandlerTestState 7 (BitVec.ofNat 64 9))) := by
  have h2 : RiscV.registerOfNat 2 = some (2 : Fin 32) := by decide
  have h3 : RiscV.registerOfNat 3 = some (3 : Fin 32) := by decide
  have h4 : RiscV.registerOfNat 4 = some (4 : Fin 32) := by decide
  have h5 : RiscV.registerOfNat 5 = some (5 : Fin 32) := by decide
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopRepeatWithHandlersAndFfi, wordLoopHandlerTestFfi,
    h2, h3, h4, h5]

def wordLoopCallBody : WordProg (RiscV.Word 64) := .return 0 []

example :
    RiscV.evalWordLoopCallWithHandlersAndFfi
        [(1, [], wordLoopCallBody)] (fun _ _ _ _ _ state => some state) 3
        wordLoopHandlerTestState
          (some ([], ([], []), .skip, 0, 0)) (some 1) [] none =
      some (RiscV.WordLoopControlResult.normal wordLoopHandlerTestState) := by
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopCallWithHandlersAndFfi, RiscV.lookupWordFunction,
    RiscV.readWordRegisters, RiscV.bindWordRegisters,
    RiscV.assignWordRegisters, RiscV.clearWordRegisters, wordLoopCallBody]

example :
    RiscV.evalWordLoopProgWithHandlersAndFfi
        [(1, [], wordLoopCallBody)] (fun _ _ _ _ _ state => some state) 8
        wordLoopHandlerTestState
        (.loop []
          (.seq
            (.call (some ([], ([], []), .skip, 0, 0)) (some 1) [] none)
            (.break 0)) []) =
      some (RiscV.WordLoopControlResult.normal wordLoopHandlerTestState) := by
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopRepeatWithHandlersAndFfi,
    RiscV.evalWordLoopCallWithHandlersAndFfi,
    RiscV.lookupWordFunction, RiscV.readWordRegisters,
    RiscV.bindWordRegisters, RiscV.assignWordRegisters,
    RiscV.clearWordRegisters,
    wordLoopCallBody]

end Flapjack
