import Flapjack.Test.StackFrameMachine

/-!
Regression coverage for the generalized FrameMachine call equations.  The
callees are compound programs rather than a single `.raise` or `.return`, so
the tests exercise the evaluated callee-state boundary used by handler-aware
Word-to-Stack simulations.
-/

namespace Flapjack.RiscV

def generalRaiseCallCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 7 5) (.raise 7))
  | _ => none

def generalReturnCallCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 6 17) (.return 6))
  | _ => none

example :
    evalStackFrameFuelWithCodeAndFfi identityFrameFfi 12
      generalRaiseCallCode frameMachineState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0)
        (some ((.const 3 9 : StackProg Nat), 3, 0))) =
      evalStackFrameFuelWithCodeAndFfi identityFrameFfi 11
        generalRaiseCallCode
        (stackFrameWriteRegister
          (stackFrameWriteRegister frameMachineState 7 (BitVec.ofNat 64 5))
          3 (BitVec.ofNat 64 5))
        (.const 3 9) := by
  apply evalStackFrameFuelWithCodeAndFfi_call_raise_handler_of_eval
  · rfl
  · rfl

example :
    evalStackFrameFuelWithCodeAndFfi identityFrameFfi 12
      generalReturnCallCode frameMachineState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0) none) =
      evalStackFrameFuelWithCodeAndFfi identityFrameFfi 11
        generalReturnCallCode
        (stackFrameWriteRegister frameMachineState 6 (BitVec.ofNat 64 17))
        (.skip) := by
  apply evalStackFrameFuelWithCodeAndFfi_call_return_handler_of_eval
  · rfl
  · rfl

end Flapjack.RiscV
