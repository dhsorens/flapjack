import Flapjack.StackAlloc.Machine

/-!
Regression coverage for the abstract StackLang arbitrary-callee call
equations.  Compound callees make the evaluated state explicit before the
handler or return continuation is entered.
-/

namespace Flapjack.RiscV

def generalStackCallState : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def generalStackCallHost : StackMachineFfiHandler 64 :=
  fun _ _ _ _ _ state => some state

def generalStackRaiseCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 7 5) (.raise 7))
  | _ => none

def generalStackReturnCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 6 17) (.return 6))
  | _ => none

example :
    evalStackProgFuelWithCodeAndFfi generalStackCallHost 12
      generalStackRaiseCode generalStackCallState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0)
        (some ((.const 3 9 : StackProg Nat), 3, 0))) =
      evalStackProgFuelWithCodeAndFfi generalStackCallHost 11
        generalStackRaiseCode
        (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister generalStackCallState 7
            (BitVec.ofNat 64 5))
          3 (BitVec.ofNat 64 5))
        (.const 3 9) := by
  apply evalStackProgFuelWithCodeAndFfi_call_raise_handler_of_eval
  · rfl
  · rfl

example :
    evalStackProgFuelWithCodeAndFfi generalStackCallHost 12
      generalStackReturnCode generalStackCallState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0) none) =
      evalStackProgFuelWithCodeAndFfi generalStackCallHost 11
        generalStackReturnCode
        (wordStackMachineWriteRegister generalStackCallState 6
          (BitVec.ofNat 64 17))
        (.skip) := by
  apply evalStackProgFuelWithCodeAndFfi_call_return_handler_of_eval
  · rfl
  · rfl

end Flapjack.RiscV
