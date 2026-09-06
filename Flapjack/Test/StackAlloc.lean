import Flapjack.RiscV.Lab

namespace Flapjack

open RiscV

def stackAllocTestConfig : StackAllocConfig :=
  { gcStubLocation := 77, returnLabel := 12, firstFreshLabel := 20 }

def stackAllocRemoveConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example :
    stackAllocCompFuel 1 stackAllocTestConfig 20 (.alloc 3 : StackProg Nat) =
      (.call (some (.skip, 0, 12, 20)) (.label 77) none, 21) := by
  rfl

example :
    stackAllocCompFuel 1 stackAllocTestConfig 20
        (.storeConsts 1 2 (some 88) : StackProg Nat) =
      (.call (some (.skip, 0, 12, 20)) (.label 88) none, 21) := by
  rfl

example :
    (stackAllocWithNext stackAllocTestConfig
      (.seq (.alloc 1) (.alloc 2) : StackProg Nat)).2 = 22 := by
  simp [stackAllocTestConfig, stackAllocWithNext, stackAllocCompFuel,
    stackAllocProgDepth]

example :
    stackAllocStubs stackAllocTestConfig = [(77, (.return 0 : StackProg Nat))] := by
  rfl

example :
    (compileStackProgramNatListWithStackAllocToRiscV (width := 64)
      { services := [] } stackAllocRemoveConfig stackAllocTestConfig 0 0
      [(1, (.alloc 1 : StackProg Nat))]).isSome := by
  native_decide

end Flapjack
