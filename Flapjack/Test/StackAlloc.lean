import Flapjack.RiscV.Lab
import Flapjack.StackAlloc.Runtime
import Flapjack.StackAlloc.Machine
import Flapjack.StackAlloc.Correctness

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
  simp [stackAllocTestConfig, stackAllocWithNext, stackAllocComp,
    stackAllocNextLab]

example :
    stackAllocComp stackAllocTestConfig 20
        (.call none (.label 88)
          (some ((.alloc 1 : StackProg Nat), 4, 5))) =
      (.call none (.label 88) none, 20) := by
  simp [stackAllocComp]

example :
    stackAllocCompile stackAllocTestConfig
        [(1, (.alloc 3 : StackProg Nat))] =
      [(77, (.return 0 : StackProg Nat)),
       (1, (.call (some (.skip, 0, 12, 2)) (.label 77) none))] := by
  simp [stackAllocCompile, stackAllocStubs, stackAllocProgram,
    stackAllocComp, stackAllocRuntimeCall, stackAllocNextLab,
    stackAllocTestConfig, stackAllocStub]

example :
    stackAllocStubs stackAllocTestConfig = [(77, (.return 0 : StackProg Nat))] := by
  rfl

example :
    (compileStackProgramNatListWithStackAllocToRiscV (width := 64)
      { services := [] } stackAllocRemoveConfig stackAllocTestConfig 0 0
      [(1, (.alloc 1 : StackProg Nat))]).isSome := by
  native_decide

example :
    (compileStackProgramNatListWithHaltToRiscV (width := 64)
      { services := [] } stackAllocRemoveConfig 0 0
      [(1, (.halt 1 : StackProg Nat))]).isSome := by
  native_decide

def stackGcTestConfig : StackGcConfig :=
  { shiftLength := 11
    smallShiftLength := 9
    lenSize := 32
    wordShift := 3
    wordBits := 64
    bytesInWord := 8
    immediateScratch := 31 }

example :
    stackGcSimpleStub stackGcTestConfig =
      stackSeq [stackGcSimpleCode stackGcTestConfig, .return 0] := by
  rfl

example :
    (stackAllocCompileWithSimpleGc stackAllocTestConfig stackGcTestConfig
      [(1, (.alloc 1 : StackProg Nat))]).head? =
        some (77, stackGcSimpleStub stackGcTestConfig) := by
  simp [stackAllocCompileWithSimpleGc, stackAllocSimpleStubs,
    stackAllocTestConfig]

example :
    (compileStackProgramNatListWithSimpleGcToRiscV (width := 64)
      { services := [] } stackAllocRemoveConfig stackAllocTestConfig
      stackGcTestConfig 0 0 [(1, (.alloc 1 : StackProg Nat))]).isSome := by
  native_decide

def zeroStackMachineState : RiscV.WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    (evalStackProgFuel 4 zeroStackMachineState
      (.seq (.const 1 7) (.set .allocSize 1) : StackProg Nat)).isSome := by
  native_decide

example :
    (evalStackProgFuel 3000 zeroStackMachineState
      (stackGcSimpleCode stackGcTestConfig)).isSome := by
  native_decide

example :
    stackGcSimpleZeroObservation
      (evalStackProgFuel 3000 zeroStackMachineState
        (stackGcSimpleCode stackGcTestConfig)) = true := by
  native_decide

def forwardedPointerState : RiscV.WordStackMachineState 64 :=
  { registers := fun register => if register = 5 then 3 else 0
    stack := fun _ => 0
    stores := fun store => if store = .currHeap then 0 else 0
    memory := fun address => if address = 0 then 0 else 0
    sharedMemory := fun _ => 0 }

def movedForwardingPointerState : RiscV.WordStackMachineState 64 :=
  { registers := fun register => if register = 5 then 3 else 0
    stack := fun _ => 0
    stores := fun store => if store = .currHeap then 0 else 0
    memory := fun address => if address = 0 then 4 else 0
    sharedMemory := fun _ => 0 }

def oneWordObjectState : RiscV.WordStackMachineState 64 :=
  { registers := fun register =>
      if register = 3 then 100 else
        if register = 4 then 1 else if register = 5 then 3 else 0
    stack := fun _ => 0
    stores := fun store => if store = .currHeap then 0 else 0
    memory := fun address => if address = 0 then 3 else 0
    sharedMemory := fun _ => 0 }

example :
    stackMachineNormalRegisterEquals
      (evalStackProgFuel 500 forwardedPointerState
        (stackGcMoveCode stackGcTestConfig)) 5 3 = true := by
  native_decide

example :
    stackMachineNormalRegisterEquals
      (evalStackProgFuel 500 movedForwardingPointerState
        (stackGcMoveCode stackGcTestConfig)) 5 2051 = true := by
  native_decide

example :
    stackMachineNormalRegisterEquals
      (evalStackProgFuel 1000 oneWordObjectState
        (stackGcMoveCode stackGcTestConfig)) 5 2051 = true := by
  native_decide

example :
    stackMachineNormalMemoryEquals
      (evalStackProgFuel 1000 oneWordObjectState
        (stackGcMoveCode stackGcTestConfig)) 100 3 = true := by
  native_decide

example :
    (evalStackLabelCallFuel 3000
      (fun target => if target = 77 then
        some (stackGcSimpleStub stackGcTestConfig) else none)
      zeroStackMachineState 77 (.skip : StackProg Nat)).isSome := by
  native_decide

example :
    (evalStackSectionsFuel 6000
      (stackAllocCompileWithSimpleGc stackAllocTestConfig stackGcTestConfig
        [(1, (.alloc 1 : StackProg Nat))])
      1 zeroStackMachineState).isSome := by
  native_decide

example :
    stackGcSimpleZeroObservation
      (evalStackSectionsFuel 6000
        (stackAllocCompileWithSimpleGc stackAllocTestConfig stackGcTestConfig
          [(1, (.alloc 1 : StackProg Nat))])
        1 zeroStackMachineState) = true := by
  native_decide

def oneWordObjectNatMemory : Nat → Nat :=
  fun address => if address = 0 then 3 else 0

def allAddressesInDomain : Nat → Bool :=
  fun _ => true

example :
    (stackGcNatMove stackGcTestConfig 3 1 100 0
      oneWordObjectNatMemory allAddressesInDomain).value = 2051 := by
  native_decide

example :
    (stackGcNatMove stackGcTestConfig 3 1 100 0
      oneWordObjectNatMemory allAddressesInDomain).memory 100 = 3 := by
  native_decide

example :
    stackMachineNormalRegisterNat
      (evalStackProgFuel 1000 oneWordObjectState
        (stackGcMoveCode stackGcTestConfig)) 5 =
      some (stackGcNatMove stackGcTestConfig 3 1 100 0
        oneWordObjectNatMemory allAddressesInDomain).value := by
  native_decide

example :
    (stackGcNatMoveRoots stackGcTestConfig [3, 2] 1 100 0
      oneWordObjectNatMemory allAddressesInDomain).values = [2051, 2] := by
  native_decide

example :
    (stackGcNatMoveList stackGcTestConfig 1 0 1 100 0
      oneWordObjectNatMemory allAddressesInDomain).nextScan = 8 := by
  native_decide

example :
    (stackGcNatMoveList stackGcTestConfig 1 0 1 100 0
      oneWordObjectNatMemory allAddressesInDomain).memory 100 = 3 := by
  native_decide

example :
    (stackGcNatFull stackGcTestConfig [3] 100 0
      oneWordObjectNatMemory allAddressesInDomain 10).values = [3] ∧
      (stackGcNatFull stackGcTestConfig [3] 100 0
        oneWordObjectNatMemory allAddressesInDomain 10).nextAddress = 108 ∧
      (stackGcNatFull stackGcTestConfig [3] 100 0
        oneWordObjectNatMemory allAddressesInDomain 10).condition = true := by
  native_decide

end Flapjack
