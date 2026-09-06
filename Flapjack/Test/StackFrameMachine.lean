import Flapjack.StackAlloc.FrameMachine
import Flapjack.StackAlloc.Runtime

namespace Flapjack.RiscV

def frameMachineState : StackFrameMachineState 64 :=
  { machine :=
      { registers := fun _ => 0
        stack := fun slot => if slot = 13 then 41 else 0
        stores := fun _ => 0
        memory := fun _ => 0
        sharedMemory := fun _ => 0 }
    stackSpace := 8
    stackLimit := 16
    bitmaps := [13, 29]
    bytesInWord := 8
    memoryDomain := fun _ => true
    sharedMemoryDomain := fun _ => true }

example :
    stackFrameNormalStackSpace
      (evalStackFrameFuel 2 frameMachineState (.stackAlloc 3)) = some 5 := by
  rfl

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameMachineState (.stackLoad 4 5)) 4 = some 41 := by
  rfl

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameMachineState (.bitmapLoad 4 1)) 4 = some 13 := by
  native_decide

example :
    (evalStackFrameFuel 4 frameMachineState
      (.seq (.const 3 48) (.stackStore 3 2))).isSome := by
  native_decide

example :
    evalStackFrameFuel 2 frameMachineState (.stackLoad 4 5) =
      some (.normal (stackFrameWriteRegister frameMachineState 4
        (frameMachineState.machine.stack (frameMachineState.stackSpace + 5)))) := by
  exact evalStackFrameFuel_stackLoad 1 frameMachineState 4 5 (by decide)

example :
    evalStackFrameFuel 2 frameMachineState
        (.inst (.mem .load 4 0)) =
      some (.normal (stackFrameWriteRegister frameMachineState 4
        (frameMachineState.machine.memory (frameMachineState.machine.registers 0)))) := by
  exact evalStackFrameFuel_memLoad 1 frameMachineState 4 0 (by decide)

def frameNoMemoryState : StackFrameMachineState 64 :=
  { frameMachineState with memoryDomain := fun _ => false }

example :
    (evalStackFrameFuel 2 frameNoMemoryState
      (.inst (.mem .load 4 0))).isSome = false := by
  native_decide

def frameNoSharedMemoryState : StackFrameMachineState 64 :=
  { frameMachineState with sharedMemoryDomain := fun _ => false }

example :
    (evalStackFrameFuel 2 frameNoSharedMemoryState
      (.shMem .load 4 0)).isSome = false := by
  native_decide

def frameByteState : StackFrameMachineState 64 :=
  let newMemory : Word 64 → Word 64 := fun address =>
    if address = 0 then BitVec.ofNat 64 0x04030201 else 0
  let machine := { frameMachineState.machine with memory := newMemory }
  { frameMachineState with machine := machine }

def frameUnalignedState : StackFrameMachineState 64 :=
  let registers : Nat → Word 64 := fun register =>
    if register = 1 then BitVec.ofNat 64 2
    else frameByteState.machine.registers register
  let machine := { frameByteState.machine with registers := registers }
  { frameByteState with machine := machine }

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameByteState
        (.inst (.mem .load8 4 0))) 4 = some 1 := by
  native_decide

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameByteState
        (.inst (.mem .load16 4 0))) 4 = some 513 := by
  native_decide

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameByteState
        (.inst (.mem .load32 4 0))) 4 = some 0x04030201 := by
  native_decide

def frameByteStoreState : StackFrameMachineState 64 :=
  let registers : Nat → Word 64 := fun register =>
    if register = 3 then BitVec.ofNat 64 0xaa else 0
  let machine := { frameByteState.machine with registers := registers }
  { frameByteState with machine := machine }

example :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel 2 frameByteStoreState
        (.inst (.mem .store8 3 0))) 0 = some 0x040302aa := by
  native_decide

example :
    (evalStackFrameFuel 2 frameUnalignedState
      (.inst (.mem .load32 4 1))).isSome = false := by
  native_decide

example :
    (evalStackFrameFuel 2 frameMachineState (.stackLoadAny 4 3)).isSome := by
  native_decide

example :
    (evalStackFrameFuel 2 frameMachineState
      (.seq (.const 0 1) (.stackLoadAny 4 0))).isSome = false := by
  native_decide

example :
    evalStackFrameFuel 2 frameMachineState (.stackGetSize 4) =
      some (.normal (stackFrameWriteRegister frameMachineState 4
        (BitVec.ofNat 64 8))) := by
  exact evalStackFrameFuel_stackGetSize 1 frameMachineState 4

def frameCollectorState : StackFrameMachineState 64 :=
  { machine :=
      { registers := fun _ => 0
        stack := fun _ => 0
        stores := fun _ => 0
        memory := fun _ => 0
        sharedMemory := fun _ => 0 }
    stackSpace := 8
    stackLimit := 16
    bitmaps := [0]
    bytesInWord := 8
    memoryDomain := fun _ => true
    sharedMemoryDomain := fun _ => true }

def frameCollectorConfig : StackGcConfig :=
  { shiftLength := 11
    smallShiftLength := 9
    lenSize := 32
    wordShift := 3
    wordBits := 64
    bytesInWord := 8
    immediateScratch := 31 }

def frameMoveListOneState : StackFrameMachineState 64 :=
  { frameCollectorState with
      machine := { frameCollectorState.machine with
        registers := fun register => if register = 7 then 1 else 0 } }

def frameMoveListCopyState : StackFrameMachineState 64 :=
  { frameCollectorState with
      machine := { frameCollectorState.machine with
        registers := fun register =>
          if register = 7 then 1 else if register = 8 then 100 else 0
        memory := fun address =>
          if address = 0 then BitVec.ofNat 64 0x200000003
          else if address = 100 then BitVec.ofNat 64 3 else 0 } }

def frameForwardingState : StackFrameMachineState 64 :=
  { machine :=
      { registers := fun register => if register = 5 then 3 else 0
        stack := fun _ => 0
        stores := fun _ => 0
        memory := fun address => if address = 0 then 4 else 0
        sharedMemory := fun _ => 0 }
    stackSpace := 8
    stackLimit := 16
    bitmaps := [0]
    bytesInWord := 8
    memoryDomain := fun _ => true
    sharedMemoryDomain := fun _ => true }

def frameCopyState : StackFrameMachineState 64 :=
  { machine :=
      { registers := fun register =>
          if register = 3 then 100 else
            if register = 4 then 1 else if register = 5 then 3 else 0
        stack := fun _ => 0
        stores := fun _ => 0
        memory := fun address => if address = 0 then 3 else 0
        sharedMemory := fun _ => 0 }
    stackSpace := 8
    stackLimit := 16
    bitmaps := [0]
    bytesInWord := 8
    memoryDomain := fun _ => true
    sharedMemoryDomain := fun _ => true }

def frameMemcpyOneState : StackFrameMachineState 64 :=
  { frameCopyState with
      machine := { frameCopyState.machine with
        registers := fun register =>
          if register = 0 then 1 else frameCopyState.machine.registers register } }

def frameMemcpyTwoState : StackFrameMachineState 64 :=
  { frameCopyState with
      machine := { frameCopyState.machine with
        registers := fun register =>
          if register = 0 then 2 else frameCopyState.machine.registers register } }

def frameMemcpyThreeState : StackFrameMachineState 64 :=
  { frameCopyState with
      machine := { frameCopyState.machine with
        registers := fun register =>
          if register = 0 then 3 else frameCopyState.machine.registers register } }

def frameCopyThreeState : StackFrameMachineState 64 :=
  { frameCopyState with
      machine := { frameCopyState.machine with
        memory := fun address =>
          if address = 0 then BitVec.ofNat 64 0x200000003 else 0 } }

example :
    (evalStackFrameFuel 3000 frameCollectorState
      (stackGcSimpleCode frameCollectorConfig)).isSome := by
  native_decide

example :
    evalStackFrameFuel 3 frameCollectorState
      (stackGcMoveListCode frameCollectorConfig) =
      some (.normal frameCollectorState) := by
  apply evalStackFrameFuel_stackGcMoveList_zero
  native_decide

example :
    evalStackFrameFuel 3 frameCollectorState
      (stackGcMoveLoopCode frameCollectorConfig) =
      some (.normal frameCollectorState) := by
  apply evalStackFrameFuel_stackGcMoveLoop_done
  native_decide

example :
    evalStackFrameFuel 3 frameCollectorState
      (stackGcMoveRootsBitmapsCode frameCollectorConfig) =
      some (.normal frameCollectorState) := by
  apply evalStackFrameFuel_stackGcMoveRootsBitmaps_zero
  native_decide

example :
    evalStackFrameFuel 9 frameMoveListOneState
      (stackGcMoveListCode frameCollectorConfig) =
      some (.normal (stackGcMoveListOneState frameCollectorConfig
        (stackGcMoveListOnePreState frameCollectorConfig frameMoveListOneState))) := by
  apply evalStackFrameFuel_stackGcMoveList_one
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · apply evalStackFrameGcMoveCode_immediate
    native_decide
  · native_decide
  · native_decide
  · native_decide

example :
    evalStackFrameFuel 90 frameMoveListCopyState
      (stackGcMoveListCode frameCollectorConfig) =
      some (.normal (stackGcMoveListOneState frameCollectorConfig
        (stackGcMoveCopyIterState frameCollectorConfig 2
          (stackGcMoveListOnePreState frameCollectorConfig
            frameMoveListCopyState)))) := by
  apply evalStackFrameFuel_stackGcMoveList_one
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · apply evalStackFrameFuel_stackGcMoveCode_copy_iter
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · intro address
      rfl
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  · native_decide
  · native_decide
  · native_decide

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 2 frameMachineState
        (stackGcMoveCode frameCollectorConfig)) 5 =
      some (stackGcNatMove frameCollectorConfig
        (frameMachineState.machine.registers 5).toNat
        0 100 0 (fun _ => 0) (fun _ => true)).value := by
  apply evalStackFrameGcMoveCode_immediate_matches_nat
  · native_decide
  · native_decide

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 1000 frameForwardingState
        (stackGcMoveCode frameCollectorConfig)) 5 =
      some (stackGcNatMove frameCollectorConfig 3 0 0 0
        (fun address => if address = 0 then 4 else 0)
        (fun _ => true)).value := by
  native_decide

example :
    evalStackFrameFuel 23 frameForwardingState
      (stackGcMoveCode frameCollectorConfig) =
      some (.normal (stackGcMoveForwardingState frameCollectorConfig
        frameForwardingState)) := by
  apply evalStackFrameFuel_stackGcMoveCode_forwarding
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl
  · native_decide

example :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 1000 frameCopyState
        (stackGcMoveCode frameCollectorConfig)) 5 =
      some (stackGcNatMove frameCollectorConfig 3 1 100 0
        (fun address => if address = 0 then 3 else 0)
        (fun _ => true)).value := by
  native_decide

example :
    evalStackFrameFuel 29 frameCopyState
      (stackGcMoveCode frameCollectorConfig) =
      some (.normal (stackGcMoveCopyState frameCollectorConfig
        frameCopyState)) := by
  apply evalStackFrameFuel_stackGcMoveCode_copy_one
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl
  · native_decide
  · native_decide

example :
    evalStackFrameFuel 4 frameCopyState
      (stackGcMemcpy frameCollectorConfig) =
      some (.normal frameCopyState) := by
  apply evalStackFrameFuel_stackGcMemcpy_zero
  native_decide

example :
    evalStackFrameFuel 20 frameMemcpyOneState
      (stackGcMemcpyBody frameCollectorConfig) =
      some (.normal (stackFrameMemcpyStep frameCollectorConfig
        frameMemcpyOneState)) := by
  apply evalStackFrameFuel_stackGcMemcpyBody
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl

example :
    evalStackFrameFuel 24 frameMemcpyOneState
      (stackGcMemcpy frameCollectorConfig) =
      some (.normal (stackFrameMemcpyStep frameCollectorConfig
        frameMemcpyOneState)) := by
  apply evalStackFrameFuel_stackGcMemcpy_one
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl

example :
    evalStackFrameFuel 52 frameMemcpyTwoState
      (stackGcMemcpy frameCollectorConfig) =
      some (.normal (stackFrameMemcpyStep frameCollectorConfig
        (stackFrameMemcpyStep frameCollectorConfig frameMemcpyTwoState))) := by
  apply evalStackFrameFuel_stackGcMemcpy_two
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl

example :
    evalStackFrameFuel 80 frameMemcpyThreeState
      (stackGcMemcpy frameCollectorConfig) =
      some (.normal (stackFrameMemcpyIter frameCollectorConfig 3
        frameMemcpyThreeState)) := by
  apply evalStackFrameFuel_stackGcMemcpy_iter
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl

example :
    evalStackFrameFuel 85 frameCopyThreeState
      (stackGcMoveCode frameCollectorConfig) =
      some (.normal (stackGcMoveCopyIterState frameCollectorConfig 2
        frameCopyThreeState)) := by
  apply evalStackFrameFuel_stackGcMoveCode_copy_iter
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro address
    rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

example :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel 1000 frameCopyState
        (stackGcMoveCode frameCollectorConfig)) 100 = some 3 := by
  native_decide

end Flapjack.RiscV
