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
    bitmaps := [13, 29] }

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
    bitmaps := [0] }

def frameCollectorConfig : StackGcConfig :=
  { shiftLength := 11
    smallShiftLength := 9
    lenSize := 32
    wordShift := 3
    wordBits := 64
    bytesInWord := 8
    immediateScratch := 31 }

def frameForwardingState : StackFrameMachineState 64 :=
  { machine :=
      { registers := fun register => if register = 5 then 3 else 0
        stack := fun _ => 0
        stores := fun _ => 0
        memory := fun address => if address = 0 then 4 else 0
        sharedMemory := fun _ => 0 }
    stackSpace := 8
    stackLimit := 16
    bitmaps := [0] }

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
    bitmaps := [0] }

example :
    (evalStackFrameFuel 3000 frameCollectorState
      (stackGcSimpleCode frameCollectorConfig)).isSome := by
  native_decide

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
    stackFrameNormalRegisterNat
      (evalStackFrameFuel 1000 frameCopyState
        (stackGcMoveCode frameCollectorConfig)) 5 =
      some (stackGcNatMove frameCollectorConfig 3 1 100 0
        (fun address => if address = 0 then 3 else 0)
        (fun _ => true)).value := by
  native_decide

example :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel 1000 frameCopyState
        (stackGcMoveCode frameCollectorConfig)) 100 = some 3 := by
  native_decide

end Flapjack.RiscV
