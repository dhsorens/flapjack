import Flapjack.StackAlloc.FrameMachine

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

end Flapjack.RiscV
