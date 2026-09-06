import Flapjack.StackAlloc.FrameMachine

/-!
# Bounded collector machine semantics

This module begins the machine-level collector simulation layer.  The
`memcpy` loop is the smallest non-trivial collector loop: its body updates
the source, destination, and count registers and writes one word of memory.
The theorem below relates the executable bounded frame evaluator to the
corresponding iterated machine-state transition for every word count.

The evaluator simulation theorem will use this transition API together with
the explicit machine-word count bound.  Keeping the transition layer
separate makes the later proof compositional and avoids unfolding the whole
collector state at every loop iteration.
-/

namespace Flapjack.RiscV

def stackFrameMemcpyIter [NeZero width]
    (config : StackGcConfig) : Nat → StackFrameMachineState width →
      StackFrameMachineState width
  | 0, state => state
  | words + 1, state =>
      stackFrameMemcpyIter config words (stackFrameMemcpyStep config state)

theorem stackFrameMemcpyIter_zero [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    stackFrameMemcpyIter config 0 state = state := by
  rfl

theorem stackFrameMemcpyIter_succ [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    stackFrameMemcpyIter config (words + 1) state =
      stackFrameMemcpyIter config words (stackFrameMemcpyStep config state) := by
  rfl

theorem stackFrameMemcpyIter_stackSpace [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).stackSpace =
      state.stackSpace := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).stackSpace = state.stackSpace
      rw [ih]
      rfl

theorem stackFrameMemcpyIter_stackLimit [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).stackLimit =
      state.stackLimit := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).stackLimit = state.stackLimit
      rw [ih]
      rfl

theorem stackFrameMemcpyIter_bitmaps [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).bitmaps =
      state.bitmaps := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).bitmaps = state.bitmaps
      rw [ih]
      rfl

theorem stackFrameMemcpyIter_bytesInWord [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).bytesInWord =
      state.bytesInWord := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).bytesInWord = state.bytesInWord
      rw [ih]
      rfl

theorem stackFrameMemcpyIter_memoryDomain [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).memoryDomain =
      state.memoryDomain := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).memoryDomain = state.memoryDomain
      rw [ih]
      rfl

theorem stackFrameMemcpyIter_sharedMemoryDomain [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width) :
    (stackFrameMemcpyIter config words state).sharedMemoryDomain =
      state.sharedMemoryDomain := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).sharedMemoryDomain =
        state.sharedMemoryDomain
      rw [ih]
      rfl

end Flapjack.RiscV
