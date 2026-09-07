import Flapjack.RiscV.WordToStack
import Flapjack.StackRemove

/-!
Semantic correctness for the first StackRemove store equation.

The abstract WordStack machine models the runtime store as a separate map and
the lowered program as word-addressed memory.  The theorem below states the
invariant needed to connect those views for a non-`CurrHeap` store.
-/

namespace Flapjack.RiscV

theorem evalStackRemoveGet [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination : Nat) (store : StackStore)
    (hstore : store ≠ .currHeap)
    (haddress : config.addressScratch ≠ config.storeBase)
    (hmemory :
      state.memory
          (state.registers config.storeBase -
            BitVec.ofNat width
              (config.bytesInWord * stackStorePosition store)) =
        state.stores store) :
    (evalWordStackMachine state (stackRemoveGet config destination store)).map
        (fun final => final.registers destination) =
      some (state.stores store) := by
  cases store <;>
    simp_all [stackRemoveGet, stackRemoveAddress, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, Ne.symm haddress]

theorem evalStackRemoveSet [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source : Nat) (store : StackStore)
    (hstore : store ≠ .currHeap)
    (haddress : config.addressScratch ≠ config.storeBase)
    (hsource : config.addressScratch ≠ source) :
    (evalWordStackMachine state (stackRemoveSet config store source)).map
        (fun final =>
          final.memory
            (state.registers config.storeBase -
              BitVec.ofNat width
                (config.bytesInWord * stackStorePosition store))) =
      some (state.registers source) := by
  cases store <;>
    simp_all [stackRemoveSet, stackRemoveAddress, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      Ne.symm haddress, Ne.symm hsource]

theorem evalStackRemoveGetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination : Nat) :
    (evalWordStackMachine state
      (stackRemoveGet config destination .currHeap)).map
        (fun final => final.registers destination) =
      some (state.registers config.currHeap) := by
  simp [stackRemoveGet, evalWordStackMachine, wordStackMachineBinOp,
    wordStackMachineWriteRegister]

theorem evalStackRemoveSetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source : Nat) :
    (evalWordStackMachine state
      (stackRemoveSet config .currHeap source)).map
        (fun final => final.registers config.currHeap) =
      some (state.registers source) := by
  simp [stackRemoveSet, evalWordStackMachine, wordStackMachineBinOp,
    wordStackMachineWriteRegister]

theorem evalStackRemoveStackAlloc_small [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (words : Nat) (hwords : words ≤ 255)
    (hscratch : config.scratch ≠ config.stackPointer) :
    (evalWordStackMachine state
      (stackRemoveStackAlloc config words)).map
        (fun final => final.registers config.stackPointer) =
      some (state.registers config.stackPointer -
        BitVec.ofNat width (config.bytesInWord * words)) := by
  by_cases hzero : words = 0
  · subst words
    simp [stackRemoveStackAlloc, stackRemoveStackDelta, evalWordStackMachine]
  · simp [stackRemoveStackAlloc, stackRemoveStackDelta, hzero,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, hwords, Ne.symm hscratch]

theorem evalStackRemoveStackLoad [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination offset : Nat)
    (haddress : config.addressScratch ≠ config.stackPointer)
    (hmemory :
      state.memory
          (state.registers config.stackPointer +
            BitVec.ofNat width (config.bytesInWord * offset)) =
        state.stack offset) :
    (evalWordStackMachine state
      (stackRemoveStackLoad config destination offset)).map
        (fun final => final.registers destination) =
      some (state.stack offset) := by
  simp [stackRemoveStackLoad, stackRemoveStackAddress, stackRemoveJoin,
    evalWordStackMachine, wordStackMachineBinOp,
    wordStackMachineWriteRegister, Ne.symm haddress, hmemory]

theorem evalStackRemoveStackStore [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source offset : Nat)
    (haddress : config.addressScratch ≠ config.stackPointer)
    (hscratch : config.addressScratch ≠ config.scratch)
    (hscratchPointer : config.scratch ≠ config.stackPointer) :
    (evalWordStackMachine state
      (stackRemoveStackStore config source offset)).map
        (fun final =>
          final.memory
            (state.registers config.stackPointer +
              BitVec.ofNat width (config.bytesInWord * offset))) =
      some (state.registers source) := by
  by_cases hmove : config.scratch = source
  · have hsourceAddress : source ≠ config.addressScratch := by
      intro hsource
      apply hscratch
      calc
        config.addressScratch = source := hsource.symm
        _ = config.scratch := hmove.symm
    simp [stackRemoveStackStore, stackRemoveStackAddress, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hmove, Ne.symm haddress, 
      hsourceAddress]
  · simp [stackRemoveStackStore, stackRemoveStackAddress, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hmove, Ne.symm haddress, Ne.symm hscratch,
      Ne.symm hscratchPointer]

end Flapjack.RiscV
