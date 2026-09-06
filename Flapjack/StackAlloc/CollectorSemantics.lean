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

def stackFrameMemcpyMemory [NeZero width]
    (config : StackGcConfig) : Nat → Word width → Word width →
      (Word width → Word width) → Word width → Word width
  | 0, _, _, memory, address => memory address
  | words + 1, source, destination, memory, address =>
      stackFrameMemcpyMemory config words
        (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord)
        (fun current => if current = destination then memory source else memory current) address

structure StackFrameMemcpyCorrespondence (state : StackFrameMachineState width)
    (words : Nat) (source destination : Word width)
    (memory : Word width → Word width) : Prop where
  count : state.machine.registers 0 = BitVec.ofNat width words
  source : state.machine.registers 2 = source
  destination : state.machine.registers 3 = destination
  memory : state.machine.memory = memory

theorem stackFrameMemcpyMemory_unchanged [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (source destination : Word width) (memory : Word width → Word width)
    (address : Word width)
    (haddress : ∀ index, index < words →
      address ≠ destination + BitVec.ofNat width
        (index * config.bytesInWord)) :
    stackFrameMemcpyMemory config words source destination memory address =
      memory address := by
  induction words generalizing source destination memory with
  | zero => rfl
  | succ words ih =>
      have hdestination : address ≠ destination := by
        intro heq
        apply haddress 0 (by omega)
        simpa using heq
      have hrest : ∀ index, index < words →
          address ≠ (destination + BitVec.ofNat width config.bytesInWord) +
            BitVec.ofNat width (index * config.bytesInWord) := by
        intro index hindex heq
        apply haddress (index + 1) (by omega)
        simpa [Nat.succ_mul, BitVec.ofNat_add, BitVec.add_assoc,
          BitVec.add_comm] using heq
      have hmemory := ih
        (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord)
        (fun current => if current = destination then memory source
          else memory current) hrest
      simp [stackFrameMemcpyMemory, hmemory, hdestination]

theorem bitVec_ofNat_succ_sub_one [NeZero width] (words : Nat) :
    BitVec.ofNat width (words + 1) - BitVec.ofNat width 1 =
      BitVec.ofNat width words := by
  rw [BitVec.ofNat_sub_ofNat_of_le]
  · rfl
  · exact Nat.one_lt_two_pow (NeZero.ne width)
  · omega

theorem stackFrameMemcpyStep_register_zero [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hcount : state.machine.registers 0 = BitVec.ofNat width (words + 1)) :
    (stackFrameMemcpyStep config state).machine.registers 0 =
      BitVec.ofNat width words := by
  have hscratch0' : 0 ≠ config.immediateScratch := Ne.symm hscratch0
  have hsubtract :
      BitVec.ofNat width (words + 1) - BitVec.ofNat width 1 =
        BitVec.ofNat width words :=
    bitVec_ofNat_succ_sub_one words
  simp [stackFrameMemcpyStep, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hcount, hsubtract, hscratch0',
    hscratch1, hscratch2, hscratch3]

theorem stackFrameMemcpyStep_register_zero_eq [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0) :
    (stackFrameMemcpyStep config state).machine.registers 0 =
      wordStackMachineBinOp .sub (state.machine.registers 0)
        (BitVec.ofNat width 1) := by
  simp [stackFrameMemcpyStep, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hscratch0, Ne.symm hscratch0]

theorem stackFrameMemcpyStep_register_one [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch1 : config.immediateScratch ≠ 1) :
    (stackFrameMemcpyStep config state).machine.registers 1 =
      state.machine.memory (state.machine.registers 2) := by
  simp [stackFrameMemcpyStep, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hscratch1, Ne.symm hscratch1]

theorem stackFrameMemcpyStep_register_source [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch2 : config.immediateScratch ≠ 2) :
    (stackFrameMemcpyStep config state).machine.registers 2 =
      wordStackMachineBinOp .add (state.machine.registers 2)
        (BitVec.ofNat width config.bytesInWord) := by
  simp [stackFrameMemcpyStep, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hscratch2, Ne.symm hscratch2]

theorem stackFrameMemcpyStep_register_destination [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch3 : config.immediateScratch ≠ 3) :
    (stackFrameMemcpyStep config state).machine.registers 3 =
      wordStackMachineBinOp .add (state.machine.registers 3)
        (BitVec.ofNat width config.bytesInWord) := by
  simp [stackFrameMemcpyStep, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hscratch3, Ne.symm hscratch3]

theorem stackFrameWriteRegister_memory [NeZero width]
    (state : StackFrameMachineState width) (register : Nat)
    (value address : Word width) :
    (stackFrameWriteRegister state register value).machine.memory address =
      state.machine.memory address := by
  rfl

theorem stackFrameWriteRegister_memory_function [NeZero width]
    (state : StackFrameMachineState width) (register : Nat)
    (value : Word width) :
    (stackFrameWriteRegister state register value).machine.memory =
      state.machine.memory := by
  rfl

theorem stackFrameWriteRegister_register_of_ne [NeZero width]
    (state : StackFrameMachineState width) (register target : Nat)
    (value : Word width) (htarget : target ≠ register) :
    (stackFrameWriteRegister state register value).machine.registers target =
      state.machine.registers target := by
  simp [stackFrameWriteRegister, wordStackMachineWriteRegister, htarget]

theorem stackFrameMemcpyStep_memory [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (address : Word width) :
    (stackFrameMemcpyStep config state).machine.memory address =
      if address = state.machine.registers 3 then
        state.machine.memory (state.machine.registers 2)
      else
        state.machine.memory address := by
  by_cases haddress : address = state.machine.registers 3
  · simp [stackFrameMemcpyStep, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, haddress]
  · simp [stackFrameMemcpyStep, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, haddress, Ne.symm haddress]

theorem stackFrameMemcpyStep_memory_function [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    (stackFrameMemcpyStep config state).machine.memory =
      (wordStackMachineWriteMemory state.machine
        (state.machine.registers 3)
        (state.machine.memory (state.machine.registers 2))).memory := by
  funext address
  rw [stackFrameMemcpyStep_memory]
  rfl

theorem stackFrameMemcpyStep_correspondence [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (source destination : Word width) (memory : Word width → Word width)
    (hstate : StackFrameMemcpyCorrespondence state (words + 1)
      source destination memory)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3) :
    StackFrameMemcpyCorrespondence (stackFrameMemcpyStep config state) words
      (source + BitVec.ofNat width config.bytesInWord)
      (destination + BitVec.ofNat width config.bytesInWord)
      (fun current => if current = destination then memory source else memory current) := by
  refine { count := ?_, source := ?_, destination := ?_, memory := ?_ }
  · exact stackFrameMemcpyStep_register_zero config words state
      hscratch0 hscratch1 hscratch2 hscratch3 hstate.count
  · simpa [wordStackMachineBinOp, hstate.source] using
      stackFrameMemcpyStep_register_source config state hscratch2
  · simpa [wordStackMachineBinOp, hstate.destination] using
      stackFrameMemcpyStep_register_destination config state hscratch3
  · rw [stackFrameMemcpyStep_memory_function config state, hstate.source,
      hstate.destination, hstate.memory]
    funext current
    simp [wordStackMachineWriteMemory, hstate.memory]

theorem evalStackFrameFuel_loop_normal [NeZero width]
    (fuel : Nat) (state state' : StackFrameMachineState width)
    (body : StackProg Nat)
    (hbody :
      evalStackFrameFuel fuel state body = some (.normal state')) :
    evalStackFrameFuel (fuel + 1) state (.loop body) =
      evalStackFrameFuel fuel state' (.loop body) := by
  have hbody' :
      evalStackFrameFuelWithCode fuel (fun _ => none) state body =
        some (.normal state') := by
    simpa [evalStackFrameFuel] using hbody
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hbody']

theorem evalStackFrameFuel_stackGcMemcpy_iter [NeZero width]
    (config : StackGcConfig) (fuel words : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hcount : state.machine.registers 0 = BitVec.ofNat width words)
    (hbound : words < 2 ^ width)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + words + 24) state
        (stackGcMemcpy config) =
      some (.normal (stackFrameMemcpyIter config words state)) := by
  induction words generalizing fuel state with
  | zero =>
      have hcount' : state.machine.registers 0 = 0 := by
        simpa using hcount
      have hzero := evalStackFrameFuel_stackGcMemcpy_zero config (fuel + 20)
        state hcount'
      simpa [stackFrameMemcpyIter, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hzero
  | succ words ih =>
      have hwords : words < 2 ^ width := by omega
      have hzero : BitVec.ofNat width (words + 1) ≠ 0 := by
        intro hzero
        have hzero' := congrArg BitVec.toNat hzero
        have hzero'' : words + 1 = 0 := by
          simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] using hzero'
        omega
      have hcondition :
          stackMachineCondition state.machine .notEqual 0 (.imm 0) = true := by
        have hz : BitVec.ofNat width (words + 1) ≠ (0#width) := by
          exact hzero
        simp only [stackMachineCondition]
        rw [bne_iff_ne]
        rw [hcount]
        exact hz
      have hstep :=
        evalStackFrameFuel_stackGcMemcpyBody config (fuel + words + 3)
          state hscratch0 hscratch1 hscratch2 hscratch3 hheaderDomain
      have hite :
          evalStackFrameFuel (fuel + words + 24) state
              (.ite .notEqual 0 (.imm 0) (stackGcMemcpyBody config)
                (.break 0)) =
            evalStackFrameFuel (fuel + words + 23) state
              (stackGcMemcpyBody config) := by
        apply evalStackFrameFuel_ite_true
        exact hcondition
      have hbody :
          evalStackFrameFuel (fuel + words + 24) state
              (.ite .notEqual 0 (.imm 0) (stackGcMemcpyBody config)
                (.break 0)) =
            some (.normal (stackFrameMemcpyStep config state)) := by
        rw [hite]
        have hfuel : fuel + words + 3 + 20 = fuel + words + 23 := by omega
        rw [hfuel] at hstep
        exact hstep
      have hloop := evalStackFrameFuel_loop_normal
        (fuel + words + 24) state (stackFrameMemcpyStep config state)
        (.ite .notEqual 0 (.imm 0) (stackGcMemcpyBody config) (.break 0))
        hbody
      have hcount' := stackFrameMemcpyStep_register_zero config words state
        hscratch0 hscratch1 hscratch2 hscratch3 hcount
      have hdomain' :
          ∀ address, (stackFrameMemcpyStep config state).memoryDomain address = true := by
        intro address
        exact hheaderDomain address
      have hrest := ih fuel (stackFrameMemcpyStep config state)
        hcount' hwords hdomain'
      have hfuel : fuel + (words + 1) + 24 = fuel + words + 25 := by omega
      rw [hfuel]
      simpa [stackGcMemcpy, stackGcWhile, stackFrameMemcpyIter,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hloop.trans hrest

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

theorem stackFrameMemcpyIter_memory [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3) :
    (stackFrameMemcpyIter config words state).machine.memory =
      fun address => stackFrameMemcpyMemory config words
        (state.machine.registers 2) (state.machine.registers 3)
        state.machine.memory address := by
  induction words generalizing state with
  | zero => rfl
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).machine.memory = _
      rw [ih]
      rw [stackFrameMemcpyStep_register_source config state hscratch2]
      rw [stackFrameMemcpyStep_register_destination config state hscratch3]
      rw [stackFrameMemcpyStep_memory_function config state]
      rfl

theorem stackFrameMemcpyIter_register_zero [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hcount : state.machine.registers 0 = BitVec.ofNat width words)
    (hbound : words < 2 ^ width) :
    (stackFrameMemcpyIter config words state).machine.registers 0 = 0 := by
  induction words generalizing state with
  | zero => simpa [stackFrameMemcpyIter] using hcount
  | succ words ih =>
      have hbound' : words < 2 ^ width := by omega
      have hcount' := stackFrameMemcpyStep_register_zero config words state
        hscratch0 hscratch1 hscratch2 hscratch3 hcount
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).machine.registers 0 = 0
      exact ih (stackFrameMemcpyStep config state) hcount' hbound'

theorem stackFrameMemcpyIter_register_source [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch2 : config.immediateScratch ≠ 2) :
    (stackFrameMemcpyIter config words state).machine.registers 2 =
      wordStackMachineBinOp .add (state.machine.registers 2)
        (BitVec.ofNat width (words * config.bytesInWord)) := by
  induction words generalizing state with
  | zero => simp [stackFrameMemcpyIter, wordStackMachineBinOp]
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).machine.registers 2 = _
      rw [ih]
      rw [stackFrameMemcpyStep_register_source config state hscratch2]
      simp only [wordStackMachineBinOp, Nat.succ_mul, Nat.one_mul,
        BitVec.ofNat_add]
      rw [BitVec.add_assoc]
      congr 1
      exact BitVec.add_comm _ _

theorem stackFrameMemcpyIter_register_destination [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch3 : config.immediateScratch ≠ 3) :
    (stackFrameMemcpyIter config words state).machine.registers 3 =
      wordStackMachineBinOp .add (state.machine.registers 3)
        (BitVec.ofNat width (words * config.bytesInWord)) := by
  induction words generalizing state with
  | zero => simp [stackFrameMemcpyIter, wordStackMachineBinOp]
  | succ words ih =>
      change (stackFrameMemcpyIter config words
        (stackFrameMemcpyStep config state)).machine.registers 3 = _
      rw [ih]
      rw [stackFrameMemcpyStep_register_destination config state hscratch3]
      simp only [wordStackMachineBinOp, Nat.succ_mul, Nat.one_mul,
        BitVec.ofNat_add]
      rw [BitVec.add_assoc]
      congr 1
      exact BitVec.add_comm _ _

theorem stackFrameMemcpyIter_correspondence [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (source destination : Word width) (memory : Word width → Word width)
    (hstate : StackFrameMemcpyCorrespondence state words source destination memory)
    (hbound : words < 2 ^ width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3) :
    StackFrameMemcpyCorrespondence (stackFrameMemcpyIter config words state) 0
      (source + BitVec.ofNat width (words * config.bytesInWord))
      (destination + BitVec.ofNat width (words * config.bytesInWord))
      (fun address => stackFrameMemcpyMemory config words source destination memory address) := by
  refine { count := ?_, source := ?_, destination := ?_, memory := ?_ }
  · exact stackFrameMemcpyIter_register_zero config words state
      hscratch0 hscratch1 hscratch2 hscratch3 hstate.count hbound
  · simpa [wordStackMachineBinOp, hstate.source] using
      stackFrameMemcpyIter_register_source config words state hscratch2
  · simpa [wordStackMachineBinOp, hstate.destination] using
      stackFrameMemcpyIter_register_destination config words state hscratch3
  · simpa [hstate.source, hstate.destination, hstate.memory] using
      stackFrameMemcpyIter_memory config words state hscratch2 hscratch3

end Flapjack.RiscV
