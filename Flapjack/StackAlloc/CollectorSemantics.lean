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

theorem evalStackFrameFuel_stackGcMemcpy_correspondence [NeZero width]
    (config : StackGcConfig) (fuel words : Nat)
    (state : StackFrameMachineState width)
    (source destination : Word width) (memory : Word width → Word width)
    (hstate : StackFrameMemcpyCorrespondence state words source destination memory)
    (hbound : words < 2 ^ width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + words + 24) state (stackGcMemcpy config) =
        some (.normal (stackFrameMemcpyIter config words state)) ∧
      StackFrameMemcpyCorrespondence (stackFrameMemcpyIter config words state) 0
        (source + BitVec.ofNat width (words * config.bytesInWord))
        (destination + BitVec.ofNat width (words * config.bytesInWord))
        (fun address => stackFrameMemcpyMemory config words source destination memory address) := by
  constructor
  · exact evalStackFrameFuel_stackGcMemcpy_iter config fuel words state
      hscratch0 hscratch1 hscratch2 hscratch3 hstate.count hbound hheaderDomain
  · exact stackFrameMemcpyIter_correspondence config words state source destination memory
      hstate hbound hscratch0 hscratch1 hscratch2 hscratch3

theorem stackFrameMemcpyIter_register_source_toNat [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch2 : config.immediateScratch ≠ 2) :
    ((stackFrameMemcpyIter config words state).machine.registers 2).toNat =
      ((state.machine.registers 2).toNat + words * config.bytesInWord) % 2 ^ width := by
  rw [stackFrameMemcpyIter_register_source config words state hscratch2]
  simp [wordStackMachineBinOp, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.add_mod, Nat.mod_mod]

theorem stackFrameMemcpyIter_register_destination_toNat [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (state : StackFrameMachineState width)
    (hscratch3 : config.immediateScratch ≠ 3) :
    ((stackFrameMemcpyIter config words state).machine.registers 3).toNat =
      ((state.machine.registers 3).toNat + words * config.bytesInWord) % 2 ^ width := by
  rw [stackFrameMemcpyIter_register_destination config words state hscratch3]
  simp [wordStackMachineBinOp, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.add_mod, Nat.mod_mod]

theorem stackFrameMemcpyMemory_update_toNat [NeZero width]
    (source destination : Word width) (memory : Nat → Nat) :
    (fun current : Word width =>
        if current = destination then BitVec.ofNat width (memory source.toNat)
        else BitVec.ofNat width (memory current.toNat)) =
      (fun current : Word width =>
        BitVec.ofNat width
          (if current.toNat = destination.toNat then memory source.toNat
           else memory current.toNat)) := by
  funext current
  by_cases hcurrent : current = destination
  · simp [hcurrent]
  · have hcurrent' : current.toNat ≠ destination.toNat := by
      intro heq
      apply hcurrent
      exact BitVec.eq_of_toNat_eq heq
    simp [hcurrent, hcurrent']

theorem stackFrameMemcpyMemory_toNat [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (source destination : Word width) (memory : Nat → Nat)
    (hmemory : ∀ address, memory address < 2 ^ width)
    (hsource : ∀ index, index ≤ words →
      source.toNat + index * config.bytesInWord < 2 ^ width)
    (hdestination : ∀ index, index ≤ words →
      destination.toNat + index * config.bytesInWord < 2 ^ width)
    (address : Word width) :
    (stackFrameMemcpyMemory config words source destination
      (fun current => BitVec.ofNat width (memory current.toNat)) address).toNat =
      (stackGcNatMemcpy config words source.toNat destination.toNat memory
        (fun _ => true)).memory address.toNat := by
  induction words generalizing source destination memory address with
  | zero =>
      simp [stackFrameMemcpyMemory, stackGcNatMemcpy,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hmemory _)]
  | succ words ih =>
      have hbytes : config.bytesInWord < 2 ^ width := by
        have h := hsource 1 (by omega)
        omega
      have hsource_add :
          (source + BitVec.ofNat width config.bytesInWord).toNat =
            source.toNat + config.bytesInWord := by
        have hsum : source.toNat + config.bytesInWord < 2 ^ width := by
          simpa using hsource 1 (by omega)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hbytes]
        exact Nat.mod_eq_of_lt hsum
      have hdestination_add :
          (destination + BitVec.ofNat width config.bytesInWord).toNat =
            destination.toNat + config.bytesInWord := by
        have hsum : destination.toNat + config.bytesInWord < 2 ^ width := by
          simpa using hdestination 1 (by omega)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hbytes]
        exact Nat.mod_eq_of_lt hsum
      let memory' : Nat → Nat := fun current =>
        if current = destination.toNat then memory source.toNat else memory current
      have hmemory' : ∀ current, memory' current < 2 ^ width := by
        intro current
        simp only [memory']
        split
        · exact hmemory _
        · exact hmemory _
      have hsource' : ∀ index, index ≤ words →
          (source + BitVec.ofNat width config.bytesInWord).toNat +
              index * config.bytesInWord < 2 ^ width := by
        intro index hindex
        rw [hsource_add]
        have h := hsource (index + 1) (by omega)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hdestination' : ∀ index, index ≤ words →
          (destination + BitVec.ofNat width config.bytesInWord).toNat +
              index * config.bytesInWord < 2 ^ width := by
        intro index hindex
        rw [hdestination_add]
        have h := hdestination (index + 1) (by omega)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hmemoryWord :
          (fun current : Word width =>
            if current = destination then
              BitVec.ofNat width (memory source.toNat)
            else BitVec.ofNat width (memory current.toNat)) =
            (fun current => BitVec.ofNat width (memory' current.toNat)) := by
        simpa [memory'] using
          stackFrameMemcpyMemory_update_toNat source destination memory
      rw [show stackFrameMemcpyMemory config (words + 1) source destination
          (fun current => BitVec.ofNat width (memory current.toNat)) address =
          stackFrameMemcpyMemory config words
            (source + BitVec.ofNat width config.bytesInWord)
            (destination + BitVec.ofNat width config.bytesInWord)
            (fun current => if current = destination then
              BitVec.ofNat width (memory source.toNat)
            else BitVec.ofNat width (memory current.toNat)) address by rfl]
      rw [hmemoryWord]
      rw [ih (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord) memory'
        hmemory' hsource' hdestination' address]
      simp [stackGcNatMemcpy, memory', hsource_add, hdestination_add]

theorem evalStackFrameFuel_stackGcMemcpy_matches_nat [NeZero width]
    (config : StackGcConfig) (fuel words : Nat)
    (state : StackFrameMachineState width)
    (source destination : Nat) (memory : Nat → Nat)
    (hstate : StackFrameMemcpyCorrespondence state words
      (BitVec.ofNat width source) (BitVec.ofNat width destination)
      (fun current => BitVec.ofNat width (memory current.toNat)))
    (hmemory : ∀ address, memory address < 2 ^ width)
    (hsource : ∀ index, index ≤ words →
      source + index * config.bytesInWord < 2 ^ width)
    (hdestination : ∀ index, index ≤ words →
      destination + index * config.bytesInWord < 2 ^ width)
    (hbound : words < 2 ^ width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + words + 24) state (stackGcMemcpy config) =
        some (.normal (stackFrameMemcpyIter config words state)) ∧
      ((stackFrameMemcpyIter config words state).machine.registers 3).toNat =
        (stackGcNatMemcpy config words source destination memory
          (fun _ => true)).nextAddress ∧
      ∀ address : Word width,
        ((stackFrameMemcpyIter config words state).machine.memory address).toNat =
          (stackGcNatMemcpy config words source destination memory
            (fun _ => true)).memory address.toNat := by
  have hsource0 : source < 2 ^ width := by
    simpa using hsource 0 (by omega)
  have hdestination0 : destination < 2 ^ width := by
    simpa using hdestination 0 (by omega)
  have hcorrespondence := evalStackFrameFuel_stackGcMemcpy_correspondence
    config fuel words state (BitVec.ofNat width source)
      (BitVec.ofNat width destination)
      (fun current => BitVec.ofNat width (memory current.toNat)) hstate hbound
      hscratch0 hscratch1 hscratch2 hscratch3 hheaderDomain
  refine ⟨hcorrespondence.1, ?_, ?_⟩
  · have hdestination' := stackFrameMemcpyIter_register_destination_toNat
      config words state hscratch3
    rw [hstate.destination] at hdestination'
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdestination0] at hdestination'
    rw [hdestination']
    rw [stackGcNatMemcpy_nextAddress]
    exact Nat.mod_eq_of_lt (hdestination words (by omega))
  · intro address
    rw [hcorrespondence.2.memory]
    have hmemory' := stackFrameMemcpyMemory_toNat config words
      (BitVec.ofNat width source) (BitVec.ofNat width destination) memory
      hmemory
      (by
        intro index hindex
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsource0] using
          hsource index hindex)
      (by
        intro index hindex
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdestination0] using
          hdestination index hindex)
      address
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsource0,
      Nat.mod_eq_of_lt hdestination0] using hmemory'

def stackGcMoveListImmediateState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterLoad := stackFrameWriteRegister state 5
    (state.machine.memory (state.machine.registers 8))
  let afterCount := stackFrameWriteRegister
    (stackFrameWriteRegister afterLoad config.immediateScratch
      (BitVec.ofNat width 1)) 7
    (wordStackMachineBinOp .sub (afterLoad.machine.registers 7)
      (BitVec.ofNat width 1))
  let afterStore := { afterCount with machine :=
    (wordStackMachineWriteMemory afterCount.machine
      (afterCount.machine.registers 8) (afterCount.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))

theorem evalStackFrameFuel_stackGcMoveList_immediate_one [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hvalue : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0) :
    evalStackFrameFuel (fuel + 19) state (stackGcMoveListCode config) =
      some (.normal (stackGcMoveListImmediateState config state)) := by
  let afterLoad := stackFrameWriteRegister state 5
    (state.machine.memory (state.machine.registers 8))
  let afterCount := stackFrameWriteRegister
    (stackFrameWriteRegister afterLoad config.immediateScratch
      (BitVec.ofNat width 1)) 7
    (wordStackMachineBinOp .sub (afterLoad.machine.registers 7)
      (BitVec.ofNat width 1))
  let afterStore := { afterCount with machine :=
    (wordStackMachineWriteMemory afterCount.machine
      (afterCount.machine.registers 8) (afterCount.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  let afterFinal := stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))
  have hvalue' : afterCount.machine.registers 5 &&&
      BitVec.ofNat width 1 = 0 := by
    simp [afterCount, afterLoad, stackFrameWriteRegister,
      wordStackMachineWriteRegister, hscratch5, Ne.symm hscratch5]
    exact hvalue
  have hsub : evalStackFrameFuel (fuel + 15) afterLoad
      (stackGcSubOne config 7) = some (.normal afterCount) := by
    simp [stackGcSubOne, stackGcSubImmediate, stackGcAddImmediate,
      stackGcConst, stackGcSub, stackSeq, evalStackFrameFuel,
      evalStackFrameFuelWithCode, stackFrameBasic, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp, afterCount,
      afterLoad, hscratch7, Ne.symm hscratch7]
  have hmove := evalStackFrameGcMoveCode_immediate config (fuel + 12)
    afterCount hvalue'
  have hdomain' : afterCount.memoryDomain
      (afterCount.machine.registers 8) = true := by
    simpa [afterCount, afterLoad, stackFrameWriteRegister,
      wordStackMachineWriteRegister, hscratch7, hscratch8,
      Ne.symm hscratch7, Ne.symm hscratch8] using hdomain
  have hstore := evalStackFrameFuel_memStore (fuel + 12) afterCount 5 8
    hdomain'
  have hadd : evalStackFrameFuel (fuel + 13) afterStore
      (stackGcAddBytes config 8) = some (.normal afterFinal) := by
    simp [stackGcAddBytes, stackGcAddImmediate, stackGcConst, stackGcAdd,
      stackSeq, evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
      stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp, afterFinal,
      afterScratch, afterStore, hscratch8, Ne.symm hscratch8]
  have hload := evalStackFrameFuel_memLoad (fuel + 16) state 5 8 hdomain
  have hbody : evalStackFrameFuel (fuel + 17) state
      (stackSeq [
        .inst (.mem .load 5 8),
        stackGcSubOne config 7,
        stackGcMoveCode config,
        .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) = some (.normal afterFinal) := by
    change evalStackFrameFuel (fuel + 17) state
      (.seq (.inst (.mem .load 5 8))
        (stackSeq [
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])) = some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 16) state afterLoad
      (.inst (.mem .load 5 8))
      (stackSeq [stackGcSubOne config 7, stackGcMoveCode config,
        .inst (.mem .store 5 8), stackGcAddBytes config 8]) hload]
    change evalStackFrameFuel (fuel + 16) afterLoad
      (.seq (stackGcSubOne config 7)
        (stackSeq [stackGcMoveCode config,
          .inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 15) afterLoad afterCount
      (stackGcSubOne config 7)
      (stackSeq [stackGcMoveCode config, .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) hsub]
    have hmove' : evalStackFrameFuel (fuel + 14) afterCount
        (stackGcMoveCode config) = some (.normal afterCount) := by
      simpa [Nat.add_assoc] using hmove
    change evalStackFrameFuel (fuel + 15) afterCount
      (.seq (stackGcMoveCode config)
        (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 14) afterCount afterCount
      (stackGcMoveCode config)
      (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8]) hmove']
    change evalStackFrameFuel (fuel + 14) afterCount
      (.seq (.inst (.mem .store 5 8)) (stackGcAddBytes config 8)) =
      some (.normal afterFinal)
    have hstore' : evalStackFrameFuel (fuel + 13) afterCount
        (.inst (.mem .store 5 8)) = some (.normal afterStore) := by
      simpa [Nat.add_assoc] using hstore
    rw [evalStackFrameFuel_seq_normal (fuel + 13) afterCount afterStore
      (.inst (.mem .store 5 8)) (stackGcAddBytes config 8) hstore']
    simpa [Nat.add_assoc] using hadd
  have hcondition :
      stackMachineCondition state.machine .notEqual 7 (.imm 0) = true := by
    simp [stackMachineCondition, hone, NeZero.ne width]
  have hcondition' :
      stackMachineCondition afterFinal.machine .notEqual 7 (.imm 0) = false := by
    simp [stackMachineCondition, afterFinal, afterScratch, afterStore,
      afterCount, afterLoad, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, hone,
      hscratch7, hscratch8, Ne.symm hscratch7, Ne.symm hscratch8]
  have hite : evalStackFrameFuel (fuel + 18) state
      (.ite .notEqual 7 (.imm 0)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])
        (.break 0)) = some (.normal afterFinal) := by
    rw [evalStackFrameFuel_ite_true (fuel + 17) state .notEqual 7 (.imm 0)
      _ (.break 0) hcondition]
    exact hbody
  have hdone : evalStackFrameFuel (fuel + 18) afterFinal
      (.loop (.ite .notEqual 7 (.imm 0)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])
        (.break 0))) = some (.normal afterFinal) := by
    simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hcondition']
  calc
    evalStackFrameFuel (fuel + 19) state (stackGcMoveListCode config) =
        evalStackFrameFuel (fuel + 19) state
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by rfl
    _ = evalStackFrameFuel (fuel + 18) afterFinal
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by
      exact evalStackFrameFuel_loop_normal (fuel + 18) state afterFinal
        (.ite .notEqual 7 (.imm 0)
          (stackSeq [
            .inst (.mem .load 5 8),
            stackGcSubOne config 7,
            stackGcMoveCode config,
            .inst (.mem .store 5 8),
            stackGcAddBytes config 8])
          (.break 0)) hite
    _ = some (.normal (stackGcMoveListImmediateState config state)) := by
      simpa [stackGcMoveListImmediateState, afterFinal, afterScratch,
        afterStore, afterCount, afterLoad] using hdone

def stackGcMoveListAfterCount [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterLoad := stackFrameWriteRegister state 5
    (state.machine.memory (state.machine.registers 8))
  stackFrameWriteRegister
    (stackFrameWriteRegister afterLoad config.immediateScratch
      (BitVec.ofNat width 1)) 7
    (wordStackMachineBinOp .sub (afterLoad.machine.registers 7)
      (BitVec.ofNat width 1))

def stackGcMoveListForwardingState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterCount := stackGcMoveListAfterCount config state
  let afterMove := stackGcMoveForwardingState config afterCount
  let afterStore := { afterMove with machine :=
    (wordStackMachineWriteMemory afterMove.machine
      (afterMove.machine.registers 8) (afterMove.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))

theorem evalStackFrameFuel_stackGcMoveList_forwarding_one [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ address,
      (stackGcMoveListAfterCount config state).memoryDomain address = true)
    (hforward :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 = 0)
    (hstoreDomain :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveForwardingState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true) :
    evalStackFrameFuel (fuel + 40) state (stackGcMoveListCode config) =
      some (.normal (stackGcMoveListForwardingState config state)) := by
  let afterLoad := stackFrameWriteRegister state 5
    (state.machine.memory (state.machine.registers 8))
  let afterCount := stackGcMoveListAfterCount config state
  let afterMove := stackGcMoveForwardingState config afterCount
  let afterStore := { afterMove with machine :=
    (wordStackMachineWriteMemory afterMove.machine
      (afterMove.machine.registers 8) (afterMove.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  let afterFinal := stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))
  have hsub : evalStackFrameFuel (fuel + 36) afterLoad
      (stackGcSubOne config 7) = some (.normal afterCount) := by
    simp [afterCount, afterLoad, stackGcMoveListAfterCount,
      stackGcSubOne, stackGcSubImmediate, stackGcAddImmediate,
      stackGcConst, stackGcSub, stackSeq, evalStackFrameFuel,
      evalStackFrameFuelWithCode, stackFrameBasic, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp, hscratch7,
      Ne.symm hscratch7]
  have hodd' : afterCount.machine.registers 5 &&&
      BitVec.ofNat width 1 ≠ 0 := by
    simpa [afterCount] using hodd
  have hmove := evalStackFrameFuel_stackGcMoveCode_forwarding_fuel
    config (fuel + 12) afterCount hscratch0 hscratch1 hscratch5 hodd'
      hheaderDomain hforward
  have hstore := evalStackFrameFuel_memStore (fuel + 33) afterMove 5 8
    hstoreDomain
  have hadd : evalStackFrameFuel (fuel + 34) afterStore
      (stackGcAddBytes config 8) = some (.normal afterFinal) := by
    simp [stackGcAddBytes, stackGcAddImmediate, stackGcConst, stackGcAdd,
      stackSeq, evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, afterFinal, afterScratch, afterStore,
      hscratch8, Ne.symm hscratch8]
  have hload := evalStackFrameFuel_memLoad (fuel + 37) state 5 8 hdomain
  have hbody : evalStackFrameFuel (fuel + 38) state
      (stackSeq [
        .inst (.mem .load 5 8),
        stackGcSubOne config 7,
        stackGcMoveCode config,
        .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) = some (.normal afterFinal) := by
    change evalStackFrameFuel (fuel + 38) state
      (.seq (.inst (.mem .load 5 8))
        (stackSeq [stackGcSubOne config 7, stackGcMoveCode config,
          .inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 37) state afterLoad
      (.inst (.mem .load 5 8))
      (stackSeq [stackGcSubOne config 7, stackGcMoveCode config,
        .inst (.mem .store 5 8), stackGcAddBytes config 8]) hload]
    change evalStackFrameFuel (fuel + 37) afterLoad
      (.seq (stackGcSubOne config 7)
        (stackSeq [stackGcMoveCode config,
          .inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 36) afterLoad afterCount
      (stackGcSubOne config 7)
      (stackSeq [stackGcMoveCode config, .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) hsub]
    have hmove' : evalStackFrameFuel (fuel + 35) afterCount
        (stackGcMoveCode config) = some (.normal afterMove) := by
      simpa [afterMove, Nat.add_assoc] using hmove
    change evalStackFrameFuel (fuel + 36) afterCount
      (.seq (stackGcMoveCode config)
        (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 35) afterCount afterMove
      (stackGcMoveCode config)
      (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8]) hmove']
    change evalStackFrameFuel (fuel + 35) afterMove
      (.seq (.inst (.mem .store 5 8)) (stackGcAddBytes config 8)) =
      some (.normal afterFinal)
    have hstore' : evalStackFrameFuel (fuel + 34) afterMove
        (.inst (.mem .store 5 8)) = some (.normal afterStore) := by
      simpa [afterStore, Nat.add_assoc] using hstore
    rw [evalStackFrameFuel_seq_normal (fuel + 34) afterMove afterStore
      (.inst (.mem .store 5 8)) (stackGcAddBytes config 8) hstore']
    simpa [Nat.add_assoc] using hadd
  have hcondition :
      stackMachineCondition state.machine .notEqual 7 (.imm 0) = true := by
    simp [stackMachineCondition, hone, NeZero.ne width]
  have hcondition' :
      stackMachineCondition afterFinal.machine .notEqual 7 (.imm 0) = false := by
    simp [stackMachineCondition, afterFinal, afterScratch, afterStore,
      afterMove, afterCount, stackGcMoveListAfterCount, afterLoad,
      stackGcMoveForwardingState, stackGcMoveForwardingSuffixState,
      stackGcMoveAddressState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, hone, hscratch7, hscratch8,
      Ne.symm hscratch7, Ne.symm hscratch8]
  have hite : evalStackFrameFuel (fuel + 39) state
      (.ite .notEqual 7 (.imm 0)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])
        (.break 0)) = some (.normal afterFinal) := by
    rw [evalStackFrameFuel_ite_true (fuel + 38) state .notEqual 7 (.imm 0)
      _ (.break 0) hcondition]
    exact hbody
  have hdone : evalStackFrameFuel (fuel + 39) afterFinal
      (.loop (.ite .notEqual 7 (.imm 0)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])
        (.break 0))) = some (.normal afterFinal) := by
    simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hcondition']
  calc
    evalStackFrameFuel (fuel + 40) state (stackGcMoveListCode config) =
        evalStackFrameFuel (fuel + 40) state
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by rfl
    _ = evalStackFrameFuel (fuel + 39) afterFinal
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by
      exact evalStackFrameFuel_loop_normal (fuel + 39) state afterFinal
        (.ite .notEqual 7 (.imm 0)
          (stackSeq [
            .inst (.mem .load 5 8),
            stackGcSubOne config 7,
            stackGcMoveCode config,
            .inst (.mem .store 5 8),
            stackGcAddBytes config 8])
          (.break 0)) hite
    _ = some (.normal (stackGcMoveListForwardingState config state)) := by
      simpa [stackGcMoveListForwardingState, afterFinal, afterScratch,
        afterStore, afterMove, afterCount] using hdone

end Flapjack.RiscV
