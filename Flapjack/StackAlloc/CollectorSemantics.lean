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

def stackFrameIterate [NeZero width]
    (step : StackFrameMachineState width → StackFrameMachineState width) :
    Nat → StackFrameMachineState width → StackFrameMachineState width
  | 0, state => state
  | iterations + 1, state => stackFrameIterate step iterations (step state)

theorem evalStackFrameFuel_loop_iterate [NeZero width]
    (fuel stepFuel iterations : Nat)
    (state : StackFrameMachineState width)
    (operator : Cmp) (condition : Nat) (right : WordRegImm Nat)
    (body : StackProg Nat)
    (step : StackFrameMachineState width → StackFrameMachineState width)
    (hcondition : ∀ current, current < iterations →
      stackMachineCondition
        (stackFrameIterate step current state).machine operator condition right = true)
    (hbody : ∀ current extra, current < iterations →
      evalStackFrameFuel (extra + stepFuel)
        (stackFrameIterate step current state) body =
        some (.normal (stackFrameIterate step (current + 1) state)))
    (hfinal :
      stackMachineCondition
        (stackFrameIterate step iterations state).machine operator condition right = false) :
    evalStackFrameFuel (fuel + iterations + stepFuel + 3) state
        (.loop (.ite operator condition right body (.break 0))) =
      some (.normal (stackFrameIterate step iterations state)) := by
  induction iterations generalizing state with
  | zero =>
      have hfinal' :
          stackMachineCondition state.machine operator condition right = false := by
        simpa [stackFrameIterate] using hfinal
      simp [stackFrameIterate, evalStackFrameFuel, evalStackFrameFuelWithCode,
        hfinal']
  | succ iterations ih =>
      have hcondition0 := hcondition 0 (by omega)
      have hbody0 := hbody 0 (fuel + iterations + 2) (by omega)
      have hite :
          evalStackFrameFuel (fuel + iterations + stepFuel + 3) state
              (.ite operator condition right body (.break 0)) =
            some (.normal (step state)) := by
        rw [show fuel + iterations + stepFuel + 3 =
          (fuel + iterations + stepFuel + 2) + 1 by omega]
        rw [evalStackFrameFuel_ite_true
          (fuel + iterations + stepFuel + 2) state operator condition right
          body (.break 0) hcondition0]
        have hfuel : fuel + iterations + 2 + stepFuel =
            fuel + iterations + stepFuel + 2 := by omega
        rw [hfuel] at hbody0
        simpa [stackFrameIterate] using hbody0
      have hloop := evalStackFrameFuel_loop_normal
        (fuel + iterations + stepFuel + 3) state (step state)
        (.ite operator condition right body (.break 0)) hite
      have hcondition' : ∀ current, current < iterations →
          stackMachineCondition
            (stackFrameIterate step current (step state)).machine operator condition right = true := by
        intro current hcurrent
        simpa [stackFrameIterate] using
          hcondition (current + 1) (by omega)
      have hbody' : ∀ current extra, current < iterations →
          evalStackFrameFuel (extra + stepFuel)
            (stackFrameIterate step current (step state)) body =
            some (.normal (stackFrameIterate step (current + 1) (step state))) := by
        intro current extra hcurrent
        simpa [stackFrameIterate, Nat.add_assoc] using
          hbody (current + 1) extra (by omega)
      have hrest := ih (state := step state) hcondition' hbody' hfinal
      simpa [stackFrameIterate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hloop.trans hrest

theorem evalStackFrameFuel_stackGcMoveList_iterate [NeZero width]
    (config : StackGcConfig) (fuel stepFuel iterations : Nat)
    (state : StackFrameMachineState width)
    (step : StackFrameMachineState width → StackFrameMachineState width)
    (hcondition : ∀ current, current < iterations →
      stackMachineCondition
        (stackFrameIterate step current state).machine .notEqual 7 (.imm 0) = true)
    (hbody : ∀ current extra, current < iterations →
      evalStackFrameFuel (extra + stepFuel)
        (stackFrameIterate step current state)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8]) =
        some (.normal (stackFrameIterate step (current + 1) state)))
    (hfinal :
      stackMachineCondition
        (stackFrameIterate step iterations state).machine .notEqual 7 (.imm 0) = false) :
    evalStackFrameFuel (fuel + iterations + stepFuel + 3) state
        (stackGcMoveListCode config) =
      some (.normal (stackFrameIterate step iterations state)) := by
  simpa [stackGcMoveListCode, stackGcWhile] using
    (evalStackFrameFuel_loop_iterate fuel stepFuel iterations state
      .notEqual 7 (.imm 0)
      (stackSeq [
        .inst (.mem .load 5 8),
        stackGcSubOne config 7,
        stackGcMoveCode config,
        .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) step hcondition hbody hfinal)

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

theorem evalStackFrameFuel_stackGcMoveList_immediate_one_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory address)
    (hnat : memory address % 2 = 0)
    (hbit : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 19) state
        (stackGcMoveListCode config)) 5 =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory address) := by
  have heval := evalStackFrameFuel_stackGcMoveList_immediate_one config fuel
    state hscratch5 hscratch7 hscratch8 hone hdomain hbit
  have hmemory' :
      (state.machine.memory (BitVec.ofNat width address)).toNat =
        memory address := by
    simpa [haddress] using hmemory
  rw [stackGcNatMoveList_immediate_one config address index destination
    oldBase memory domain hnat]
  simp [stackFrameNormalRegisterNat, heval,
    stackGcMoveListImmediateState, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, haddress, hmemory', hnat, hscratch5,
    Ne.symm hscratch5]

theorem evalStackFrameFuel_stackGcMoveList_immediate_one_scan_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (hbit : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0)
    (hbound : address + config.bytesInWord < 2 ^ width) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 19) state
        (stackGcMoveListCode config)) 8 =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).nextScan) := by
  have heval := evalStackFrameFuel_stackGcMoveList_immediate_one config fuel
    state hscratch5 hscratch7 hscratch8 hone hdomain hbit
  have hscan := stackGcNatMoveList_nextScan config 1 address index
    destination oldBase memory domain
  have hbytes : config.bytesInWord < 2 ^ width := by omega
  rw [hscan]
  simp [stackFrameNormalRegisterNat, heval,
    stackGcMoveListImmediateState, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, haddress, hbytes, hbound,
    BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
    hscratch8, Ne.symm hscratch8]

theorem evalStackFrameFuel_stackGcMoveList_immediate_one_count_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (hbit : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 19) state
        (stackGcMoveListCode config)) 7 = some 0 := by
  have heval := evalStackFrameFuel_stackGcMoveList_immediate_one config fuel
    state hscratch5 hscratch7 hscratch8 hone hdomain hbit
  simp [stackFrameNormalRegisterNat, heval,
    stackGcMoveListImmediateState, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, hone, haddress, hscratch7, Ne.symm hscratch7]

theorem evalStackFrameFuel_stackGcMoveList_immediate_one_memory_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (hmemory : (state.machine.memory (state.machine.registers 8)).toNat =
      memory address)
    (hnat : memory address % 2 = 0)
    (hbit : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0) :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel (fuel + 19) state
        (stackGcMoveListCode config)) address =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory address) := by
  have heval := evalStackFrameFuel_stackGcMoveList_immediate_one config fuel
    state hscratch5 hscratch7 hscratch8 hone hdomain hbit
  have hmemory' :
      (state.machine.memory (BitVec.ofNat width address)).toNat =
        memory address := by
    simpa [haddress] using hmemory
  have hmemoryBound : memory address < 2 ^ width := by
    rw [← hmemory']
    exact (state.machine.memory (BitVec.ofNat width address)).isLt
  have hmemWord :
      state.machine.memory (BitVec.ofNat width address) =
        BitVec.ofNat width (memory address) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmemoryBound] using
      hmemory'
  have hscratch5' : ¬ (5 = config.immediateScratch) := Ne.symm hscratch5
  rw [stackGcNatMoveList_immediate_one config address index destination
    oldBase memory domain hnat]
  simp [stackFrameNormalMemoryNat, heval,
    stackGcMoveListImmediateState, stackFrameWriteRegister,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, haddress, hmemWord, hscratch5, hscratch8,
    hscratch5', Ne.symm hscratch5, Ne.symm hscratch8,
    Nat.mod_eq_of_lt hmemoryBound]

theorem evalStackFrameFuel_stackGcMoveList_immediate_one_memory_relation
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (haddressBound : address < 2 ^ width)
    (hmemory : ∀ current, current < 2 ^ width →
      (state.machine.memory (BitVec.ofNat width current)).toNat =
        memory current)
    (hnat : memory address % 2 = 0)
    (hbit : state.machine.memory (state.machine.registers 8) &&&
      BitVec.ofNat width 1 = 0)
    (target : Nat) (htarget : target < 2 ^ width) :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel (fuel + 19) state
        (stackGcMoveListCode config)) target =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory target) := by
  have hmemoryAddress := hmemory address haddressBound
  have heval := evalStackFrameFuel_stackGcMoveList_immediate_one config fuel
    state hscratch5 hscratch7 hscratch8 hone hdomain hbit
  rw [heval]
  rw [stackGcNatMoveList_immediate_one config address index destination
    oldBase memory domain hnat]
  by_cases htargetAddress : target = address
  · subst target
    simp [stackFrameNormalMemoryNat, stackGcMoveListImmediateState,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, wordStackMachineBinOp, haddress,
      hmemoryAddress, hscratch5, hscratch8, Ne.symm hscratch5,
      Ne.symm hscratch8]
  · have htargetWord : BitVec.ofNat width target ≠
        state.machine.registers 8 := by
      rw [haddress]
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    have htargetOfNat : BitVec.ofNat width target ≠
        BitVec.ofNat width address := by
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    simp [stackFrameNormalMemoryNat, stackGcMoveListImmediateState,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, wordStackMachineBinOp, haddress,
      htargetWord, htargetOfNat, htargetAddress, hmemory target htarget,
      hscratch5, hscratch8, Ne.symm hscratch5, Ne.symm hscratch8]

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

theorem evalStackFrameFuel_stackGcMoveList_forwarding_one_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hmemory : (state.machine.memory (state.machine.registers 8)).toNat =
      memory address)
    (hloaded : (state.machine.memory (state.machine.registers 8)).toNat = value)
    (hvalue : value % 2 ≠ 0)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ pointer,
      (stackGcMoveListAfterCount config state).memoryDomain pointer = true)
    (hforward :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 = 0)
    (hstoreDomain :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveForwardingState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true)
    (hforwardNat :
      stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hforwardValue :
      (stackGcMachineForwardingValue config
        (stackGcMoveListAfterCount config state)).toNat =
        stackGcNatUpdateAddress config
          (memory (stackGcNatPointerAddress config oldBase value) / 4) value) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 40) state
        (stackGcMoveListCode config)) 5 =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory address) := by
  have hloadedNat : memory address = value := hmemory.symm.trans hloaded
  have hnat := stackGcNatMoveList_forwarding_one config address value index
    destination oldBase memory domain hvalue hforwardNat hloadedNat
  have heval := evalStackFrameFuel_stackGcMoveList_forwarding_one config fuel
    state hscratch0 hscratch1 hscratch5 hscratch7 hscratch8 hone hdomain hodd
    hheaderDomain hforward hstoreDomain
  have hafterMove5 :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).machine.registers 5 =
        stackGcMachineForwardingValue config
          (stackGcMoveListAfterCount config state) := by
    simp [stackGcMoveForwardingState, stackGcMoveForwardingSuffixState,
      stackGcMoveAddressState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp,
      wordStackMachineShift, stackGcMachineForwardingValue,
      stackGcMachineMoveAddress,
      hscratch0, hscratch1, hscratch5, Ne.symm hscratch0,
      Ne.symm hscratch1, Ne.symm hscratch5]
  have hfinal5 :
      (stackGcMoveListForwardingState config state).machine.registers 5 =
        (stackGcMoveForwardingState config
          (stackGcMoveListAfterCount config state)).machine.registers 5 := by
    simp [stackGcMoveListForwardingState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hscratch5, hscratch8, Ne.symm hscratch5, Ne.symm hscratch8]
  rw [hnat]
  rw [heval]
  simp only [stackFrameNormalRegisterNat, if_pos rfl]
  congr 1
  rw [hfinal5, hafterMove5, hforwardValue]
  simp

theorem evalStackFrameFuel_stackGcMoveList_forwarding_one_memory_relation
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (haddressBound : address < 2 ^ width)
    (hmemory : ∀ current, current < 2 ^ width →
      (state.machine.memory (BitVec.ofNat width current)).toNat =
        memory current)
    (hloadedNat : memory address = value)
    (hvalue : value % 2 ≠ 0)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ pointer,
      (stackGcMoveListAfterCount config state).memoryDomain pointer = true)
    (hforward :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 = 0)
    (hstoreDomain :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveForwardingState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true)
    (hforwardNat :
      stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hforwardValue :
      (stackGcMachineForwardingValue config
        (stackGcMoveListAfterCount config state)).toNat =
        stackGcNatUpdateAddress config
          (memory (stackGcNatPointerAddress config oldBase value) / 4) value)
    (target : Nat) (htarget : target < 2 ^ width) :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel (fuel + 40) state
        (stackGcMoveListCode config)) target =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory target) := by
  have hmemoryAddress := hmemory address haddressBound
  have hmemoryReg8 :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory address := by
    simpa [haddress] using hmemoryAddress
  have hloaded :
      (state.machine.memory (state.machine.registers 8)).toNat = value := by
    exact hmemoryReg8.trans hloadedNat
  have hnat := stackGcNatMoveList_forwarding_one config address value index
    destination oldBase memory domain hvalue hforwardNat hloadedNat
  have heval := evalStackFrameFuel_stackGcMoveList_forwarding_one config fuel
    state hscratch0 hscratch1 hscratch5 hscratch7 hscratch8 hone hdomain hodd
    hheaderDomain hforward hstoreDomain
  have hfinalValue :=
    evalStackFrameFuel_stackGcMoveList_forwarding_one_matches_nat config fuel
      state address value index destination oldBase memory domain hscratch0
      hscratch1 hscratch5 hscratch7 hscratch8 hone hdomain hmemoryReg8 hloaded
      hvalue hodd hheaderDomain hforward hstoreDomain hforwardNat hforwardValue
  have hafterMove5 :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).machine.registers 5 =
        stackGcMachineForwardingValue config
          (stackGcMoveListAfterCount config state) := by
    simp [stackGcMoveForwardingState, stackGcMoveForwardingSuffixState,
      stackGcMoveAddressState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp,
      wordStackMachineShift, stackGcMachineForwardingValue,
      stackGcMachineMoveAddress,
      hscratch0, hscratch1, hscratch5, Ne.symm hscratch0,
      Ne.symm hscratch1, Ne.symm hscratch5]
  have hfinal5 :
      (stackGcMoveListForwardingState config state).machine.registers 5 =
        (stackGcMoveForwardingState config
          (stackGcMoveListAfterCount config state)).machine.registers 5 := by
    simp [stackGcMoveListForwardingState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hscratch5, hscratch8, Ne.symm hscratch5, Ne.symm hscratch8]
  have hafterMove8 :
      (stackGcMoveForwardingState config
        (stackGcMoveListAfterCount config state)).machine.registers 8 =
        state.machine.registers 8 := by
    simp [stackGcMoveForwardingState, stackGcMoveForwardingSuffixState,
      stackGcMoveAddressState, stackGcMoveListAfterCount,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, wordStackMachineShift,
      hscratch0, hscratch1, hscratch5, hscratch7, hscratch8,
      Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch5,
      Ne.symm hscratch7, Ne.symm hscratch8]
  have hfinalMemory :
      (stackGcMoveListForwardingState config state).machine.memory
          (BitVec.ofNat width address) =
        (stackGcMoveListForwardingState config state).machine.registers 5 := by
    simp [stackGcMoveListForwardingState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      haddress, hscratch0, hscratch1, hscratch5, hscratch7, hscratch8,
      hafterMove8,
      Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch5,
      Ne.symm hscratch7, Ne.symm hscratch8]
  rw [heval, hnat]
  by_cases htargetAddress : target = address
  · subst target
    simp only [stackFrameNormalMemoryNat, if_pos rfl]
    rw [hfinalMemory, hfinal5, hafterMove5, hforwardValue]
    simp
  · have htargetWord : BitVec.ofNat width target ≠
        state.machine.registers 8 := by
      rw [haddress]
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    have htargetOfNat : BitVec.ofNat width target ≠
        BitVec.ofNat width address := by
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    simp [stackFrameNormalMemoryNat, stackGcMoveListForwardingState,
      stackGcMoveForwardingState, stackGcMoveForwardingSuffixState,
      stackGcMoveAddressState, stackGcMoveListAfterCount,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, wordStackMachineBinOp,
      haddress, htargetWord, htargetOfNat, htargetAddress,
      hmemory target htarget, hscratch0, hscratch1, hscratch5,
      hscratch7, hscratch8, Ne.symm hscratch0, Ne.symm hscratch1,
      Ne.symm hscratch5, Ne.symm hscratch7, Ne.symm hscratch8]

def stackGcMoveListCopyState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterCount := stackGcMoveListAfterCount config state
  let afterMove := stackGcMoveCopyState config afterCount
  let afterStore := { afterMove with machine :=
    (wordStackMachineWriteMemory afterMove.machine
      (afterMove.machine.registers 8) (afterMove.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))

theorem evalStackFrameFuel_stackGcMoveList_copy_one [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hscratch4 : config.immediateScratch ≠ 4)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch6 : config.immediateScratch ≠ 6)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ address,
      (stackGcMoveListAfterCount config state).memoryDomain address = true)
    (hheaderLength :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) >>>
        shiftAmount (BitVec.ofNat width
          (config.wordBits - config.lenSize)) = 0)
    (hnotforwarding :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 ≠ 0)
    (hstoreDomain :
      (stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveCopyState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true) :
    evalStackFrameFuel (fuel + 46) state (stackGcMoveListCode config) =
      some (.normal (stackGcMoveListCopyState config state)) := by
  let afterLoad := stackFrameWriteRegister state 5
    (state.machine.memory (state.machine.registers 8))
  let afterCount := stackGcMoveListAfterCount config state
  let afterMove := stackGcMoveCopyState config afterCount
  let afterStore := { afterMove with machine :=
    (wordStackMachineWriteMemory afterMove.machine
      (afterMove.machine.registers 8) (afterMove.machine.registers 5)) }
  let afterScratch := stackFrameWriteRegister afterStore
    config.immediateScratch (BitVec.ofNat width config.bytesInWord)
  let afterFinal := stackFrameWriteRegister afterScratch 8
    (wordStackMachineBinOp .add (afterScratch.machine.registers 8)
      (BitVec.ofNat width config.bytesInWord))
  have hsub : evalStackFrameFuel (fuel + 42) afterLoad
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
  have hmove := evalStackFrameFuel_stackGcMoveCode_copy_one_fuel config
    (fuel + 12) afterCount hscratch0 hscratch1 hscratch2 hscratch3 hscratch4
      hscratch5 hscratch6 hodd' hheaderDomain hheaderLength hnotforwarding
  have hstore := evalStackFrameFuel_memStore (fuel + 39) afterMove 5 8
    hstoreDomain
  have hadd : evalStackFrameFuel (fuel + 40) afterStore
      (stackGcAddBytes config 8) = some (.normal afterFinal) := by
    simp [stackGcAddBytes, stackGcAddImmediate, stackGcConst, stackGcAdd,
      stackSeq, evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, afterFinal, afterScratch, afterStore,
      hscratch8, Ne.symm hscratch8]
  have hload := evalStackFrameFuel_memLoad (fuel + 43) state 5 8 hdomain
  have hbody : evalStackFrameFuel (fuel + 44) state
      (stackSeq [
        .inst (.mem .load 5 8),
        stackGcSubOne config 7,
        stackGcMoveCode config,
        .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) = some (.normal afterFinal) := by
    change evalStackFrameFuel (fuel + 44) state
      (.seq (.inst (.mem .load 5 8))
        (stackSeq [stackGcSubOne config 7, stackGcMoveCode config,
          .inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 43) state afterLoad
      (.inst (.mem .load 5 8))
      (stackSeq [stackGcSubOne config 7, stackGcMoveCode config,
        .inst (.mem .store 5 8), stackGcAddBytes config 8]) hload]
    change evalStackFrameFuel (fuel + 43) afterLoad
      (.seq (stackGcSubOne config 7)
        (stackSeq [stackGcMoveCode config,
          .inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 42) afterLoad afterCount
      (stackGcSubOne config 7)
      (stackSeq [stackGcMoveCode config, .inst (.mem .store 5 8),
        stackGcAddBytes config 8]) hsub]
    have hmove' : evalStackFrameFuel (fuel + 41) afterCount
        (stackGcMoveCode config) = some (.normal afterMove) := by
      simpa [afterMove, Nat.add_assoc] using hmove
    change evalStackFrameFuel (fuel + 42) afterCount
      (.seq (stackGcMoveCode config)
        (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8])) =
      some (.normal afterFinal)
    rw [evalStackFrameFuel_seq_normal (fuel + 41) afterCount afterMove
      (stackGcMoveCode config)
      (stackSeq [.inst (.mem .store 5 8), stackGcAddBytes config 8]) hmove']
    change evalStackFrameFuel (fuel + 41) afterMove
      (.seq (.inst (.mem .store 5 8)) (stackGcAddBytes config 8)) =
      some (.normal afterFinal)
    have hstore' : evalStackFrameFuel (fuel + 40) afterMove
        (.inst (.mem .store 5 8)) = some (.normal afterStore) := by
      simpa [afterStore, Nat.add_assoc] using hstore
    rw [evalStackFrameFuel_seq_normal (fuel + 40) afterMove afterStore
      (.inst (.mem .store 5 8)) (stackGcAddBytes config 8) hstore']
    simpa [Nat.add_assoc] using hadd
  have hcondition :
      stackMachineCondition state.machine .notEqual 7 (.imm 0) = true := by
    simp [stackMachineCondition, hone, NeZero.ne width]
  have haddress7 (source : StackFrameMachineState width) :
      (stackGcMoveAddressState config source).machine.registers 7 =
        source.machine.registers 7 := by
    simp [stackGcMoveAddressState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, hscratch0, hscratch1,
      hscratch7, Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch7]
  have hprefix7 (source : StackFrameMachineState width) :
      (stackGcMoveCopyPrefixState config source).machine.registers 7 =
        source.machine.registers 7 := by
    simp [stackGcMoveCopyPrefixState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, hscratch0, hscratch1, hscratch2,
      hscratch6, hscratch7, Ne.symm hscratch0, Ne.symm hscratch1,
      Ne.symm hscratch2, Ne.symm hscratch6, Ne.symm hscratch7]
  have hsuffix7 (source : StackFrameMachineState width) :
      (stackGcMoveCopySuffixState config source).machine.registers 7 =
        source.machine.registers 7 := by
    simp [stackGcMoveCopySuffixState, stackFrameMemcpyStep,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, hscratch0, hscratch1, hscratch2,
      hscratch3, hscratch4, hscratch5, hscratch6, hscratch7,
      Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch2,
      Ne.symm hscratch3, Ne.symm hscratch4, Ne.symm hscratch5,
      Ne.symm hscratch6, Ne.symm hscratch7]
  have hcount7 : afterCount.machine.registers 7 = BitVec.ofNat width 0 := by
    simp [afterCount, stackGcMoveListAfterCount, afterLoad,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, hone, hscratch7, Ne.symm hscratch7]
  have hmove7 : afterMove.machine.registers 7 = afterCount.machine.registers 7 := by
    simp only [afterMove, stackGcMoveCopyState]
    rw [hsuffix7, hprefix7, haddress7]
  have hfinal7 : afterFinal.machine.registers 7 = afterMove.machine.registers 7 := by
    simp [afterFinal, afterScratch, afterStore, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, hscratch7, hscratch8,
      Ne.symm hscratch7, Ne.symm hscratch8]
  have hcondition' :
      stackMachineCondition afterFinal.machine .notEqual 7 (.imm 0) = false := by
    simp [stackMachineCondition, hfinal7, hmove7, hcount7, hone,
      NeZero.ne width]
  have hite : evalStackFrameFuel (fuel + 45) state
      (.ite .notEqual 7 (.imm 0)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8])
        (.break 0)) = some (.normal afterFinal) := by
    rw [evalStackFrameFuel_ite_true (fuel + 44) state .notEqual 7 (.imm 0)
      _ (.break 0) hcondition]
    exact hbody
  have hdone : evalStackFrameFuel (fuel + 45) afterFinal
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
    evalStackFrameFuel (fuel + 46) state (stackGcMoveListCode config) =
        evalStackFrameFuel (fuel + 46) state
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by rfl
    _ = evalStackFrameFuel (fuel + 45) afterFinal
          (.loop (.ite .notEqual 7 (.imm 0)
            (stackSeq [
              .inst (.mem .load 5 8),
              stackGcSubOne config 7,
              stackGcMoveCode config,
              .inst (.mem .store 5 8),
              stackGcAddBytes config 8])
            (.break 0))) := by
      exact evalStackFrameFuel_loop_normal (fuel + 45) state afterFinal
        (.ite .notEqual 7 (.imm 0)
          (stackSeq [
            .inst (.mem .load 5 8),
            stackGcSubOne config 7,
            stackGcMoveCode config,
            .inst (.mem .store 5 8),
            stackGcAddBytes config 8])
          (.break 0)) hite
    _ = some (.normal (stackGcMoveListCopyState config state)) := by
      simpa [stackGcMoveListCopyState, afterFinal, afterScratch,
        afterStore, afterMove, afterCount] using hdone

theorem evalStackFrameFuel_stackGcMoveList_copy_one_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hscratch4 : config.immediateScratch ≠ 4)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch6 : config.immediateScratch ≠ 6)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hmemory : (state.machine.memory (state.machine.registers 8)).toNat =
      memory address)
    (hloaded : (state.machine.memory (state.machine.registers 8)).toNat = value)
    (hvalue : value % 2 ≠ 0)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ pointer,
      (stackGcMoveListAfterCount config state).memoryDomain pointer = true)
    (hheaderLength :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) >>>
        shiftAmount (BitVec.ofNat width
          (config.wordBits - config.lenSize)) = 0)
    (hnotforwarding :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 ≠ 0)
    (hstoreDomain :
      (stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveCopyState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hcopyValue :
      ((stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).machine.registers 5).toNat =
        stackGcNatUpdateAddress config index value) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 46) state
        (stackGcMoveListCode config)) 5 =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory address) := by
  have hloadedNat : memory address = value := hmemory.symm.trans hloaded
  have hnat := stackGcNatMoveList_copy_one config address value index
    destination oldBase memory domain hvalue hnonforward hloadedNat
  have heval := evalStackFrameFuel_stackGcMoveList_copy_one config fuel state
    hscratch0 hscratch1 hscratch2 hscratch3 hscratch4 hscratch5 hscratch6
    hscratch7 hscratch8 hone hdomain hodd hheaderDomain hheaderLength
    hnotforwarding hstoreDomain
  have hfinal5 :
      (stackGcMoveListCopyState config state).machine.registers 5 =
        (stackGcMoveCopyState config
          (stackGcMoveListAfterCount config state)).machine.registers 5 := by
    simp [stackGcMoveListCopyState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hscratch5, hscratch8, Ne.symm hscratch5, Ne.symm hscratch8]
  rw [hnat]
  rw [heval]
  simp only [stackFrameNormalRegisterNat, if_pos rfl]
  congr 1
  rw [hfinal5, hcopyValue]
  simp

theorem evalStackFrameFuel_stackGcMoveList_copy_one_memory_relation
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hscratch4 : config.immediateScratch ≠ 4)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch6 : config.immediateScratch ≠ 6)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hone : state.machine.registers 7 = BitVec.ofNat width 1)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width address)
    (haddressBound : address < 2 ^ width)
    (hmemory : ∀ current, current < 2 ^ width →
      (state.machine.memory (BitVec.ofNat width current)).toNat =
        memory current)
    (hloadedNat : memory address = value)
    (hvalue : value % 2 ≠ 0)
    (hodd :
      (stackGcMoveListAfterCount config state).machine.registers 5 &&&
        BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ pointer,
      (stackGcMoveListAfterCount config state).memoryDomain pointer = true)
    (hheaderLength :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) >>>
        shiftAmount (BitVec.ofNat width
          (config.wordBits - config.lenSize)) = 0)
    (hnotforwarding :
      (stackGcMoveListAfterCount config state).machine.memory
          (stackGcMachineMoveAddress config
            (stackGcMoveListAfterCount config state)) &&&
        BitVec.ofNat width 3 ≠ 0)
    (hstoreDomain :
      (stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).memoryDomain
          ((stackGcMoveCopyState config
            (stackGcMoveListAfterCount config state)).machine.registers 8) = true)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hcopyValue :
      ((stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).machine.registers 5).toNat =
        stackGcNatUpdateAddress config index value)
    (hcopyMemory : ∀ target, target < 2 ^ width → target ≠ address →
      ((stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).machine.memory
          (BitVec.ofNat width target)).toNat =
        (stackGcNatMoveList config 1 address index destination oldBase
          memory domain).memory target)
    (target : Nat) (htarget : target < 2 ^ width) :
    stackFrameNormalMemoryNat
      (evalStackFrameFuel (fuel + 46) state
        (stackGcMoveListCode config)) target =
      some ((stackGcNatMoveList config 1 address index destination oldBase
        memory domain).memory target) := by
  have hmemoryAddress := hmemory address haddressBound
  have hmemoryReg8 :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory address := by
    simpa [haddress] using hmemoryAddress
  have hloaded :
      (state.machine.memory (state.machine.registers 8)).toNat = value := by
    exact hmemoryReg8.trans hloadedNat
  have hnat := stackGcNatMoveList_copy_one config address value index
    destination oldBase memory domain hvalue hnonforward hloadedNat
  have heval := evalStackFrameFuel_stackGcMoveList_copy_one config fuel state
    hscratch0 hscratch1 hscratch2 hscratch3 hscratch4 hscratch5 hscratch6
    hscratch7 hscratch8 hone hdomain hodd hheaderDomain hheaderLength
    hnotforwarding hstoreDomain
  have hfinal5 :
      (stackGcMoveListCopyState config state).machine.registers 5 =
        (stackGcMoveCopyState config
          (stackGcMoveListAfterCount config state)).machine.registers 5 := by
    simp [stackGcMoveListCopyState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hscratch5, hscratch8, Ne.symm hscratch5, Ne.symm hscratch8]
  have hafterMove8 :
      (stackGcMoveCopyState config
        (stackGcMoveListAfterCount config state)).machine.registers 8 =
        state.machine.registers 8 := by
    have haddress8 (source : StackFrameMachineState width) :
        (stackGcMoveAddressState config source).machine.registers 8 =
          source.machine.registers 8 := by
      simp [stackGcMoveAddressState, stackFrameWriteRegister,
        wordStackMachineWriteRegister, hscratch0, hscratch1,
        hscratch7, hscratch8, Ne.symm hscratch0, Ne.symm hscratch1,
        Ne.symm hscratch7, Ne.symm hscratch8]
    have hprefix8 (source : StackFrameMachineState width) :
        (stackGcMoveCopyPrefixState config source).machine.registers 8 =
          source.machine.registers 8 := by
      simp [stackGcMoveCopyPrefixState, stackFrameWriteRegister,
        wordStackMachineWriteRegister, hscratch0, hscratch1,
        hscratch2, hscratch6, hscratch7, hscratch8,
        Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch2,
        Ne.symm hscratch6, Ne.symm hscratch7, Ne.symm hscratch8]
    have hsuffix8 (source : StackFrameMachineState width) :
        (stackGcMoveCopySuffixState config source).machine.registers 8 =
          source.machine.registers 8 := by
      simp [stackGcMoveCopySuffixState, stackFrameMemcpyStep,
        stackFrameWriteRegister, wordStackMachineWriteRegister,
        wordStackMachineWriteMemory, hscratch0, hscratch1,
        hscratch2, hscratch3, hscratch4, hscratch5, hscratch6,
        hscratch7, hscratch8, Ne.symm hscratch0, Ne.symm hscratch1,
        Ne.symm hscratch2, Ne.symm hscratch3, Ne.symm hscratch4,
        Ne.symm hscratch5, Ne.symm hscratch6, Ne.symm hscratch7,
        Ne.symm hscratch8]
    have hcount8 :
        (stackGcMoveListAfterCount config state).machine.registers 8 =
          state.machine.registers 8 := by
      simp [stackGcMoveListAfterCount, stackFrameWriteRegister,
        wordStackMachineWriteRegister, hscratch0, hscratch5,
        hscratch7, hscratch8, Ne.symm hscratch0, Ne.symm hscratch5,
        Ne.symm hscratch7, Ne.symm hscratch8]
    simp only [stackGcMoveCopyState]
    rw [hsuffix8, hprefix8, haddress8]
    exact hcount8
  have hfinalMemory :
      (stackGcMoveListCopyState config state).machine.memory
          (BitVec.ofNat width address) =
        (stackGcMoveListCopyState config state).machine.registers 5 := by
    simp only [stackGcMoveListCopyState]
    simp only [stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      wordStackMachineBinOp, haddress, hafterMove8, hscratch0,
      hscratch1, hscratch2, hscratch3, hscratch4, hscratch5,
      hscratch6, hscratch7, hscratch8, Ne.symm hscratch0,
      Ne.symm hscratch1, Ne.symm hscratch2, Ne.symm hscratch3,
      Ne.symm hscratch4, Ne.symm hscratch5, Ne.symm hscratch6,
      Ne.symm hscratch7, Ne.symm hscratch8]
    simp only [if_pos rfl,
      if_neg (show (5 : Nat) ≠ 8 by decide),
      if_neg (show ¬ False by decide)]
    rfl
  rw [heval]
  by_cases htargetAddress : target = address
  · subst target
    rw [hnat]
    simp only [stackFrameNormalMemoryNat, if_pos rfl]
    rw [hfinalMemory, hfinal5, hcopyValue]
    simp
  · have htargetWord : BitVec.ofNat width target ≠
        state.machine.registers 8 := by
      rw [haddress]
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    have htargetOfNat : BitVec.ofNat width target ≠
        BitVec.ofNat width address := by
      intro heq
      have hto := congrArg BitVec.toNat heq
      apply htargetAddress
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htarget,
        Nat.mod_eq_of_lt haddressBound] using hto
    have hcopy := hcopyMemory target htarget htargetAddress
    simp only [stackFrameNormalMemoryNat, stackGcMoveListCopyState,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, wordStackMachineBinOp,
      haddress, hafterMove8, htargetWord, htargetAddress, hcopy,
      hscratch0, hscratch1, hscratch2, hscratch3, hscratch4,
      hscratch5, hscratch6, hscratch7, hscratch8,
      Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch2,
      Ne.symm hscratch3, Ne.symm hscratch4, Ne.symm hscratch5,
      Ne.symm hscratch6, Ne.symm hscratch7, Ne.symm hscratch8]
    simp only [if_neg htargetOfNat]
    exact congrArg some hcopy

theorem stackGcMoveLoop_machine_condition_matches_nat [NeZero width]
    (state : StackFrameMachineState width) (scan destination : Nat)
    (hscanBound : scan < 2 ^ width)
    (hdestinationBound : destination < 2 ^ width)
    (hscan : state.machine.registers 8 = BitVec.ofNat width scan)
    (hdestination : state.machine.registers 3 = BitVec.ofNat width destination) :
    stackMachineCondition state.machine .notEqual 3 (.reg 8) = true ↔
      scan ≠ destination := by
  have hwordEq :
      BitVec.ofNat width destination = BitVec.ofNat width scan ↔
        destination = scan := by
    constructor
    · intro h
      have hto := congrArg BitVec.toNat h
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscanBound,
        Nat.mod_eq_of_lt hdestinationBound] using hto
    · intro h
      simpa [h]
  simp [stackMachineCondition, hscan, hdestination, hwordEq]
  omega

private theorem natLandFour_eq_zero_iff_testBit_two_false (value : Nat) :
    value &&& 4 = 0 ↔ value.testBit 2 = false := by
  constructor
  · intro hzero
    cases hbit : value.testBit 2 with
    | false => simpa [hbit]
    | true =>
        have hmask : (4 : Nat).testBit 2 = true := by decide
        have hand : (value &&& 4).testBit 2 = true := by
          rw [Nat.testBit_and, hbit, hmask]
          decide
        simp [hzero] at hand
  · intro hbit
    have hall : ∀ index, (value &&& 4).testBit index = false := by
      intro index
      rw [Nat.testBit_and]
      by_cases hindex : index = 2
      · simp [hindex, hbit]
      · have hmask : (4 : Nat).testBit index = false := by
          have hpow : (4 : Nat) = 2 ^ 2 := by decide
          simpa [hpow] using
            (Nat.testBit_two_pow_of_ne (Ne.symm hindex))
        simp [hmask]
    by_cases hzero : value &&& 4 = 0
    · exact hzero
    · obtain ⟨index, hindex⟩ := Nat.exists_testBit_of_ne_zero hzero
      have hfalse := hall index
      simp [hindex] at hfalse

theorem stackGcNatHeaderHasCode_iff_testBit_two (header : Nat) :
    stackGcNatHeaderHasCode header = true ↔ header.testBit 2 = true := by
  unfold stackGcNatHeaderHasCode
  simp only [decide_eq_true_eq]
  rw [Nat.mod_two_eq_one_iff_testBit_zero]
  rw [show (4 : Nat) = 2 ^ 2 by decide]
  rw [Nat.testBit_div_two_pow]

theorem stackGcMachineHeaderCondition_matches_nat [NeZero width]
    (header : Word width) (hwidth : 3 ≤ width) :
    (header &&& BitVec.ofNat width 4 == 0) = true ↔
      stackGcNatHeaderHasCode header.toNat ≠ true := by
  have hmask : (BitVec.ofNat width 4).toNat = 4 := by
    simp [BitVec.toNat_ofNat]
    have hpow : 2 ^ 3 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) hwidth
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (by decide) hpow)
  have htest :
      (header &&& BitVec.ofNat width 4 == 0) = true ↔
        header.toNat.testBit 2 = false := by
    constructor
    · intro h
      have hzero : header &&& BitVec.ofNat width 4 = 0 := by
        simpa using h
      have hzero' := congrArg BitVec.toNat hzero
      apply (natLandFour_eq_zero_iff_testBit_two_false header.toNat).mp
      simpa [BitVec.toNat_and, hmask] using hzero'
    · intro h
      have hzero' :=
        (natLandFour_eq_zero_iff_testBit_two_false header.toNat).mpr h
      have hzero : header &&& BitVec.ofNat width 4 = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.toNat_and, hmask] using hzero'
      simpa [hzero]
  have hcode := stackGcNatHeaderHasCode_iff_testBit_two header.toNat
  have hcodeData :
      stackGcNatHeaderHasCode header.toNat ≠ true ↔
        header.toNat.testBit 2 = false := by
    have hneq := not_congr hcode
    simpa only [Bool.eq_false_iff] using hneq
  exact htest.trans hcodeData.symm

theorem stackGcMoveLoop_header_condition_matches_nat [NeZero width]
    (state : StackFrameMachineState width) (scan : Nat)
    (memory : Nat → Nat) (hwidth : 3 ≤ width)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan) :
    stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = true ↔
      stackGcNatHeaderHasCode (memory scan) ≠ true := by
  have hmemoryAt :
      (state.machine.memory (BitVec.ofNat width scan)).toNat =
        memory scan := by
    simpa [haddress] using hmemory
  have hbound : memory scan < 2 ^ width := by
    rw [← hmemoryAt]
    exact (state.machine.memory (BitVec.ofNat width scan)).isLt
  have hword : state.machine.memory (BitVec.ofNat width scan) =
      BitVec.ofNat width (memory scan) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] using hmemoryAt
  have hheader := stackGcMachineHeaderCondition_matches_nat
    (state.machine.memory (BitVec.ofNat width scan)) hwidth
  simpa [stackMachineCondition, stackFrameWriteRegister,
    wordStackMachineWriteRegister, haddress, hword,
    Nat.mod_eq_of_lt hbound] using hheader

/-! One machine transition for the header/code branch of `word_gc_move_loop`.
The data branch delegates to the already established MoveList transition API;
this branch only advances the scan pointer and is therefore a useful first
composable step for the full loop simulation. -/

def stackGcMoveLoopCodeStepState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterLoad := stackFrameWriteRegister state 7
    (state.machine.memory (state.machine.registers 8))
  let afterLength := stackFrameWriteRegister afterLoad config.immediateScratch
    (BitVec.ofNat width (config.wordBits - config.lenSize))
  let afterShift := stackFrameWriteRegister afterLength 7
    (wordStackMachineShift .lsr (afterLoad.machine.registers 7)
      (afterLength.machine.registers config.immediateScratch))
  let afterOne := stackFrameWriteRegister afterShift config.immediateScratch
    (BitVec.ofNat width 1)
  let afterCount := stackFrameWriteRegister afterOne 7
    (wordStackMachineBinOp .add (afterShift.machine.registers 7)
      (afterOne.machine.registers config.immediateScratch))
  let afterWordShift := stackFrameWriteRegister afterCount config.immediateScratch
    (BitVec.ofNat width config.wordShift)
  let afterWord := stackFrameWriteRegister afterWordShift 7
    (wordStackMachineShift .lsl (afterCount.machine.registers 7)
      (afterWordShift.machine.registers config.immediateScratch))
  stackFrameWriteRegister afterWord 8
    (wordStackMachineBinOp .add (afterWord.machine.registers 8)
      (afterWord.machine.registers 7))

theorem stackGcMoveLoopCodeStepState_memory [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    (stackGcMoveLoopCodeStepState config state).machine.memory =
      state.machine.memory := by
  simp [stackGcMoveLoopCodeStepState, stackFrameWriteRegister,
    wordStackMachineWriteRegister]

def stackGcMachineMemoryMatchesNat [NeZero width]
    (state : StackFrameMachineState width) (memory : Nat → Nat) : Prop :=
  ∀ address, address < 2 ^ width →
    (state.machine.memory (BitVec.ofNat width address)).toNat =
      memory address

theorem stackGcMoveLoopCodeStepState_memory_matches_nat [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (memory : Nat → Nat)
    (hmemory : stackGcMachineMemoryMatchesNat state memory) :
    stackGcMachineMemoryMatchesNat
      (stackGcMoveLoopCodeStepState config state) memory := by
  intro address haddress
  rw [stackGcMoveLoopCodeStepState_memory]
  exact hmemory address haddress

def stackGcMachineScanMatchesNat [NeZero width]
    (state : StackFrameMachineState width) (scan : Nat) : Prop :=
  (state.machine.registers 8).toNat = scan

def stackGcMachineNatRelation [NeZero width]
    (state : StackFrameMachineState width) (scan : Nat)
    (memory : Nat → Nat) : Prop :=
  stackGcMachineScanMatchesNat state scan ∧
    stackGcMachineMemoryMatchesNat state memory

theorem evalStackFrameFuel_stackGcMoveLoop_code_step [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false) :
    evalStackFrameFuel (fuel + 12) state
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])]) =
      some (.normal (stackGcMoveLoopCodeStepState config state)) := by
  let afterLoad := stackFrameWriteRegister state 7
    (state.machine.memory (state.machine.registers 8))
  have hload := evalStackFrameFuel_memLoad (fuel + 11) state 7 8 hdomain
  have hdata :
      evalStackFrameFuel (fuel + 10) afterLoad
        (stackSeq [
          stackGcShiftImmediate config .lsr 7
            (config.wordBits - config.lenSize),
          stackGcAddOne config 7,
          stackGcShiftImmediate config .lsl 7 config.wordShift,
          stackGcAdd 8 7]) =
        some (.normal (stackGcMoveLoopCodeStepState config state)) := by
    simp [stackGcMoveLoopCodeStepState, afterLoad, stackSeq,
      evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
      stackFrameWriteRegister, stackGcShiftImmediate, stackGcAddImmediate,
      stackGcAddOne, stackGcConst, stackGcAdd, wordStackMachineWriteRegister,
      wordStackMachineBinOp, wordStackMachineShift, hscratch7, hscratch8,
      Ne.symm hscratch7, Ne.symm hscratch8]
  have hrest :
      evalStackFrameFuel (fuel + 11) afterLoad
        (.ite .test 7 (.imm 4)
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddBytes config 8,
            stackGcMoveListCode config])
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddOne config 7,
            stackGcShiftImmediate config .lsl 7 config.wordShift,
            stackGcAdd 8 7])) =
        some (.normal (stackGcMoveLoopCodeStepState config state)) := by
    rw [evalStackFrameFuel_ite_false (fuel + 10) afterLoad
      .test 7 (.imm 4)
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddBytes config 8,
        stackGcMoveListCode config])
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddOne config 7,
        stackGcShiftImmediate config .lsl 7 config.wordShift,
        stackGcAdd 8 7]) hcode]
    exact hdata
  have hseq := evalStackFrameFuel_seq_normal (fuel + 11) state afterLoad
    (.inst (.mem .load 7 8))
    (.ite .test 7 (.imm 4)
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddBytes config 8,
        stackGcMoveListCode config])
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddOne config 7,
        stackGcShiftImmediate config .lsl 7 config.wordShift,
        stackGcAdd 8 7])) hload
  rw [hrest] at hseq
  simpa [stackSeq, afterLoad] using hseq

def stackGcMoveLoopCodePrefixState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let afterLength := stackFrameWriteRegister state config.immediateScratch
    (BitVec.ofNat width (config.wordBits - config.lenSize))
  let afterShift := stackFrameWriteRegister afterLength 7
    (wordStackMachineShift .lsr (state.machine.registers 7)
      (afterLength.machine.registers config.immediateScratch))
  let afterBytes := stackFrameWriteRegister afterShift config.immediateScratch
    (BitVec.ofNat width config.bytesInWord)
  stackFrameWriteRegister afterBytes 8
    (wordStackMachineBinOp .add (afterBytes.machine.registers 8)
      (afterBytes.machine.registers config.immediateScratch))

theorem evalStackFrameFuel_stackGcMoveLoop_code_prefix [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8) :
    evalStackFrameFuel (fuel + 10) state
        (stackSeq [
          stackGcShiftImmediate config .lsr 7
            (config.wordBits - config.lenSize),
          stackGcAddBytes config 8]) =
      some (.normal (stackGcMoveLoopCodePrefixState config state)) := by
  simp [stackGcMoveLoopCodePrefixState, stackSeq, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackFrameBasic, stackFrameWriteRegister,
    stackGcShiftImmediate, stackGcAddImmediate, stackGcAddBytes,
    stackGcConst, stackGcAdd, wordStackMachineWriteRegister,
    wordStackMachineBinOp, wordStackMachineShift, hscratch7, hscratch8,
    Ne.symm hscratch7, Ne.symm hscratch8]

theorem evalStackFrameFuel_stackGcMoveLoop_code_step_scan_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width (config.wordBits - config.lenSize))) +
        BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 12) state
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])])) 8 =
      some (scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord) := by
  have heval := evalStackFrameFuel_stackGcMoveLoop_code_step config fuel
    state hscratch7 hscratch8 hdomain hcode
  have hscanBound : scan < 2 ^ width := by omega
  have hmemory' :
      (state.machine.memory (BitVec.ofNat width scan)).toNat =
        memory scan := by
    simpa [haddress] using hmemory
  have hmemoryBound : memory scan < 2 ^ width := by
    rw [← hmemory']
    exact (state.machine.memory (BitVec.ofNat width scan)).isLt
  have hmemWord :
      state.machine.memory (BitVec.ofNat width scan) =
        BitVec.ofNat width (memory scan) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmemoryBound] using
      hmemory'
  have hcount' :
      (((BitVec.ofNat width (memory scan) >>>
          shiftAmount (BitVec.ofNat width (config.wordBits - config.lenSize))) +
        BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord := by
    simpa [haddress, hmemWord] using hcount
  rw [heval]
  simp only [stackFrameNormalRegisterNat]
  have hreg :
      (stackGcMoveLoopCodeStepState config state).machine.registers 8 =
        state.machine.registers 8 +
          (((state.machine.memory (state.machine.registers 8) >>>
              shiftAmount (BitVec.ofNat width
                (config.wordBits - config.lenSize))) +
            BitVec.ofNat width 1) <<<
              shiftAmount (BitVec.ofNat width config.wordShift)) := by
    simp [stackGcMoveLoopCodeStepState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp,
      wordStackMachineShift, hscratch8, Ne.symm hscratch8]
  rw [hreg, BitVec.toNat_add]
  rw [hcount]
  simp [haddress, hmemory', BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hscanBound, Nat.mod_eq_of_lt hadvance]

theorem stackGcMoveLoopCodeStepState_scan_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width
            (config.wordBits - config.lenSize))) + BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    stackGcMachineScanMatchesNat
      (stackGcMoveLoopCodeStepState config state)
      (scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord) := by
  have hresult := evalStackFrameFuel_stackGcMoveLoop_code_step_scan_matches_nat
    config fuel state scan memory domain hscratch7 hscratch8 hdomain
    haddress hmemory hcode hadvance hcount
  have heval := evalStackFrameFuel_stackGcMoveLoop_code_step config fuel
    state hscratch7 hscratch8 hdomain hcode
  rw [heval] at hresult
  simpa [stackGcMachineScanMatchesNat, stackFrameNormalRegisterNat] using
    hresult

theorem stackGcMoveLoopCodeStepState_preserves_nat_relation
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      stackGcMachineNatRelation state scan memory)
    (hmemoryAt :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width
            (config.wordBits - config.lenSize))) + BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    stackGcMachineNatRelation
      (stackGcMoveLoopCodeStepState config state)
      (scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord) memory := by
  rcases hmemory with ⟨_, hmemoryAll⟩
  constructor
  · exact stackGcMoveLoopCodeStepState_scan_matches_nat
      config fuel state scan memory domain hscratch7 hscratch8 hdomain
      haddress hmemoryAt hcode hadvance hcount
  · exact stackGcMoveLoopCodeStepState_memory_matches_nat
      config state memory hmemoryAll

theorem stackGcMoveLoopCodeStepState_preserves_nat_relation_of_memory
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (hwidth : 3 ≤ width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory : stackGcMachineNatRelation state scan memory)
    (hcodeNat : stackGcNatHeaderHasCode (memory scan) = true)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width
            (config.wordBits - config.lenSize))) +
        BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    stackGcMachineNatRelation
      (stackGcMoveLoopCodeStepState config state)
      (scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord) memory := by
  rcases hmemory with ⟨hscanMatches, hmemoryAll⟩
  have hscanBound : scan < 2 ^ width := by
    rw [← hscanMatches]
    exact (state.machine.registers 8).isLt
  have hmemoryAt :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan := by
    have h := hmemoryAll scan hscanBound
    simpa [haddress] using h
  have hcodeIff := stackGcMoveLoop_header_condition_matches_nat
    state scan memory hwidth haddress hmemoryAt
  have hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false := by
    apply (Bool.eq_false_iff).mpr
    intro htrue
    exact (hcodeIff.mp htrue) hcodeNat
  exact stackGcMoveLoopCodeStepState_preserves_nat_relation config fuel state
    scan memory domain hscratch7 hscratch8 hdomain haddress
    ⟨hscanMatches, hmemoryAll⟩ hmemoryAt hcode hadvance hcount

theorem evalStackFrameFuel_stackGcMoveLoop_code_step_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hcode :
      stackMachineCondition
        (stackFrameWriteRegister state 7
          (state.machine.memory (state.machine.registers 8))).machine
        .test 7 (.imm 4) = false)
    (hscan : scan ≠ destination)
    (hcodeNat : stackGcNatHeaderHasCode (memory scan) = true)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width
            (config.wordBits - config.lenSize))) + BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    let nextScan :=
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord
    stackFrameNormalRegisterNat
        (evalStackFrameFuel (fuel + 12) state
          (stackSeq [
            .inst (.mem .load 7 8),
            .ite .test 7 (.imm 4)
              (stackSeq [
                stackGcShiftImmediate config .lsr 7
                  (config.wordBits - config.lenSize),
                stackGcAddBytes config 8,
                stackGcMoveListCode config])
              (stackSeq [
                stackGcShiftImmediate config .lsr 7
                  (config.wordBits - config.lenSize),
                stackGcAddOne config 7,
                stackGcShiftImmediate config .lsl 7 config.wordShift,
                stackGcAdd 8 7])])) 8 =
        some nextScan ∧
      stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
          memory domain condition =
        stackGcNatMoveLoop config fuel nextScan index destination oldBase
          memory domain (condition && domain scan) := by
  dsimp
  constructor
  · exact evalStackFrameFuel_stackGcMoveLoop_code_step_scan_matches_nat
      config fuel state scan memory domain hscratch7 hscratch8 hdomain
      haddress hmemory hcode hadvance hcount
  · exact stackGcNatMoveLoop_code_step config fuel scan index destination
      oldBase memory domain condition hscan hcodeNat

theorem evalStackFrameFuel_stackGcMoveLoop_iterate [NeZero width]
    (config : StackGcConfig) (fuel stepFuel iterations : Nat)
    (state : StackFrameMachineState width)
    (step : StackFrameMachineState width → StackFrameMachineState width)
    (hcondition : ∀ current, current < iterations →
      stackMachineCondition
        (stackFrameIterate step current state).machine .notEqual 3 (.reg 8) = true)
    (hbody : ∀ current extra, current < iterations →
      evalStackFrameFuel (extra + stepFuel)
        (stackFrameIterate step current state)
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])]) =
        some (.normal (stackFrameIterate step (current + 1) state)))
    (hfinal :
      stackMachineCondition
        (stackFrameIterate step iterations state).machine .notEqual 3 (.reg 8) = false) :
    evalStackFrameFuel (fuel + iterations + stepFuel + 3) state
        (stackGcMoveLoopCode config) =
      some (.normal (stackFrameIterate step iterations state)) := by
  simpa [stackGcMoveLoopCode, stackGcWhile] using
    (evalStackFrameFuel_loop_iterate fuel stepFuel iterations state
      .notEqual 3 (.reg 8)
      (stackSeq [
        .inst (.mem .load 7 8),
        .ite .test 7 (.imm 4)
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddBytes config 8,
            stackGcMoveListCode config])
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddOne config 7,
            stackGcShiftImmediate config .lsl 7 config.wordShift,
            stackGcAdd 8 7])]) step hcondition hbody hfinal)

theorem evalStackFrameFuel_stackGcMoveLoop_data_branch [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state final : StackFrameMachineState width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hcondition : stackMachineCondition state.machine .test 7 (.imm 4) = true)
    (hmove :
      evalStackFrameFuel (fuel + 12)
        (stackGcMoveLoopCodePrefixState config state)
        (stackGcMoveListCode config) =
      some (.normal final)) :
    evalStackFrameFuel (fuel + 15) state
        (.ite .test 7 (.imm 4)
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddBytes config 8,
            stackGcMoveListCode config])
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddOne config 7,
            stackGcShiftImmediate config .lsl 7 config.wordShift,
            stackGcAdd 8 7])) =
      some (.normal final) := by
  let afterLength := stackFrameWriteRegister state config.immediateScratch
    (BitVec.ofNat width (config.wordBits - config.lenSize))
  let afterShift := stackFrameWriteRegister afterLength 7
    (wordStackMachineShift .lsr (state.machine.registers 7)
      (afterLength.machine.registers config.immediateScratch))
  have hshift :
      evalStackFrameFuel (fuel + 13) state
        (stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize)) =
      some (.normal afterShift) := by
    simp [afterShift, afterLength, stackGcShiftImmediate,
      stackGcAddImmediate, stackGcConst, stackSeq, evalStackFrameFuel,
      evalStackFrameFuelWithCode, stackFrameBasic, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineShift, hscratch7,
      Ne.symm hscratch7]
  have hadd :
      evalStackFrameFuel (fuel + 12) afterShift
        (stackGcAddBytes config 8) =
      some (.normal (stackGcMoveLoopCodePrefixState config state)) := by
    simp [stackGcMoveLoopCodePrefixState, afterShift, afterLength,
      stackGcAddBytes, stackGcAddImmediate, stackGcConst, stackGcAdd,
      stackSeq, evalStackFrameFuel, evalStackFrameFuelWithCode,
      stackFrameBasic, stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, hscratch8, Ne.symm hscratch8]
  have hrest := evalStackFrameFuel_seq_normal (fuel + 12) afterShift
    (stackGcMoveLoopCodePrefixState config state)
    (stackGcAddBytes config 8) (stackGcMoveListCode config) hadd
  rw [hmove] at hrest
  have hwhole := evalStackFrameFuel_seq_normal (fuel + 13) state afterShift
    (stackGcShiftImmediate config .lsr 7
      (config.wordBits - config.lenSize))
    (stackSeq [stackGcAddBytes config 8, stackGcMoveListCode config]) hshift
  simp only [stackSeq] at hwhole
  rw [hrest] at hwhole
  rw [evalStackFrameFuel_ite_true (fuel + 14) state .test 7 (.imm 4)
    (stackSeq [
      stackGcShiftImmediate config .lsr 7
        (config.wordBits - config.lenSize),
      stackGcAddBytes config 8,
      stackGcMoveListCode config])
    (stackSeq [
      stackGcShiftImmediate config .lsr 7
        (config.wordBits - config.lenSize),
      stackGcAddOne config 7,
      stackGcShiftImmediate config .lsl 7 config.wordShift,
      stackGcAdd 8 7]) hcondition]
  simpa [stackSeq] using hwhole

theorem evalStackFrameFuel_stackGcMoveLoop_data_step [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state final : StackFrameMachineState width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hcondition : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = true)
    (hmove :
      evalStackFrameFuel (fuel + 12)
        (stackGcMoveLoopCodePrefixState config
          (stackFrameWriteRegister state 7
            (state.machine.memory (state.machine.registers 8))))
        (stackGcMoveListCode config) =
      some (.normal final)) :
    evalStackFrameFuel (fuel + 16) state
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])]) =
      some (.normal final) := by
  let loaded := stackFrameWriteRegister state 7
    (state.machine.memory (state.machine.registers 8))
  have hbranch := evalStackFrameFuel_stackGcMoveLoop_data_branch
    config fuel loaded final hscratch7 hscratch8 hcondition
    (by simpa [loaded] using hmove)
  have hbranch' :
      evalStackFrameFuel (fuel + 15)
        (stackFrameWriteRegister state 7
          (state.machine.memory (state.machine.registers 8)))
        (.ite .test 7 (.imm 4)
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddBytes config 8,
            stackGcMoveListCode config])
          (stackSeq [
            stackGcShiftImmediate config .lsr 7
              (config.wordBits - config.lenSize),
            stackGcAddOne config 7,
            stackGcShiftImmediate config .lsl 7 config.wordShift,
            stackGcAdd 8 7])) =
      some (.normal final) := by
    simpa [loaded] using hbranch
  have hload := evalStackFrameFuel_memLoad (fuel + 14) state 7 8 hdomain
  have hseq := evalStackFrameFuel_seq_normal (fuel + 15) state
    (stackFrameWriteRegister state 7
      (state.machine.memory (state.machine.registers 8)))
    (.inst (.mem .load 7 8))
    (.ite .test 7 (.imm 4)
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddBytes config 8,
        stackGcMoveListCode config])
      (stackSeq [
        stackGcShiftImmediate config .lsr 7
          (config.wordBits - config.lenSize),
        stackGcAddOne config 7,
        stackGcShiftImmediate config .lsl 7 config.wordShift,
        stackGcAdd 8 7])) hload
  rw [hbranch'] at hseq
  simpa [stackSeq] using hseq

theorem evalStackFrameFuel_stackGcMoveLoop_data_step_matches_nat
    [NeZero width] (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (state final : StackFrameMachineState width)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hscan : scan ≠ destination)
    (hcodeNat : stackGcNatHeaderHasCode (memory scan) ≠ true)
    (hcondition : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = true)
    (hmove :
      evalStackFrameFuel (fuel + 12)
        (stackGcMoveLoopCodePrefixState config
          (stackFrameWriteRegister state 7
            (state.machine.memory (state.machine.registers 8))))
        (stackGcMoveListCode config) =
      some (.normal final)) :
    let moved := stackGcNatMoveList config
      (stackGcNatDecodeLength config (memory scan))
      (scan + config.bytesInWord) index destination oldBase memory domain
    evalStackFrameFuel (fuel + 16) state
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])]) =
        some (.normal final) ∧
      stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
          memory domain condition =
        stackGcNatMoveLoop config fuel moved.nextScan moved.nextIndex
          moved.nextAddress oldBase moved.memory domain
          (condition && domain scan && moved.condition) := by
  dsimp
  constructor
  · exact evalStackFrameFuel_stackGcMoveLoop_data_step config fuel state final
      hscratch7 hscratch8 hdomain hcondition hmove
  · exact stackGcNatMoveLoop_data_step config fuel scan index destination oldBase
      memory domain condition hscan hcodeNat

theorem evalStackFrameFuel_stackGcMoveLoop_data_step_matches_nat_of_memory
    [NeZero width] (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (state final : StackFrameMachineState width)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hwidth : 3 ≤ width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (hscan : scan ≠ destination)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hcodeNat : stackGcNatHeaderHasCode (memory scan) ≠ true)
    (hmove :
      evalStackFrameFuel (fuel + 12)
        (stackGcMoveLoopCodePrefixState config
          (stackFrameWriteRegister state 7
            (state.machine.memory (state.machine.registers 8))))
        (stackGcMoveListCode config) =
      some (.normal final)) :
    let moved := stackGcNatMoveList config
      (stackGcNatDecodeLength config (memory scan))
      (scan + config.bytesInWord) index destination oldBase memory domain
    evalStackFrameFuel (fuel + 16) state
        (stackSeq [
          .inst (.mem .load 7 8),
          .ite .test 7 (.imm 4)
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddBytes config 8,
              stackGcMoveListCode config])
            (stackSeq [
              stackGcShiftImmediate config .lsr 7
                (config.wordBits - config.lenSize),
              stackGcAddOne config 7,
              stackGcShiftImmediate config .lsl 7 config.wordShift,
              stackGcAdd 8 7])]) =
        some (.normal final) ∧
      stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
          memory domain condition =
        stackGcNatMoveLoop config fuel moved.nextScan moved.nextIndex
          moved.nextAddress oldBase moved.memory domain
          (condition && domain scan && moved.condition) := by
  have hconditionIff := stackGcMoveLoop_header_condition_matches_nat
    state scan memory hwidth haddress hmemory
  have hcondition := hconditionIff.mpr hcodeNat
  exact evalStackFrameFuel_stackGcMoveLoop_data_step_matches_nat config fuel scan
    index destination oldBase state final memory domain condition hscratch7
    hscratch8 hdomain hscan hcodeNat hcondition hmove

theorem evalStackFrameFuel_stackGcMoveLoop_code_step_matches_nat_of_memory
    [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hwidth : 3 ≤ width)
    (hscratch7 : config.immediateScratch ≠ 7)
    (hscratch8 : config.immediateScratch ≠ 8)
    (hdomain : state.memoryDomain (state.machine.registers 8) = true)
    (haddress : state.machine.registers 8 = BitVec.ofNat width scan)
    (hmemory :
      (state.machine.memory (state.machine.registers 8)).toNat =
        memory scan)
    (hscan : scan ≠ destination)
    (hcodeNat : stackGcNatHeaderHasCode (memory scan) = true)
    (hadvance :
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord < 2 ^ width)
    (hcount :
      (((state.machine.memory (state.machine.registers 8) >>>
          shiftAmount (BitVec.ofNat width
            (config.wordBits - config.lenSize))) +
        BitVec.ofNat width 1) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)).toNat =
        (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord) :
    let nextScan :=
      scan + (stackGcNatDecodeLength config (memory scan) + 1) *
        config.bytesInWord
    stackFrameNormalRegisterNat
        (evalStackFrameFuel (fuel + 12) state
          (stackSeq [
            .inst (.mem .load 7 8),
            .ite .test 7 (.imm 4)
              (stackSeq [
                stackGcShiftImmediate config .lsr 7
                  (config.wordBits - config.lenSize),
                stackGcAddBytes config 8,
                stackGcMoveListCode config])
              (stackSeq [
                stackGcShiftImmediate config .lsr 7
                  (config.wordBits - config.lenSize),
                stackGcAddOne config 7,
                stackGcShiftImmediate config .lsl 7 config.wordShift,
                stackGcAdd 8 7])])) 8 =
        some nextScan ∧
      stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
          memory domain condition =
        stackGcNatMoveLoop config fuel nextScan index destination oldBase
          memory domain (condition && domain scan) := by
  have hconditionIff := stackGcMoveLoop_header_condition_matches_nat
    state scan memory hwidth haddress hmemory
  have hcode : stackMachineCondition
      (stackFrameWriteRegister state 7
        (state.machine.memory (state.machine.registers 8))).machine
      .test 7 (.imm 4) = false := by
    apply (Bool.eq_false_iff).mpr
    intro htrue
    exact (hconditionIff.mp htrue) hcodeNat
  exact evalStackFrameFuel_stackGcMoveLoop_code_step_matches_nat config fuel
    state scan index destination oldBase memory domain condition hscratch7
    hscratch8 hdomain haddress hmemory hcode hscan hcodeNat hadvance hcount

theorem stackGcMachineNatRelation_stackFrameIterate_of_step
    [NeZero width] (iterations : Nat)
    (state : StackFrameMachineState width)
    (step : StackFrameMachineState width → StackFrameMachineState width)
    (scans : Nat → Nat) (memories : Nat → Nat → Nat)
    (hinitial : stackGcMachineNatRelation state (scans 0) (memories 0))
    (hstep : ∀ current, current < iterations →
      stackGcMachineNatRelation
          (stackFrameIterate step current state)
          (scans current) (memories current) →
      stackGcMachineNatRelation
          (stackFrameIterate step (current + 1) state)
          (scans (current + 1)) (memories (current + 1))) :
    stackGcMachineNatRelation
      (stackFrameIterate step iterations state)
      (scans iterations) (memories iterations) := by
  induction iterations with
  | zero =>
      simpa [stackFrameIterate] using hinitial
  | succ iterations ih =>
      have hprevious := ih (hstep := fun current hcurrent hrelation =>
        hstep current (by omega) hrelation)
      have hnext := hstep iterations (by omega) hprevious
      simpa [Nat.succ_eq_add_one] using hnext

theorem evalStackFrameFuel_stackGcMoveList_iterate_with_nat_relation
    [NeZero width] (config : StackGcConfig)
    (fuel stepFuel iterations : Nat)
    (state : StackFrameMachineState width)
    (step : StackFrameMachineState width → StackFrameMachineState width)
    (scans : Nat → Nat) (memories : Nat → Nat → Nat)
    (hinitial : stackGcMachineNatRelation state (scans 0) (memories 0))
    (hcondition : ∀ current, current < iterations →
      stackMachineCondition
        (stackFrameIterate step current state).machine .notEqual 7 (.imm 0) = true)
    (hbody : ∀ current extra, current < iterations →
      evalStackFrameFuel (extra + stepFuel)
        (stackFrameIterate step current state)
        (stackSeq [
          .inst (.mem .load 5 8),
          stackGcSubOne config 7,
          stackGcMoveCode config,
          .inst (.mem .store 5 8),
          stackGcAddBytes config 8]) =
        some (.normal (stackFrameIterate step (current + 1) state)))
    (hfinal :
      stackMachineCondition
        (stackFrameIterate step iterations state).machine .notEqual 7 (.imm 0) = false)
    (hstep : ∀ current, current < iterations →
      stackGcMachineNatRelation
          (stackFrameIterate step current state)
          (scans current) (memories current) →
      stackGcMachineNatRelation
          (stackFrameIterate step (current + 1) state)
          (scans (current + 1)) (memories (current + 1))) :
    evalStackFrameFuel (fuel + iterations + stepFuel + 3) state
        (stackGcMoveListCode config) =
      some (.normal (stackFrameIterate step iterations state)) ∧
      stackGcMachineNatRelation
        (stackFrameIterate step iterations state)
        (scans iterations) (memories iterations) := by
  constructor
  · exact evalStackFrameFuel_stackGcMoveList_iterate config fuel stepFuel
      iterations state step hcondition hbody hfinal
  · exact stackGcMachineNatRelation_stackFrameIterate_of_step iterations
      state step scans memories hinitial hstep

end Flapjack.RiscV
