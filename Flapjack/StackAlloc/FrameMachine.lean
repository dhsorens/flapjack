import Flapjack.StackAlloc.Machine
import Flapjack.StackAlloc.Correctness
import Flapjack.RiscV.PanMemory

/-!
# Bounded StackLang frame semantics

CakeML's StackLang state distinguishes the stack array from `stack_space`, the
number of free words at the front of the current frame.  The first executable
StackAlloc machine model intentionally used an unbounded stack function for
the collector body.  This module adds the bounded frame boundary needed by
the general StackLang semantics without changing that small collector model.

The evaluator is fuel-bounded and keeps unsupported calls explicit.  Its
frame operations follow the equations in `cakeml/compiler/backend/semantics/
stackSemScript.sml`: fixed and dynamic accesses are bounds-checked, dynamic
offsets must be word-aligned, and bitmap loads read a separate bitmap table.
-/

namespace Flapjack.RiscV

structure StackFrameMachineState (width : Nat) where
  machine : WordStackMachineState width
  stackSpace : Nat
  stackLimit : Nat
  bitmaps : List (Word width)
  bytesInWord : Word width
  memoryDomain : Word width → Bool
  sharedMemoryDomain : Word width → Bool

inductive StackFrameMachineControl (width : Nat) where
  | normal (state : StackFrameMachineState width)
  | break (state : StackFrameMachineState width)
  | continue (state : StackFrameMachineState width)
  | raised (state : StackFrameMachineState width) (value : Word width)
  | returned (state : StackFrameMachineState width) (value : Word width)
  | halted (state : StackFrameMachineState width) (value : Word width)

def stackFrameWriteRegister [NeZero width]
    (state : StackFrameMachineState width) (register : Nat)
    (value : Word width) : StackFrameMachineState width :=
  { state with machine := wordStackMachineWriteRegister state.machine register value }

def stackFrameWriteSlot [NeZero width]
    (state : StackFrameMachineState width) (slot : Nat)
    (value : Word width) : StackFrameMachineState width :=
  { state with machine := wordStackMachineWriteSlot state.machine slot value }

def stackFrameAnyOffset [NeZero width] (value : Word width) : Option Nat :=
  let offset := BitVec.ushiftRight value 3
  if BitVec.shiftLeft offset 3 == value then some offset.toNat else none

def stackGcMachineMoveAddress [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) : Word width :=
  let value := state.machine.registers 5
  let shifted := wordStackMachineShift .lsl
    (wordStackMachineShift .lsr value (BitVec.ofNat width config.shiftLength))
    (BitVec.ofNat width config.wordShift)
  wordStackMachineBinOp .add shifted (state.machine.stores .currHeap)

def stackGcMachineForwardingValue [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) : Word width :=
  let header := state.machine.memory (stackGcMachineMoveAddress config state)
  let shiftedHeader := wordStackMachineShift .lsl
    (wordStackMachineShift .lsr header (BitVec.ofNat width 2))
    (BitVec.ofNat width config.shiftLength)
  let clearShift := config.wordBits - (config.smallShiftLength - 1) - 1
  let lowBits := wordStackMachineShift .lsr
    (wordStackMachineShift .lsl (state.machine.registers 5)
      (BitVec.ofNat width clearShift))
    (BitVec.ofNat width clearShift)
  wordStackMachineBinOp .or lowBits shiftedHeader

def stackFrameFlatMemory (state : StackFrameMachineState width) :
    PanFlatMemory (Word width) :=
  fun address => some (state.machine.memory address)

def stackFrameApplyFlatMemory (state : StackFrameMachineState width)
    (memory : PanFlatMemory (Word width)) : StackFrameMachineState width :=
  let newMemory : Word width → Word width := fun address =>
      match memory address with
      | some value => value
      | none => state.machine.memory address
  let machine := { state.machine with memory := newMemory }
  { state with machine := machine }

def stackFrameBasic [NeZero width]
    (state : StackFrameMachineState width) :
    StackProg Nat → Option (StackFrameMachineControl width)
  | .skip => some (.normal state)
  | .const destination value =>
      some (.normal (stackFrameWriteRegister state destination
        (BitVec.ofNat width value)))
  | .arith operator destination left right =>
      some (.normal (stackFrameWriteRegister state destination
        (wordStackMachineBinOp operator (state.machine.registers left)
          (state.machine.registers right))))
  | .shift operator destination left right =>
      some (.normal (stackFrameWriteRegister state destination
        (wordStackMachineShift operator (state.machine.registers left)
          (state.machine.registers right))))
  | .inst (.mem .load destination address) =>
      let address := state.machine.registers address
      if state.memoryDomain address then
        some (.normal (stackFrameWriteRegister state destination
          (state.machine.memory address)))
      else none
  | .inst (.mem .store source address) =>
      let address := state.machine.registers address
      if state.memoryDomain address then
        some (.normal { state with machine :=
          (wordStackMachineWriteMemory state.machine address
            (state.machine.registers source)) })
      else none
  | .inst (.mem .load8 destination address) =>
      let address := state.machine.registers address
      (panRiscVReadByte state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address).map (fun value =>
          .normal (stackFrameWriteRegister state destination value))
  | .inst (.mem .load16 destination address) =>
      let address := state.machine.registers address
      (panRiscVRead16 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address).map (fun value =>
          .normal (stackFrameWriteRegister state destination value))
  | .inst (.mem .load32 destination address) =>
      let address := state.machine.registers address
      (panRiscVRead32 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address).map (fun value =>
          .normal (stackFrameWriteRegister state destination value))
  | .inst (.mem .store8 source address) =>
      let address := state.machine.registers address
      (panRiscVStoreByte state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address (state.machine.registers source)).map
        (stackFrameApplyFlatMemory state)
        |>.map (fun state => .normal state)
  | .inst (.mem .store16 source address) =>
      let address := state.machine.registers address
      (panRiscVStore16 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address (state.machine.registers source)).map
        (stackFrameApplyFlatMemory state)
        |>.map (fun state => .normal state)
  | .inst (.mem .store32 source address) =>
      let address := state.machine.registers address
      (panRiscVStore32 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord address (state.machine.registers source)).map
        (stackFrameApplyFlatMemory state)
        |>.map (fun state => .normal state)
  | .inst instruction =>
      (evalWordStackMachine state.machine (.inst instruction)).map
        (fun machine => .normal { state with machine := machine })
  | .get destination store =>
      some (.normal (stackFrameWriteRegister state destination
        (state.machine.stores store)))
  | .set store source =>
      some (.normal { state with machine :=
        (wordStackMachineWriteStore state.machine store
          (state.machine.registers source)) })
  | .opCurrHeap operator destination source =>
      some (.normal (stackFrameWriteRegister state destination
        (wordStackMachineBinOp operator (state.machine.registers source)
          (state.machine.stores .currHeap))))
  | .shMem .load destination address =>
      let address := state.machine.registers address
      if state.sharedMemoryDomain address then
        some (.normal (stackFrameWriteRegister state destination
          (state.machine.sharedMemory address)))
      else none
  | .shMem .store source address =>
      let address := state.machine.registers address
      if state.sharedMemoryDomain address then
        some (.normal { state with machine :=
          (wordStackMachineWriteSharedMemory state.machine address
            (state.machine.registers source)) })
      else none
  | _ => none

def stackFrameSlotIndex (state : StackFrameMachineState width)
    (offset : Nat) : Nat :=
  state.stackSpace + offset

def stackFrameIndexValid (state : StackFrameMachineState width)
    (index : Nat) : Bool :=
  index < state.stackLimit

def stackFrameBitmapAt : List (Word width) → Nat → Option (Word width)
  | [], _ => none
  | bitmap :: _, 0 => some bitmap
  | _ :: bitmaps, index + 1 => stackFrameBitmapAt bitmaps index

def evalStackFrameFuelWithCode [NeZero width] :
    Nat → (Nat → Option (StackProg Nat)) → StackFrameMachineState width →
      StackProg Nat → Option (StackFrameMachineControl width)
  | 0, _, _, _ => none
  | fuel + 1, _, state, .stackAlloc words =>
      if state.stackSpace < words then
        some (.halted state (BitVec.ofNat width 2))
      else
        some (.normal { state with stackSpace := state.stackSpace - words })
  | fuel + 1, _, state, .stackFree words =>
      if state.stackLimit ≤ state.stackSpace + words then none
      else
        some (.normal { state with stackSpace := state.stackSpace + words })
  | fuel + 1, _, state, .stackLoad register offset =>
      let index := stackFrameSlotIndex state offset
      if stackFrameIndexValid state index then
        some (.normal (stackFrameWriteRegister state register
          (state.machine.stack index)))
      else none
  | fuel + 1, _, state, .stackStore register offset =>
      let index := stackFrameSlotIndex state offset
      if stackFrameIndexValid state index then
        some (.normal (stackFrameWriteSlot state index
          (state.machine.registers register)))
      else none
  | fuel + 1, _, state, .stackLoadAny register offsetRegister =>
      match stackFrameAnyOffset (state.machine.registers offsetRegister) with
      | none => none
      | some offset =>
          let index := stackFrameSlotIndex state offset
          if stackFrameIndexValid state index then
            some (.normal (stackFrameWriteRegister state register
              (state.machine.stack index)))
          else none
  | fuel + 1, _, state, .stackStoreAny register offsetRegister =>
      match stackFrameAnyOffset (state.machine.registers offsetRegister) with
      | none => none
      | some offset =>
          let index := stackFrameSlotIndex state offset
          if stackFrameIndexValid state index then
            some (.normal (stackFrameWriteSlot state index
              (state.machine.registers register)))
          else none
  | fuel + 1, _, state, .stackGetSize register =>
      some (.normal (stackFrameWriteRegister state register
        (BitVec.ofNat width state.stackSpace)))
  | fuel + 1, _, state, .stackSetSize register =>
      let value := (state.machine.registers register).toNat
      if state.stackLimit ≤ value then none
      else
        some (.normal
          { (stackFrameWriteRegister state register
              (BitVec.shiftLeft (state.machine.registers register) 3)) with
            stackSpace := value })
  | fuel + 1, _, state, .bitmapLoad destination address =>
      if destination = address then none
      else match state.machine.registers address with
      | address =>
          match stackFrameBitmapAt state.bitmaps address.toNat with
          | none => none
          | some bitmap =>
              some (.normal (stackFrameWriteRegister state destination bitmap))
  | fuel + 1, _, state, .break _ => some (.break state)
  | fuel + 1, _, state, .continue _ => some (.continue state)
  | fuel + 1, _, state, .raise register =>
      some (.raised state (state.machine.registers register))
  | fuel + 1, _, state, .return register =>
      some (.returned state (state.machine.registers register))
  | fuel + 1, _, state, .halt register =>
      some (.halted state (state.machine.registers register))
  | fuel + 1, code, state, .seq first second =>
      match evalStackFrameFuelWithCode fuel code state first with
      | some (.normal state) => evalStackFrameFuelWithCode fuel code state second
      | result => result
  | fuel + 1, code, state, .ite operator condition right thenBranch elseBranch =>
      if stackMachineCondition state.machine operator condition right then
        evalStackFrameFuelWithCode fuel code state thenBranch
      else
        evalStackFrameFuelWithCode fuel code state elseBranch
  | fuel + 1, code, state, .loop body =>
      match evalStackFrameFuelWithCode fuel code state body with
      | some (.normal state) => evalStackFrameFuelWithCode fuel code state (.loop body)
      | some (.continue state) => evalStackFrameFuelWithCode fuel code state (.loop body)
      | some (.break state) => some (.normal state)
      | result => result
  | fuel + 1, code, state, .call returnHandler (.label target) none =>
      match code target with
      | none => none
      | some callee =>
          match evalStackFrameFuelWithCode fuel code state callee with
          | some (.returned state value) =>
              match returnHandler with
              | some (returnCode, _, _, _) =>
                  evalStackFrameFuelWithCode fuel code state returnCode
              | none => some (.returned state value)
          | some (.raised state value) => some (.raised state value)
          | some (.halted state value) => some (.halted state value)
          | _ => none
  | fuel + 1, _, _, .call _ _ _ => none
  | fuel + 1, _, state, program => stackFrameBasic state program

def evalStackFrameFuel [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (program : StackProg Nat) : Option (StackFrameMachineControl width) :=
  evalStackFrameFuelWithCode fuel (fun _ => none) state program

def stackFrameNormalStackSpace [NeZero width]
    (result : Option (StackFrameMachineControl width)) : Option Nat :=
  match result with
  | some (.normal state) => some state.stackSpace
  | _ => none

def stackFrameNormalRegisterNat [NeZero width]
    (result : Option (StackFrameMachineControl width))
    (register : Nat) : Option Nat :=
  match result with
  | some (.normal state) => some (state.machine.registers register).toNat
  | _ => none

def stackFrameNormalMemoryNat [NeZero width]
    (result : Option (StackFrameMachineControl width))
    (address : Nat) : Option Nat :=
  match result with
  | some (.normal state) =>
      some (state.machine.memory (BitVec.ofNat width address)).toNat
  | _ => none

theorem evalStackFrameFuel_stackGetSize [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width) (register : Nat) :
    evalStackFrameFuel (fuel + 1) state (.stackGetSize register) =
      some (.normal (stackFrameWriteRegister state register
        (BitVec.ofNat width state.stackSpace))) := by
  rfl

theorem evalStackFrameFuel_stackLoad [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (register offset : Nat)
    (hvalid : state.stackSpace + offset < state.stackLimit) :
    evalStackFrameFuel (fuel + 1) state (.stackLoad register offset) =
      some (.normal (stackFrameWriteRegister state register
        (state.machine.stack (state.stackSpace + offset)))) := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode,
    stackFrameSlotIndex, stackFrameIndexValid, hvalid]

theorem evalStackFrameFuel_stackStore [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (register offset : Nat)
    (hvalid : state.stackSpace + offset < state.stackLimit) :
    evalStackFrameFuel (fuel + 1) state (.stackStore register offset) =
      some (.normal (stackFrameWriteSlot state
        (state.stackSpace + offset) (state.machine.registers register))) := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode,
    stackFrameSlotIndex, stackFrameIndexValid, hvalid]

theorem evalStackFrameFuel_memLoad [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (destination address : Nat)
    (hdomain : state.memoryDomain (state.machine.registers address) = true) :
    evalStackFrameFuel (fuel + 1) state
        (.inst (.mem .load destination address)) =
      some (.normal (stackFrameWriteRegister state destination
        (state.machine.memory (state.machine.registers address)))) := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
    hdomain]

theorem evalStackFrameFuel_memStore [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (source address : Nat)
    (hdomain : state.memoryDomain (state.machine.registers address) = true) :
    evalStackFrameFuel (fuel + 1) state
        (.inst (.mem .store source address)) =
      some (.normal { state with machine :=
        (wordStackMachineWriteMemory state.machine
          (state.machine.registers address) (state.machine.registers source)) }) := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, stackFrameBasic,
    hdomain]

theorem evalStackFrameFuel_memLoad32 [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (destination address : Nat) :
    evalStackFrameFuel (fuel + 1) state
        (.inst (.mem .load32 destination address)) =
      (panRiscVRead32 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord (state.machine.registers address)).map
        (fun value => .normal (stackFrameWriteRegister state destination value)) := by
  rfl

theorem evalStackFrameFuel_memStore32 [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (source address : Nat) :
    evalStackFrameFuel (fuel + 1) state
        (.inst (.mem .store32 source address)) =
      ((panRiscVStore32 state.memoryDomain (stackFrameFlatMemory state)
        state.bytesInWord (state.machine.registers address)
        (state.machine.registers source)).map (stackFrameApplyFlatMemory state)).map
        (fun state => .normal state) := by
  rfl

theorem evalStackFrameFuel_stackGcMemcpy_zero [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hzero : state.machine.registers 0 = 0) :
    evalStackFrameFuel (fuel + 4) state (stackGcMemcpy config) =
      some (.normal state) := by
  simp [stackGcMemcpy, stackGcWhile, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackMachineCondition, hzero]

theorem evalStackFrameGcMoveCode_immediate [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hvalue : state.machine.registers 5 &&& BitVec.ofNat width 1 = 0) :
    evalStackFrameFuel (fuel + 2) state (stackGcMoveCode config) =
      some (.normal state) := by
  simp [stackGcMoveCode, evalStackFrameFuel, evalStackFrameFuelWithCode,
    stackFrameBasic, stackMachineCondition, hvalue]

theorem evalStackFrameGcMoveCode_forwarding_register [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hodd : state.machine.registers 5 &&& BitVec.ofNat width 1 ≠ 0)
    (hdomain : state.memoryDomain (stackGcMachineMoveAddress config state) = true)
    (hforward :
      state.machine.memory (stackGcMachineMoveAddress config state) &&&
        BitVec.ofNat width 3 = 0) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 40) state (stackGcMoveCode config)) 5 =
      some (stackGcMachineForwardingValue config state).toNat := by
  by_cases htest : state.machine.registers 5 &&& BitVec.ofNat width 1 == 0
  · have hzero : state.machine.registers 5 &&& BitVec.ofNat width 1 = 0 := by
      simpa using htest
    exact False.elim (hodd hzero)
  · have hnot : ¬ state.machine.registers 5 &&& BitVec.ofNat width 1 = 0 := by
      intro hzero
      apply htest
      simp [hzero]
    have hcondition :
        stackMachineCondition state.machine .test 5 (.imm 1) = false := by
      change (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) = false
      cases hbool : (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) with
      | false => simp [hbool]
      | true => exact False.elim (htest hbool)
    have hforwardBool :
        ((state.machine.memory (stackGcMachineMoveAddress config state) &&&
            BitVec.ofNat width 3) == 0) = true := by
      simp [hforward]
    have hscratch0' : 0 ≠ config.immediateScratch := Ne.symm hscratch0
    have hscratch1' : 1 ≠ config.immediateScratch := Ne.symm hscratch1
    have hscratch5' : 5 ≠ config.immediateScratch := Ne.symm hscratch5
    have hdomain' :
        state.memoryDomain
            ((state.machine.registers 5 >>>
                shiftAmount (BitVec.ofNat width config.shiftLength)) <<<
              shiftAmount (BitVec.ofNat width config.wordShift) +
              state.machine.stores .currHeap) = true := by
      simpa [stackGcMachineMoveAddress, wordStackMachineShift,
        wordStackMachineBinOp] using hdomain
    have hforwardBool' :
        ((state.machine.memory
            ((state.machine.registers 5 >>>
                shiftAmount (BitVec.ofNat width config.shiftLength)) <<<
              shiftAmount (BitVec.ofNat width config.wordShift) +
              state.machine.stores .currHeap) &&&
            BitVec.ofNat width 3) == 0) = true := by
      simpa [stackGcMachineMoveAddress, wordStackMachineShift,
        wordStackMachineBinOp] using hforwardBool
    have hforwardEq :
        (state.machine.memory
            ((state.machine.registers 5 >>>
                shiftAmount (BitVec.ofNat width config.shiftLength)) <<<
              shiftAmount (BitVec.ofNat width config.wordShift) +
              state.machine.stores .currHeap) &&&
            BitVec.ofNat width 3) = BitVec.ofNat width 0 := by
      simpa [stackGcMachineMoveAddress, wordStackMachineShift,
        wordStackMachineBinOp] using hforward
    simp [stackGcMoveCode, evalStackFrameFuel, evalStackFrameFuelWithCode,
      stackSeq, stackGcMove, stackGcShiftImmediate, stackGcAddImmediate,
      stackGcConst, stackGcAdd, stackGcClearTop, stackFrameBasic,
      stackMachineCondition, stackFrameWriteRegister, stackFrameWriteSlot,
      wordStackMachineWriteRegister, wordStackMachineWriteStore,
      wordStackMachineBinOp, wordStackMachineShift,
      stackGcMachineMoveAddress,
      stackGcMachineForwardingValue, hcondition, hodd, hdomain, hdomain', hforward,
      hforwardBool, hforwardBool', hscratch0, hscratch1, hscratch5,
      hscratch0', hscratch1', hscratch5']
    have hoddEq :
        ¬ (state.machine.registers 5 &&& BitVec.ofNat width 1) =
            BitVec.ofNat width 0 := by
      simpa using hodd
    rw [if_neg hoddEq]
    rw [if_pos hforwardEq]
    simp [stackFrameNormalRegisterNat, stackGcMachineForwardingValue,
      wordStackMachineShift, wordStackMachineBinOp]

theorem evalStackFrameGcMoveCode_immediate_matches_nat [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (index destination oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool)
    (hbit : state.machine.registers 5 &&& BitVec.ofNat width 1 = 0)
    (hnat : (state.machine.registers 5).toNat % 2 = 0) :
    stackFrameNormalRegisterNat
      (evalStackFrameFuel (fuel + 2) state (stackGcMoveCode config)) 5 =
      some (stackGcNatMove config (state.machine.registers 5).toNat
        index destination oldBase memory domain).value := by
  have hmachine := evalStackFrameGcMoveCode_immediate config fuel state hbit
  have hspec := stackGcNatMove_immediate config
    (state.machine.registers 5).toNat index destination oldBase memory domain hnat
  simp [stackFrameNormalRegisterNat, hmachine, hspec]

theorem stackFrameAnyOffset_eq_toNat [NeZero width]
    (value : Word width) (offset : Nat)
    (h : stackFrameAnyOffset value = some offset) :
    offset = (BitVec.ushiftRight value 3).toNat := by
  simp [stackFrameAnyOffset] at h
  exact h.2.symm

end Flapjack.RiscV
