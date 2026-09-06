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

def stackGcMoveAddressState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let state0 := stackFrameWriteRegister state 0
    (wordStackMachineBinOp .or (state.machine.registers 5)
      (state.machine.registers 5))
  let state1 := stackFrameWriteRegister state0 1
    (state.machine.stores .currHeap)
  let state2 := stackFrameWriteRegister state1 config.immediateScratch
    (BitVec.ofNat width config.shiftLength)
  let state3 := stackFrameWriteRegister state2 0
    (wordStackMachineShift .lsr (state2.machine.registers 0)
      (state2.machine.registers config.immediateScratch))
  let state4 := stackFrameWriteRegister state3 config.immediateScratch
    (BitVec.ofNat width config.wordShift)
  let state5 := stackFrameWriteRegister state4 0
    (wordStackMachineShift .lsl (state4.machine.registers 0)
      (state4.machine.registers config.immediateScratch))
  let state6 := stackFrameWriteRegister state5 0
    (wordStackMachineBinOp .add (state5.machine.registers 0)
      (state5.machine.registers 1))
  stackFrameWriteRegister state6 1
    (state.machine.memory (state6.machine.registers 0))

def stackGcMoveCopyPrefixState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let state0 := stackFrameWriteRegister state config.immediateScratch
    (BitVec.ofNat width (config.wordBits - config.lenSize))
  let state1 := stackFrameWriteRegister state0 1
    (wordStackMachineShift .lsr (state0.machine.registers 1)
      (state0.machine.registers config.immediateScratch))
  let state2 := stackFrameWriteRegister state1 config.immediateScratch
    (BitVec.ofNat width 1)
  let state3 := stackFrameWriteRegister state2 1
    (wordStackMachineBinOp .add (state2.machine.registers 1)
      (state2.machine.registers config.immediateScratch))
  let state4 := stackFrameWriteRegister state3 6
    (wordStackMachineBinOp .or (state3.machine.registers 1)
      (state3.machine.registers 1))
  let state5 := stackFrameWriteRegister state4 2
    (wordStackMachineBinOp .or (state4.machine.registers 0)
      (state4.machine.registers 0))
  stackFrameWriteRegister state5 0
    (wordStackMachineBinOp .or (state5.machine.registers 1)
      (state5.machine.registers 1))

def stackGcMoveForwardingSuffixState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let state0 := stackFrameWriteRegister state config.immediateScratch
    (BitVec.ofNat width 2)
  let state1 := stackFrameWriteRegister state0 1
    (wordStackMachineShift .lsr (state0.machine.registers 1)
      (state0.machine.registers config.immediateScratch))
  let state2 := stackFrameWriteRegister state1 config.immediateScratch
    (BitVec.ofNat width config.shiftLength)
  let state3 := stackFrameWriteRegister state2 1
    (wordStackMachineShift .lsl (state2.machine.registers 1)
      (state2.machine.registers config.immediateScratch))
  let clearShift := config.wordBits - (config.smallShiftLength - 1) - 1
  let state4 := stackFrameWriteRegister state3 config.immediateScratch
    (BitVec.ofNat width clearShift)
  let state5 := stackFrameWriteRegister state4 5
    (wordStackMachineShift .lsl (state4.machine.registers 5)
      (state4.machine.registers config.immediateScratch))
  let state6 := stackFrameWriteRegister state5 config.immediateScratch
    (BitVec.ofNat width clearShift)
  let state7 := stackFrameWriteRegister state6 5
    (wordStackMachineShift .lsr (state6.machine.registers 5)
      (state6.machine.registers config.immediateScratch))
  stackFrameWriteRegister state7 5
    (wordStackMachineBinOp .or (state7.machine.registers 5)
      (state7.machine.registers 1))

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

theorem evalStackFrameFuel_seq_normal [NeZero width]
    (fuel : Nat) (state state' : StackFrameMachineState width)
    (first second : StackProg Nat)
    (hfirst :
      evalStackFrameFuel fuel state first = some (.normal state')) :
    evalStackFrameFuel (fuel + 1) state (.seq first second) =
      evalStackFrameFuel fuel state' second := by
  have hfirst' :
      evalStackFrameFuelWithCode fuel (fun _ => none) state first =
        some (.normal state') := by
    simpa [evalStackFrameFuel] using hfirst
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hfirst']

theorem evalStackFrameFuel_ite_true [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (operator : Cmp) (condition : Nat) (right : WordRegImm Nat)
    (thenBranch elseBranch : StackProg Nat)
    (hcondition :
      stackMachineCondition state.machine operator condition right = true) :
    evalStackFrameFuel (fuel + 1) state
        (.ite operator condition right thenBranch elseBranch) =
      evalStackFrameFuel fuel state thenBranch := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hcondition]

theorem evalStackFrameFuel_ite_false [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width)
    (operator : Cmp) (condition : Nat) (right : WordRegImm Nat)
    (thenBranch elseBranch : StackProg Nat)
    (hcondition :
      stackMachineCondition state.machine operator condition right = false) :
    evalStackFrameFuel (fuel + 1) state
        (.ite operator condition right thenBranch elseBranch) =
      evalStackFrameFuel fuel state elseBranch := by
  simp [evalStackFrameFuel, evalStackFrameFuelWithCode, hcondition]

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

def stackFrameMemcpyStep [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let value := state.machine.memory (state.machine.registers 2)
  let afterLoad := stackFrameWriteRegister state 1 value
  let afterSourceStep := stackFrameWriteRegister afterLoad 2
    (wordStackMachineBinOp .add (afterLoad.machine.registers 2)
      (BitVec.ofNat width config.bytesInWord))
  let afterCountStep := stackFrameWriteRegister afterSourceStep 0
    (wordStackMachineBinOp .sub (afterSourceStep.machine.registers 0)
      (BitVec.ofNat width 1))
  let afterStore := { afterCountStep with machine :=
    (wordStackMachineWriteMemory afterCountStep.machine
      (afterCountStep.machine.registers 3)
      (afterCountStep.machine.registers 1)) }
  let afterScratch := stackFrameWriteRegister afterStore config.immediateScratch
    (BitVec.ofNat width config.bytesInWord)
  stackFrameWriteRegister afterScratch 3
    (wordStackMachineBinOp .add (afterScratch.machine.registers 3)
      (BitVec.ofNat width config.bytesInWord))

def stackGcMoveCopySuffixState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  let state0 := stackFrameMemcpyStep config state
  let state1 := stackFrameWriteRegister state0 0
    (wordStackMachineBinOp .or (state0.machine.registers 6)
      (state0.machine.registers 6))
  let state2 := stackFrameWriteRegister state1 config.immediateScratch
    (BitVec.ofNat width config.wordShift)
  let state3 := stackFrameWriteRegister state2 0
    (wordStackMachineShift .lsl (state2.machine.registers 0)
      (state2.machine.registers config.immediateScratch))
  let state4 := stackFrameWriteRegister state3 2
    (wordStackMachineBinOp .sub (state3.machine.registers 2)
      (state3.machine.registers 0))
  let state5 := stackFrameWriteRegister state4 0
    (wordStackMachineBinOp .or (state4.machine.registers 4)
      (state4.machine.registers 4))
  let state6 := stackFrameWriteRegister state5 config.immediateScratch
    (BitVec.ofNat width 2)
  let state7 := stackFrameWriteRegister state6 0
    (wordStackMachineShift .lsl (state6.machine.registers 0)
      (state6.machine.registers config.immediateScratch))
  let state8 := { state7 with machine :=
    (wordStackMachineWriteMemory state7.machine
      (state7.machine.registers 2) (state7.machine.registers 0)) }
  let state9 := stackFrameWriteRegister state8 1
    (wordStackMachineBinOp .or (state8.machine.registers 4)
      (state8.machine.registers 4))
  let clearShift := config.wordBits - (config.smallShiftLength - 1) - 1
  let state10 := stackFrameWriteRegister state9 config.immediateScratch
    (BitVec.ofNat width clearShift)
  let state11 := stackFrameWriteRegister state10 5
    (wordStackMachineShift .lsl (state10.machine.registers 5)
      (state10.machine.registers config.immediateScratch))
  let state12 := stackFrameWriteRegister state11 config.immediateScratch
    (BitVec.ofNat width clearShift)
  let state13 := stackFrameWriteRegister state12 5
    (wordStackMachineShift .lsr (state12.machine.registers 5)
      (state12.machine.registers config.immediateScratch))
  let state14 := stackFrameWriteRegister state13 config.immediateScratch
    (BitVec.ofNat width config.shiftLength)
  let state15 := stackFrameWriteRegister state14 1
    (wordStackMachineShift .lsl (state14.machine.registers 1)
      (state14.machine.registers config.immediateScratch))
  let state16 := stackFrameWriteRegister state15 5
    (wordStackMachineBinOp .or (state15.machine.registers 5)
      (state15.machine.registers 1))
  stackFrameWriteRegister state16 4
    (wordStackMachineBinOp .add (state16.machine.registers 4)
      (state16.machine.registers 6))

def stackGcMoveCopyState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  stackGcMoveCopySuffixState config
    (stackGcMoveCopyPrefixState config
      (stackGcMoveAddressState config state))

def stackGcMoveForwardingState [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width) :
    StackFrameMachineState width :=
  stackGcMoveForwardingSuffixState config
    (stackGcMoveAddressState config state)

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

theorem evalStackFrameFuel_stackGcMoveAddressPrefix [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (haddress :
      state.memoryDomain (stackGcMachineMoveAddress config state) = true) :
    evalStackFrameFuel (fuel + 20) state
        (stackGcMoveAddressPrefix config) =
      some (.normal (stackGcMoveAddressState config state)) := by
  have haddress' :
      state.memoryDomain
          (state.machine.registers 5 >>>
            shiftAmount (BitVec.ofNat width config.shiftLength) <<<
            shiftAmount (BitVec.ofNat width config.wordShift) +
            state.machine.stores .currHeap) = true := by
    simpa [stackGcMachineMoveAddress, wordStackMachineShift,
      wordStackMachineBinOp] using haddress
  simp [stackGcMoveAddressPrefix, stackGcMoveAddressState,
    evalStackFrameFuel, evalStackFrameFuelWithCode, stackSeq,
    stackGcShiftImmediate, stackGcConst, stackGcMove, stackGcAdd,
    stackFrameBasic, stackFrameWriteRegister, wordStackMachineWriteRegister,
    wordStackMachineBinOp, wordStackMachineShift,
    stackGcMachineMoveAddress, haddress, haddress', hscratch0, hscratch1,
    Ne.symm hscratch0, Ne.symm hscratch1]

theorem evalStackFrameFuel_stackGcMoveForwardingSuffix [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5) :
    evalStackFrameFuel (fuel + 20) state
        (stackGcMoveForwardingSuffix config) =
      some (.normal (stackGcMoveForwardingSuffixState config state)) := by
  simp [stackGcMoveForwardingSuffix, stackGcMoveForwardingSuffixState,
    evalStackFrameFuel, evalStackFrameFuelWithCode, stackSeq,
    stackGcShiftImmediate, stackGcConst, stackGcClearTop,
    stackGcAddImmediate, stackGcAdd, stackFrameBasic,
    stackFrameWriteRegister, wordStackMachineWriteRegister,
    wordStackMachineBinOp, wordStackMachineShift, hscratch1, hscratch5,
    Ne.symm hscratch1, Ne.symm hscratch5]

theorem evalStackFrameFuel_stackGcMoveCopyPrefix [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch6 : config.immediateScratch ≠ 6) :
    evalStackFrameFuel (fuel + 20) state
        (stackGcMoveCopyPrefix config) =
      some (.normal (stackGcMoveCopyPrefixState config state)) := by
  simp [stackGcMoveCopyPrefix, stackGcMoveCopyPrefixState,
    evalStackFrameFuel, evalStackFrameFuelWithCode, stackSeq,
    stackGcShiftImmediate, stackGcAddImmediate, stackGcAddOne,
    stackGcConst, stackGcMove, stackGcAdd, stackFrameBasic,
    stackFrameWriteRegister, wordStackMachineWriteRegister,
    wordStackMachineBinOp, wordStackMachineShift,
    hscratch0, hscratch1, hscratch2, hscratch6,
    Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch2,
    Ne.symm hscratch6]

theorem evalStackFrameFuel_stackGcMemcpy_zero [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hzero : state.machine.registers 0 = 0) :
    evalStackFrameFuel (fuel + 4) state (stackGcMemcpy config) =
      some (.normal state) := by
  simp [stackGcMemcpy, stackGcWhile, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackMachineCondition, hzero]

theorem evalStackFrameFuel_stackGcMemcpyBody [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + 20) state (stackGcMemcpyBody config) =
      some (.normal (stackFrameMemcpyStep config state)) := by
  have hscratch0' : 0 ≠ config.immediateScratch := Ne.symm hscratch0
  have hscratch1' : 1 ≠ config.immediateScratch := Ne.symm hscratch1
  have hscratch2' : 2 ≠ config.immediateScratch := Ne.symm hscratch2
  have hscratch3' : 3 ≠ config.immediateScratch := Ne.symm hscratch3
  simp [stackGcMemcpyBody, stackFrameMemcpyStep, stackSeq,
    stackGcAddBytes, stackGcSubOne, stackGcAddImmediate, stackGcSubImmediate,
    stackGcConst, stackGcAdd, stackGcSub, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackFrameBasic,
    stackFrameWriteRegister, stackFrameWriteSlot,
    wordStackMachineWriteRegister, wordStackMachineWriteMemory,
    wordStackMachineBinOp, wordStackMachineShift, hheaderDomain,
    hscratch0, hscratch1, hscratch2, hscratch3,
    hscratch0', hscratch1', hscratch2', hscratch3']
  funext current
  by_cases h3 : current = 3
  · simp [h3, hscratch3, hscratch3']
  · by_cases hs : current = config.immediateScratch
    · simp [h3, hs]
    · by_cases h0 : current = 0
      · simp [h3, hs, h0, hscratch0']
      · by_cases h2 : current = 2
        · simp [h3, hs, h0, h2, hscratch2']
        · by_cases h1 : current = 1
          · simp [h3, hs, h0, h2, h1, hscratch1']
          · simp [h3, hs, h0, h2, h1, hscratch1',
              hscratch2', hscratch0']

theorem evalStackFrameFuel_stackGcMemcpy_one [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hone : state.machine.registers 0 = BitVec.ofNat width 1)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + 24) state (stackGcMemcpy config) =
      some (.normal (stackFrameMemcpyStep config state)) := by
  have hscratch0' : 0 ≠ config.immediateScratch := Ne.symm hscratch0
  have hscratch1' : 1 ≠ config.immediateScratch := Ne.symm hscratch1
  have hscratch2' : 2 ≠ config.immediateScratch := Ne.symm hscratch2
  have hscratch3' : 3 ≠ config.immediateScratch := Ne.symm hscratch3
  have hstep :=
    evalStackFrameFuel_stackGcMemcpyBody config (fuel + 2) state
      hscratch0 hscratch1 hscratch2 hscratch3 hheaderDomain
  have hstep' :
      evalStackFrameFuelWithCode (fuel + 22) (fun _ => none) state
        (stackGcMemcpyBody config) =
        some (.normal (stackFrameMemcpyStep config state)) := by
    have hfuel : fuel + 2 + 20 = fuel + 22 := by omega
    rw [hfuel] at hstep
    simpa [evalStackFrameFuel] using hstep
  have hstepZero :
      (stackFrameMemcpyStep config state).machine.registers 0 = 0 := by
    simp [stackFrameMemcpyStep, hone, hscratch0, hscratch0', hscratch1,
      hscratch1', hscratch2, hscratch2', hscratch3, hscratch3',
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, wordStackMachineBinOp]
  have hwidth : width ≠ 0 := NeZero.ne width
  have hcondition :
      stackMachineCondition state.machine .notEqual 0 (.imm 0) = true := by
    simp [stackMachineCondition, hone, hwidth]
  have hstepCondition :
      stackMachineCondition (stackFrameMemcpyStep config state).machine
        .notEqual 0 (.imm 0) = false := by
    simp [stackMachineCondition, hstepZero]
  simp [stackGcMemcpy, stackGcWhile, evalStackFrameFuel,
    evalStackFrameFuelWithCode, hcondition, hstepCondition, hstep, hstep',
    hstepZero]

theorem evalStackFrameFuel_stackGcMoveCopySuffix_one [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hscratch4 : config.immediateScratch ≠ 4)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch6 : config.immediateScratch ≠ 6)
    (hone : state.machine.registers 0 = BitVec.ofNat width 1)
    (hheaderDomain : ∀ address, state.memoryDomain address = true) :
    evalStackFrameFuel (fuel + 25) state
        (stackGcMoveCopySuffix config) =
      some (.normal (stackGcMoveCopySuffixState config state)) := by
  have hstep :=
    evalStackFrameFuel_stackGcMemcpy_one config fuel state
      hscratch0 hscratch1 hscratch2 hscratch3 hone hheaderDomain
  have hstep' :
      evalStackFrameFuelWithCode (fuel + 24) (fun _ => none) state
        (stackGcMemcpy config) =
        some (.normal (stackFrameMemcpyStep config state)) := by
    simpa [evalStackFrameFuel] using hstep
  simp [stackGcMoveCopySuffix, stackGcMoveCopySuffixState,
    evalStackFrameFuel, evalStackFrameFuelWithCode, stackSeq,
    stackGcMove, stackGcShiftImmediate, stackGcAddImmediate,
    stackGcAddOne, stackGcAddBytes, stackGcSubImmediate, stackGcConst,
    stackGcAdd, stackGcSub, stackGcClearTop, stackFrameBasic,
    stackFrameMemcpyStep, hheaderDomain,
    stackFrameWriteRegister, wordStackMachineWriteRegister,
    wordStackMachineWriteMemory, wordStackMachineBinOp,
    wordStackMachineShift, hstep, hstep', hscratch0, hscratch1, hscratch2,
    hscratch3, hscratch4, hscratch5, hscratch6,
    Ne.symm hscratch0, Ne.symm hscratch1, Ne.symm hscratch2,
    Ne.symm hscratch3, Ne.symm hscratch4, Ne.symm hscratch5,
    Ne.symm hscratch6]

theorem evalStackFrameFuel_stackGcMoveCode_copy_one [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch2 : config.immediateScratch ≠ 2)
    (hscratch3 : config.immediateScratch ≠ 3)
    (hscratch4 : config.immediateScratch ≠ 4)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hscratch6 : config.immediateScratch ≠ 6)
    (hodd : state.machine.registers 5 &&&
      BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ address, state.memoryDomain address = true)
    (hheaderLength :
      state.machine.memory (stackGcMachineMoveAddress config state) >>>
        shiftAmount (BitVec.ofNat width
          (config.wordBits - config.lenSize)) = 0)
    (hnotforwarding :
      state.machine.memory (stackGcMachineMoveAddress config state) &&&
        BitVec.ofNat width 3 ≠ 0) :
    evalStackFrameFuel 29 state (stackGcMoveCode config) =
      some (.normal (stackGcMoveCopyState config state)) := by
  have houter :
      stackMachineCondition state.machine .test 5 (.imm 1) = false := by
    change (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) = false
    cases hbool : (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) with
    | false => simp [hbool]
    | true =>
        have hzero : state.machine.registers 5 &&& BitVec.ofNat width 1 =
            BitVec.ofNat width 0 := by
          simpa using hbool
        exact False.elim (hodd hzero)
  have haddress :
      state.memoryDomain (stackGcMachineMoveAddress config state) = true :=
    hheaderDomain _
  have hprefix :=
    evalStackFrameFuel_stackGcMoveAddressPrefix config 7 state
      hscratch0 hscratch1 haddress
  have hprefix' :
      evalStackFrameFuelWithCode 27 (fun _ => none) state
        (stackGcMoveAddressPrefix config) =
        some (.normal (stackGcMoveAddressState config state)) := by
    simpa [evalStackFrameFuel] using hprefix
  have hheaderLength' :
      state.machine.memory
          (state.machine.registers 5 >>>
            shiftAmount (BitVec.ofNat width config.shiftLength) <<<
            shiftAmount (BitVec.ofNat width config.wordShift) +
            state.machine.stores .currHeap) >>>
        shiftAmount (BitVec.ofNat width
          (config.wordBits - config.lenSize)) = BitVec.ofNat width 0 := by
    simpa [stackGcMachineMoveAddress, wordStackMachineShift,
      wordStackMachineBinOp] using hheaderLength
  have hinner :
      stackMachineCondition
          (stackGcMoveAddressState config state).machine
          .test 1 (.imm 3) = false := by
    change ((stackGcMoveAddressState config state).machine.registers 1 &&&
      BitVec.ofNat width 3 == 0) = false
    cases hbool :
        ((stackGcMoveAddressState config state).machine.registers 1 &&&
          BitVec.ofNat width 3 == 0) with
    | false => simp [hbool]
    | true =>
        have hzero :
            (stackGcMoveAddressState config state).machine.registers 1 &&&
              BitVec.ofNat width 3 = BitVec.ofNat width 0 := by
          simpa using hbool
        apply False.elim
        apply hnotforwarding
        simpa [stackGcMoveAddressState, stackFrameWriteRegister,
          wordStackMachineWriteRegister, wordStackMachineBinOp,
          wordStackMachineShift, stackGcMachineMoveAddress,
          hscratch0, hscratch1, Ne.symm hscratch0, Ne.symm hscratch1] using hzero
  have hcopyPrefix :=
    evalStackFrameFuel_stackGcMoveCopyPrefix config 5
      (stackGcMoveAddressState config state)
      hscratch0 hscratch1 hscratch2 hscratch6
  have hcopyPrefix' :
      evalStackFrameFuelWithCode 25 (fun _ => none)
        (stackGcMoveAddressState config state)
        (stackGcMoveCopyPrefix config) =
        some (.normal (stackGcMoveCopyPrefixState config
          (stackGcMoveAddressState config state))) := by
    simpa [evalStackFrameFuel] using hcopyPrefix
  have hone :
      (stackGcMoveCopyPrefixState config
        (stackGcMoveAddressState config state)).machine.registers 0 =
          BitVec.ofNat width 1 := by
    simp [stackGcMoveCopyPrefixState, stackGcMoveAddressState,
      stackFrameWriteRegister, wordStackMachineWriteRegister,
      wordStackMachineBinOp, wordStackMachineShift,
      stackGcMachineMoveAddress, hscratch0, hscratch1, hscratch2,
      hscratch6, Ne.symm hscratch0, Ne.symm hscratch1,
      Ne.symm hscratch2, Ne.symm hscratch6, hheaderLength']
  have hcopySuffix :=
    evalStackFrameFuel_stackGcMoveCopySuffix_one config 0
      (stackGcMoveCopyPrefixState config
        (stackGcMoveAddressState config state))
      hscratch0 hscratch1 hscratch2 hscratch3 hscratch4 hscratch5 hscratch6
      hone hheaderDomain
  have hcopySuffix' :
      evalStackFrameFuelWithCode 25 (fun _ => none)
        (stackGcMoveCopyPrefixState config
          (stackGcMoveAddressState config state))
        (stackGcMoveCopySuffix config) =
        some (.normal (stackGcMoveCopySuffixState config
          (stackGcMoveCopyPrefixState config
            (stackGcMoveAddressState config state)))) := by
    simpa [evalStackFrameFuel] using hcopySuffix
  simp [stackGcMoveCode, stackGcMoveCopyState, stackSeq, evalStackFrameFuel,
    evalStackFrameFuelWithCode, houter, hinner, hprefix, hprefix',
    hcopyPrefix, hcopyPrefix', hcopySuffix, hcopySuffix']

theorem evalStackFrameFuel_stackGcMoveCode_forwarding [NeZero width]
    (config : StackGcConfig) (state : StackFrameMachineState width)
    (hscratch0 : config.immediateScratch ≠ 0)
    (hscratch1 : config.immediateScratch ≠ 1)
    (hscratch5 : config.immediateScratch ≠ 5)
    (hodd : state.machine.registers 5 &&&
      BitVec.ofNat width 1 ≠ 0)
    (hheaderDomain : ∀ address, state.memoryDomain address = true)
    (hforward :
      state.machine.memory (stackGcMachineMoveAddress config state) &&&
        BitVec.ofNat width 3 = 0) :
    evalStackFrameFuel 23 state (stackGcMoveCode config) =
      some (.normal (stackGcMoveForwardingState config state)) := by
  have houter :
      stackMachineCondition state.machine .test 5 (.imm 1) = false := by
    change (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) = false
    cases hbool : (state.machine.registers 5 &&& BitVec.ofNat width 1 == 0) with
    | false => simp [hbool]
    | true =>
        have hzero : state.machine.registers 5 &&& BitVec.ofNat width 1 =
            BitVec.ofNat width 0 := by
          simpa using hbool
        exact False.elim (hodd hzero)
  have haddress :
      state.memoryDomain (stackGcMachineMoveAddress config state) = true :=
    hheaderDomain _
  have hprefix :=
    evalStackFrameFuel_stackGcMoveAddressPrefix config 1 state
      hscratch0 hscratch1 haddress
  have hprefix' :
      evalStackFrameFuelWithCode 21 (fun _ => none) state
        (stackGcMoveAddressPrefix config) =
        some (.normal (stackGcMoveAddressState config state)) := by
    simpa [evalStackFrameFuel] using hprefix
  have hforward' :
      state.machine.memory
          (state.machine.registers 5 >>>
            shiftAmount (BitVec.ofNat width config.shiftLength) <<<
            shiftAmount (BitVec.ofNat width config.wordShift) +
            state.machine.stores .currHeap) &&& BitVec.ofNat width 3 =
          BitVec.ofNat width 0 := by
    simpa [stackGcMachineMoveAddress, wordStackMachineShift,
      wordStackMachineBinOp] using hforward
  have hinner :
      stackMachineCondition
          (stackGcMoveAddressState config state).machine
          .test 1 (.imm 3) = true := by
    change ((stackGcMoveAddressState config state).machine.registers 1 &&&
      BitVec.ofNat width 3 == 0) = true
    simp [stackGcMoveAddressState, stackFrameWriteRegister,
      wordStackMachineWriteRegister, wordStackMachineBinOp,
      wordStackMachineShift, stackGcMachineMoveAddress,
      hscratch0, hscratch1, Ne.symm hscratch0, Ne.symm hscratch1,
      hforward']
  have hsuffix :=
    evalStackFrameFuel_stackGcMoveForwardingSuffix config 0
      (stackGcMoveAddressState config state) hscratch1 hscratch5
  have hsuffix' :
      evalStackFrameFuelWithCode 20 (fun _ => none)
        (stackGcMoveAddressState config state)
        (stackGcMoveForwardingSuffix config) =
        some (.normal (stackGcMoveForwardingSuffixState config
          (stackGcMoveAddressState config state))) := by
    simpa [evalStackFrameFuel] using hsuffix
  simp [stackGcMoveCode, stackSeq, evalStackFrameFuel,
    evalStackFrameFuelWithCode, houter, hinner, hprefix, hprefix',
    hsuffix, hsuffix', stackGcMoveForwardingState]

theorem evalStackFrameFuel_stackGcMoveList_zero [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hzero : state.machine.registers 7 = BitVec.ofNat width 0) :
    evalStackFrameFuel (fuel + 3) state (stackGcMoveListCode config) =
      some (.normal state) := by
  simp [stackGcMoveListCode, stackGcWhile, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackMachineCondition, hzero]

theorem evalStackFrameFuel_stackGcMoveLoop_done [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hdone : state.machine.registers 3 = state.machine.registers 8) :
    evalStackFrameFuel (fuel + 3) state (stackGcMoveLoopCode config) =
      some (.normal state) := by
  simp [stackGcMoveLoopCode, stackGcWhile, evalStackFrameFuel,
    evalStackFrameFuelWithCode, stackMachineCondition, hdone]

theorem evalStackFrameFuel_stackGcMoveRootsBitmaps_zero [NeZero width]
    (config : StackGcConfig) (fuel : Nat)
    (state : StackFrameMachineState width)
    (hzero : state.machine.registers 9 = BitVec.ofNat width 0) :
    evalStackFrameFuel (fuel + 3) state
        (stackGcMoveRootsBitmapsCode config) =
      some (.normal state) := by
  simp [stackGcMoveRootsBitmapsCode, stackGcWhile, evalStackFrameFuel,
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
      stackSeq, stackGcMoveAddressPrefix, stackGcMoveForwardingSuffix,
      stackGcMove,
      stackGcShiftImmediate, stackGcAddImmediate,
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
