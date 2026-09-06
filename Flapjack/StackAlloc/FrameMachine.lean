import Flapjack.StackAlloc.Machine

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
  | .shMem operator source address =>
      (evalWordStackMachine state.machine (.shMem operator source address)).map
        (fun machine => .normal { state with machine := machine })
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

theorem evalStackFrameFuel_stackGetSize [NeZero width]
    (fuel : Nat) (state : StackFrameMachineState width) (register : Nat) :
    evalStackFrameFuel (fuel + 1) state (.stackGetSize register) =
      some (.normal (stackFrameWriteRegister state register
        (BitVec.ofNat width state.stackSpace))) := by
  rfl

theorem stackFrameAnyOffset_eq_toNat [NeZero width]
    (value : Word width) (offset : Nat)
    (h : stackFrameAnyOffset value = some offset) :
    offset = (BitVec.ushiftRight value 3).toNat := by
  simp [stackFrameAnyOffset] at h
  exact h.2.symm

end Flapjack.RiscV
