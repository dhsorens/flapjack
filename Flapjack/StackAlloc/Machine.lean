import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-!
# Executable StackLang machine boundary for StackAlloc

The existing `WordStackMachineState` is an abstract word-memory model used by
the Word-to-Stack proofs.  This file extends it with control outcomes and a
fuel-bounded evaluator for the StackLang constructs used by the non-
generational collector.  It is intentionally explicit about unsupported
calls and stack-frame operations: those are separate backend obligations and
cannot be silently treated as successful execution.
-/

namespace Flapjack.RiscV

inductive StackMachineControl (width : Nat) where
  | normal (state : WordStackMachineState width)
  | break (state : WordStackMachineState width)
  | continue (state : WordStackMachineState width)
  | returned (state : WordStackMachineState width) (value : Word width)
  | halted (state : WordStackMachineState width) (value : Word width)

def stackMachineCondition [NeZero width] (state : WordStackMachineState width)
    (operator : Cmp) (condition : Nat) (right : WordRegImm Nat) : Bool :=
  let leftValue := state.registers condition
  let rightValue := match right with
    | .imm value => BitVec.ofNat width value
    | .reg register => state.registers register
  match operator with
  | .equal => leftValue == rightValue
  | .notEqual => leftValue != rightValue
  | .less => signedLess leftValue rightValue
  | .notLess => !signedLess leftValue rightValue
  | .lower => decide (leftValue < rightValue)
  | .notLower => decide (¬ leftValue < rightValue)
  | .test => leftValue &&& rightValue == 0
  | .notTest => leftValue &&& rightValue != 0

def stackMachineWriteAny [NeZero width]
    (state : WordStackMachineState width) (register offsetRegister : Nat)
    (value : Word width) : WordStackMachineState width :=
  wordStackMachineWriteSlot state
    (state.registers offsetRegister).toNat value

def stackMachineReadAny [NeZero width]
    (state : WordStackMachineState width) (offsetRegister : Nat) : Word width :=
  state.stack (state.registers offsetRegister).toNat

def stackMachineWriteBitmap [NeZero width]
    (state : WordStackMachineState width) (destination address : Nat) :
    WordStackMachineState width :=
  wordStackMachineWriteRegister state destination
    (state.memory (state.stores .bitmapBase + state.registers address))

def evalStackProgFuel [NeZero width] :
    Nat → WordStackMachineState width → StackProg Nat →
      Option (StackMachineControl width)
  | 0, _, _ => none
  | fuel + 1, state, .skip => some (.normal state)
  | fuel + 1, state, .const destination value =>
      some (.normal (wordStackMachineWriteRegister state destination
        (BitVec.ofNat width value)))
  | fuel + 1, state, .arith operator destination left right =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator (state.registers left)
          (state.registers right))))
  | fuel + 1, state, .shift operator destination left right =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineShift operator (state.registers left)
          (state.registers right))))
  | fuel + 1, state, .inst instruction =>
      (evalWordStackMachine state (.inst instruction)).map .normal
  | fuel + 1, state, .get destination store =>
      some (.normal (wordStackMachineWriteRegister state destination
        (state.stores store)))
  | fuel + 1, state, .set store source =>
      some (.normal (wordStackMachineWriteStore state store
        (state.registers source)))
  | fuel + 1, state, .opCurrHeap operator destination source =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator (state.registers source)
          (state.stores .currHeap))))
  | fuel + 1, state, .stackLoad register offset =>
      some (.normal (wordStackMachineWriteRegister state register
        (state.stack offset)))
  | fuel + 1, state, .stackStore register offset =>
      some (.normal (wordStackMachineWriteSlot state offset
        (state.registers register)))
  | fuel + 1, state, .stackLoadAny register offsetRegister =>
      some (.normal (wordStackMachineWriteRegister state register
        (stackMachineReadAny state offsetRegister)))
  | fuel + 1, state, .stackStoreAny register offsetRegister =>
      some (.normal (stackMachineWriteAny state register offsetRegister
        (state.registers register)))
  | fuel + 1, state, .bitmapLoad destination address =>
      some (.normal (stackMachineWriteBitmap state destination address))
  | fuel + 1, state, .seq first second =>
      match evalStackProgFuel fuel state first with
      | some (.normal state) => evalStackProgFuel fuel state second
      | result => result
  | fuel + 1, state, .ite operator condition right thenBranch elseBranch =>
      if stackMachineCondition state operator condition right then
        evalStackProgFuel fuel state thenBranch
      else
        evalStackProgFuel fuel state elseBranch
  | fuel + 1, state, .loop body =>
      match evalStackProgFuel fuel state body with
      | some (.normal state) => evalStackProgFuel fuel state (.loop body)
      | some (.continue state) => evalStackProgFuel fuel state (.loop body)
      | some (.break state) => some (.normal state)
      | result => result
  | fuel + 1, state, .break _ => some (.break state)
  | fuel + 1, state, .continue _ => some (.continue state)
  | fuel + 1, state, .return register =>
      some (.returned state (state.registers register))
  | fuel + 1, state, .halt register =>
      some (.halted state (state.registers register))
  | _, _, _ => none

def stackGcSimpleZeroObservation [NeZero width]
    (result : Option (StackMachineControl width)) : Bool :=
  match result with
  | some (.normal state) =>
      state.registers 0 == 0 && state.registers 1 == 0 &&
        state.stores .currHeap == 0 && state.stores .triggerGC == 0
  | _ => false

def stackMachineNormalRegisterEquals [NeZero width]
    (result : Option (StackMachineControl width))
    (register value : Nat) : Bool :=
  match result with
  | some (.normal state) => state.registers register == BitVec.ofNat width value
  | _ => false

def stackMachineNormalMemoryEquals [NeZero width]
    (result : Option (StackMachineControl width))
    (address value : Nat) : Bool :=
  match result with
  | some (.normal state) =>
      state.memory (BitVec.ofNat width address) == BitVec.ofNat width value
  | _ => false

def stackMachineNormalRegisterNat [NeZero width]
    (result : Option (StackMachineControl width))
    (register : Nat) : Option Nat :=
  match result with
  | some (.normal state) => some (state.registers register).toNat
  | _ => none

/-! A small call resolver for the runtime path.  The collector stub returns
    through the call's explicit return continuation; unresolved labels and
    non-returning callees remain failures instead of being treated as normal
    control flow. -/
def evalStackLabelCallFuel [NeZero width]
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (target : Nat)
    (returnCode : StackProg Nat) : Option (StackMachineControl width) := do
  let callee ← code target
  let result ← evalStackProgFuel fuel state callee
  match result with
  | .returned state _ => evalStackProgFuel fuel state returnCode
  | _ => none

theorem evalStackLabelCallFuel_unknown [NeZero width]
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (target : Nat)
    (returnCode : StackProg Nat)
    (hunknown : code target = none) :
    evalStackLabelCallFuel fuel code state target returnCode = none := by
  simp [evalStackLabelCallFuel, hunknown]

theorem evalStackProgFuel_skip [NeZero width]
    (fuel : Nat) (state : WordStackMachineState width) :
    evalStackProgFuel (fuel + 1) state (.skip : StackProg Nat) =
      some (.normal state) := by
  rfl

theorem evalStackProgFuel_const [NeZero width]
    (fuel : Nat) (state : WordStackMachineState width)
    (destination value : Nat) :
    evalStackProgFuel (fuel + 1) state (.const destination value : StackProg Nat) =
      some (.normal (wordStackMachineWriteRegister state destination
        (BitVec.ofNat width value))) := by
  rfl

theorem evalStackProgFuel_loop_break [NeZero width]
    (fuel : Nat) (state : WordStackMachineState width) :
    evalStackProgFuel (fuel + 2) state
      (.loop (.break 0) : StackProg Nat) = some (.normal state) := by
  simp [evalStackProgFuel]

end Flapjack.RiscV
