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
  | raised (state : WordStackMachineState width) (value : Word width)
  | halted (state : WordStackMachineState width) (value : Word width)

def stackMachineLookup : List (Nat × StackProg Nat) → Nat →
    Option (StackProg Nat)
  | [], _ => none
  | (label, program) :: sections, target =>
      if label = target then some program else stackMachineLookup sections target

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

def evalStackProgFuelWithCode [NeZero width] :
    Nat → (Nat → Option (StackProg Nat)) → WordStackMachineState width →
      StackProg Nat →
    Option (StackMachineControl width)
  | 0, _, _, _ => none
  | fuel + 1, _, state, .skip => some (.normal state)
  | fuel + 1, _, state, .const destination value =>
      some (.normal (wordStackMachineWriteRegister state destination
        (BitVec.ofNat width value)))
  | fuel + 1, _, state, .arith operator destination left right =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator (state.registers left)
          (state.registers right))))
  | fuel + 1, _, state, .shift operator destination left right =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineShift operator (state.registers left)
          (state.registers right))))
  | fuel + 1, _, state, .inst instruction =>
      (evalWordStackMachine state (.inst instruction)).map .normal
  | fuel + 1, _, state, .get destination store =>
      some (.normal (wordStackMachineWriteRegister state destination
        (state.stores store)))
  | fuel + 1, _, state, .set store source =>
      some (.normal (wordStackMachineWriteStore state store
        (state.registers source)))
  | fuel + 1, _, state, .opCurrHeap operator destination source =>
      some (.normal (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator (state.registers source)
          (state.stores .currHeap))))
  | fuel + 1, _, state, .stackLoad register offset =>
      some (.normal (wordStackMachineWriteRegister state register
        (state.stack offset)))
  | fuel + 1, _, state, .stackStore register offset =>
      some (.normal (wordStackMachineWriteSlot state offset
        (state.registers register)))
  | fuel + 1, _, state, .stackLoadAny register offsetRegister =>
      some (.normal (wordStackMachineWriteRegister state register
        (stackMachineReadAny state offsetRegister)))
  | fuel + 1, _, state, .stackStoreAny register offsetRegister =>
      some (.normal (stackMachineWriteAny state register offsetRegister
        (state.registers register)))
  | fuel + 1, _, state, .bitmapLoad destination address =>
      some (.normal (stackMachineWriteBitmap state destination address))
  | fuel + 1, code, state, .seq first second =>
      match evalStackProgFuelWithCode fuel code state first with
      | some (.normal state) => evalStackProgFuelWithCode fuel code state second
      | result => result
  | fuel + 1, code, state, .ite operator condition right thenBranch elseBranch =>
      if stackMachineCondition state operator condition right then
        evalStackProgFuelWithCode fuel code state thenBranch
      else
        evalStackProgFuelWithCode fuel code state elseBranch
  | fuel + 1, code, state, .loop body =>
      match evalStackProgFuelWithCode fuel code state body with
      | some (.normal state) => evalStackProgFuelWithCode fuel code state (.loop body)
      | some (.continue state) => evalStackProgFuelWithCode fuel code state (.loop body)
      | some (.break state) => some (.normal state)
      | result => result
  | fuel + 1, _, state, .break _ => some (.break state)
  | fuel + 1, _, state, .continue _ => some (.continue state)
  | fuel + 1, _, state, .raise register =>
      some (.raised state (state.registers register))
  | fuel + 1, _, state, .return register =>
      some (.returned state (state.registers register))
  | fuel + 1, _, state, .halt register =>
      some (.halted state (state.registers register))
  | fuel + 1, code, state, .call returnHandler (.label target) handler =>
      match code target with
      | none => none
      | some callee =>
          match evalStackProgFuelWithCode fuel code state callee with
          | some (.returned state value) =>
              match returnHandler with
              | some (returnCode, _, _, _) =>
                  evalStackProgFuelWithCode fuel code state returnCode
              | none => some (.returned state value)
          | some (.raised state value) =>
              match handler with
              | some (handlerCode, exceptionRegister, _) =>
                  evalStackProgFuelWithCode fuel code
                    (wordStackMachineWriteRegister state exceptionRegister value)
                    handlerCode
              | none => some (.raised state value)
          | some (.halted state value) => some (.halted state value)
          | _ => none
  | fuel + 1, _, _, .call _ _ _ => none
  | _, _, _, _ => none

def evalStackProgFuel [NeZero width] :
    Nat → WordStackMachineState width → StackProg Nat →
    Option (StackMachineControl width) :=
  fun fuel state program =>
    evalStackProgFuelWithCode fuel (fun _ => none) state program

theorem evalStackProgFuelWithCode_raise [NeZero width]
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (register : Nat) :
    evalStackProgFuelWithCode (fuel + 1) code state (.raise register) =
      some (.raised state (state.registers register)) := by
  rfl

theorem evalStackProgFuelWithCode_call_raise_handler [NeZero width]
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (target exceptionRegister
      handlerLabel : Nat) (returnCode : StackProg Nat)
    (link returnLabel entryLabel register : Nat) (handlerCode : StackProg Nat)
    (hcallee : code target = some (.raise register)) :
    evalStackProgFuelWithCode (fuel + 2) code state
        (.call (some (returnCode, link, returnLabel, entryLabel)) (.label target)
          (some (handlerCode, exceptionRegister, handlerLabel))) =
      evalStackProgFuelWithCode (fuel + 1) code
        (wordStackMachineWriteRegister state exceptionRegister
          (state.registers register)) handlerCode := by
  simp [evalStackProgFuelWithCode, hcallee]

abbrev StackMachineFfiHandler (width : Nat) :=
  FunName → Word width → Word width → Word width → Word width →
    WordStackMachineState width → Option (WordStackMachineState width)

/-! FFI-aware control evaluation.  The ordinary instruction cases are
    delegated to `evalStackProgFuelWithCode`; compound control forms recurse
    here so an FFI action remains observable when nested in a sequence, branch,
    loop, return continuation, or exception handler. -/
def evalStackProgFuelWithCodeAndFfi [NeZero width]
    (host : StackMachineFfiHandler width) :
    Nat → (Nat → Option (StackProg Nat)) → WordStackMachineState width →
      StackProg Nat → Option (StackMachineControl width)
  | 0, _, _, _ => none
  | fuel + 1, _, state, .ffi function configuration configurationLength array arrayLength _ =>
      (host function (state.registers configuration)
        (state.registers configurationLength) (state.registers array)
        (state.registers arrayLength) state).map .normal
  | fuel + 1, code, state, .seq first second =>
      match evalStackProgFuelWithCodeAndFfi host fuel code state first with
      | some (.normal state) =>
          evalStackProgFuelWithCodeAndFfi host fuel code state second
      | result => result
  | fuel + 1, code, state, .ite operator condition right thenBranch elseBranch =>
      if stackMachineCondition state operator condition right then
        evalStackProgFuelWithCodeAndFfi host fuel code state thenBranch
      else
        evalStackProgFuelWithCodeAndFfi host fuel code state elseBranch
  | fuel + 1, code, state, .loop body =>
      match evalStackProgFuelWithCodeAndFfi host fuel code state body with
      | some (.normal state) =>
          evalStackProgFuelWithCodeAndFfi host fuel code state (.loop body)
      | some (.continue state) =>
          evalStackProgFuelWithCodeAndFfi host fuel code state (.loop body)
      | some (.break state) => some (.normal state)
      | result => result
  | fuel + 1, code, state, .call returnHandler (.label target) handler =>
      match code target with
      | none => none
      | some callee =>
          match evalStackProgFuelWithCodeAndFfi host fuel code state callee with
          | some (.returned state value) =>
              match returnHandler with
              | some (returnCode, _, _, _) =>
                  evalStackProgFuelWithCodeAndFfi host fuel code state returnCode
              | none => some (.returned state value)
          | some (.raised state value) =>
              match handler with
              | some (handlerCode, exceptionRegister, _) =>
                  evalStackProgFuelWithCodeAndFfi host fuel code
                    (wordStackMachineWriteRegister state exceptionRegister value)
                    handlerCode
              | none => some (.raised state value)
          | some (.halted state value) => some (.halted state value)
          | _ => none
  | fuel + 1, _, _, .call _ _ _ => none
  | fuel + 1, code, state, program =>
      evalStackProgFuelWithCode (fuel + 1) code state program

theorem evalStackProgFuelWithCodeAndFfi_ffi [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width)
    (function : FunName) (configuration configurationLength array arrayLength : Nat)
    (returnAddress : Nat) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state
        (.ffi function configuration configurationLength array arrayLength
          returnAddress) =
      (host function (state.registers configuration)
        (state.registers configurationLength) (state.registers array)
        (state.registers arrayLength) state).map .normal := by
  rfl

theorem evalStackProgFuelWithCodeAndFfi_seq_normal [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state middle : WordStackMachineState width)
    (first second : StackProg Nat)
    (result : StackMachineControl width)
    (hfirst : evalStackProgFuelWithCodeAndFfi host fuel code state first =
      some (.normal middle))
    (hsecond : evalStackProgFuelWithCodeAndFfi host fuel code middle second =
      some result) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state
      (.seq first second) = some result := by
  simp [evalStackProgFuelWithCodeAndFfi, hfirst, hsecond]

theorem evalStackProgFuelWithCodeAndFfi_call_raise_handler [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (target exceptionRegister
      handlerLabel : Nat) (returnCode : StackProg Nat)
    (link returnLabel entryLabel register : Nat) (handlerCode : StackProg Nat)
    (hcallee : code target = some (.raise register)) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 2) code state
        (.call (some (returnCode, link, returnLabel, entryLabel)) (.label target)
          (some (handlerCode, exceptionRegister, handlerLabel))) =
      evalStackProgFuelWithCodeAndFfi host (fuel + 1) code
        (wordStackMachineWriteRegister state exceptionRegister
          (state.registers register)) handlerCode := by
  simp [evalStackProgFuelWithCodeAndFfi, evalStackProgFuelWithCode,
    hcallee]

theorem evalStackProgFuelWithCodeAndFfi_loop_break [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state state' : WordStackMachineState width)
    (body : StackProg Nat) (hbody :
      evalStackProgFuelWithCodeAndFfi host fuel code state body =
        some (.break state')) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state
      (.loop body) = some (.normal state') := by
  simp [evalStackProgFuelWithCodeAndFfi, hbody]

theorem evalStackProgFuelWithCodeAndFfi_call_return_handler [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state : WordStackMachineState width) (target register : Nat)
    (returnCode : StackProg Nat) (link returnLabel entryLabel : Nat)
    (handler : Option (StackProg Nat × Nat × Nat))
    (hcallee : code target = some (.return register)) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 2) code state
        (.call (some (returnCode, link, returnLabel, entryLabel)) (.label target)
          handler) =
      evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state returnCode := by
  simp [evalStackProgFuelWithCodeAndFfi, evalStackProgFuelWithCode,
    hcallee]

theorem evalStackGcMoveCode_immediate
    (config : StackGcConfig) (fuel : Nat)
    (state : WordStackMachineState 64)
    (hvalue : state.registers 5 &&& BitVec.ofNat 64 1 = 0) :
    evalStackProgFuel (fuel + 2) state (stackGcMoveCode config) =
      some (.normal state) := by
  simp [stackGcMoveCode, evalStackProgFuel, evalStackProgFuelWithCode,
    stackMachineCondition, hvalue]

def evalStackSectionsFuel [NeZero width]
    (fuel : Nat) (sections : List (Nat × StackProg Nat)) (entry : Nat)
    (state : WordStackMachineState width) :
    Option (StackMachineControl width) :=
  match stackMachineLookup sections entry with
  | some program =>
      evalStackProgFuelWithCode fuel (stackMachineLookup sections) state program
  | none => none

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
  simp [evalStackProgFuel, evalStackProgFuelWithCode]

theorem evalStackSectionsFuel_unknown [NeZero width]
    (fuel : Nat) (sections : List (Nat × StackProg Nat))
    (entry : Nat) (state : WordStackMachineState width)
    (hunknown : stackMachineLookup sections entry = none) :
    evalStackSectionsFuel fuel sections entry state = none := by
  simp [evalStackSectionsFuel, hunknown]

end Flapjack.RiscV
