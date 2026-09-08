import Flapjack.RiscV.Calls
import Flapjack.WordSemantics

/-!
RISC-V environment-call boundary for Word FFI operations.

CakeML lowers foreign calls through a target-side environment-call primitive.
The native instruction model therefore keeps ECALL distinct from host
effects; executeWithFfi supplies the explicit environment transition used by
the compiler-correctness boundary.

The ABI used here is deliberately small and explicit:

* x10--x13 carry configuration pointer, configuration length, array pointer,
  and array length;
* x14 carries the numeric FFI service identifier; and
* the host receives the post-marshalling machine state and may reject the
  operation by returning none.
-/

namespace Flapjack.RiscV

structure WordFfiContext where
  services : List (FunName × Nat)

def lookupWordFfiService (function : FunName) :
    List (FunName × Nat) → Option Nat
  | [] => none
  | (candidate, service) :: services =>
      if function == candidate then some service
      else lookupWordFfiService function services

def wordFfiToRiscV [NeZero width] (context : WordFfiContext)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    Option (List (Instruction width)) := do
  let service ← lookupWordFfiService function context.services
  let moves ← wordRegisterMoves
    [(10, configuration), (11, configurationLength),
     (12, array), (13, arrayLength)]
  pure (moves ++
    [.addi 14 0 (BitVec.ofNat width service), .ecall])

abbrev WordFfiHost (width : Nat) :=
  Nat → Word width → Word width → Word width → Word width →
    State width → Option (State width)

def executeWithFfi [NeZero width] (host : WordFfiHost width)
    (state : State width) : Instruction width → Option (State width)
  | .ecall =>
      host (readRegister state 14).toNat
        (readRegister state 10) (readRegister state 11)
        (readRegister state 12) (readRegister state 13) state
  | instruction => some (execute state instruction)

def executeInstructionsWithFfi [NeZero width] (host : WordFfiHost width)
    (state : State width) : List (Instruction width) → Option (State width)
  | [] => some state
  | instruction :: instructions => do
      let state ← executeWithFfi host state instruction
      executeInstructionsWithFfi host state instructions

def executeCodeUntilWithFfi [NeZero width] (host : WordFfiHost width) :
    Nat → Word width → Word width → List (Instruction width) → State width →
      Option (State width)
  | 0, _, _, _, _ => none
  | fuel + 1, start, returnAddress, code, state =>
      if state.pc = returnAddress then some state
      else
        let byteOffset := (state.pc - start).toNat
        if byteOffset % 4 ≠ 0 then none
        else
          let index := byteOffset / 4
          match code[index]? with
          | some instruction => do
              let nextState ← executeWithFfi host state instruction
              executeCodeUntilWithFfi host fuel start returnAddress code nextState
          | none => none

def executeFunctionAtWithFfi [NeZero width] (host : WordFfiHost width)
    (fuel : Nat) (start entry returnAddress : Word width)
    (parameters : List (Fin 32)) (code : List (Instruction width))
    (returns : List (Fin 32)) (arguments : List (Word width))
    (state : State width) : Option (List (Word width)) :=
  if parameters.length != arguments.length then none
  else
    let initialized :=
      (parameters.zip arguments).foldl
        (fun state (register, value) => writeRegister state register value)
        { state with pc := entry }
    (executeCodeUntilWithFfi host fuel start returnAddress code initialized).map
      (fun state => returns.map (readRegister state))

theorem lookupWordFfiService_shape :
    lookupWordFfiService "sum" [("sum", 7), ("other", 8)] = some 7 := by
  rfl

theorem wordFfiToRiscV_shape [NeZero width] :
    wordFfiToRiscV
      { services := [("sum", 7)] } "sum" 2 3 4 5 =
      some [.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 (BitVec.ofNat width 7), .ecall] := by
  simp [wordFfiToRiscV, lookupWordFfiService, wordRegisterMoves,
    registerOfNat]

theorem executeWithFfi_ecall [NeZero width] (host : WordFfiHost width)
    (state : State width) :
    executeWithFfi host state .ecall =
      host (readRegister state 14).toNat
        (readRegister state 10) (readRegister state 11)
        (readRegister state 12) (readRegister state 13) state := by
  rfl

/-!
Call-aware FFI lowering keeps the existing `WordCallContext` API unchanged
while adding the service table required by an environment call.  This is the
first composed boundary for Word programs containing both ordinary calls and
foreign calls; loop control remains handled by the separate loop-aware pass.
-/
structure WordCallFfiContext (width : Nat) [NeZero width] where
  targets : List (Nat × Word width × List Nat × List Nat)
  services : List (FunName × Nat)

def wordFunctionToRiscVWithCallsAndFfi [NeZero width]
    (context : WordCallFfiContext width) :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .ffi function configuration configurationLength array arrayLength _ => do
      let code ← wordFfiToRiscV { services := context.services } function
        configuration configurationLength array arrayLength
      pure (code, [])
  | .seq first second => do
      let (firstCode, firstReturns) ←
        wordFunctionToRiscVWithCallsAndFfi context first
      if !firstReturns.isEmpty then
        pure (firstCode, firstReturns)
      else
        let (secondCode, secondReturns) ←
          wordFunctionToRiscVWithCallsAndFfi context second
        pure (firstCode ++ secondCode, secondReturns)
  | .ite operator condition rightValue thenBranch elseBranch => do
      let (branchLeft, right, prelude) ←
        wordConditionOperands operator condition rightValue
      let (thenCode, thenReturns) ←
        wordFunctionToRiscVWithCallsAndFfi context thenBranch
      let (elseCode, elseReturns) ←
        wordFunctionToRiscVWithCallsAndFfi context elseBranch
      if thenReturns != elseReturns then none
      else
        let falseOffset : Word width :=
          BitVec.ofNat width (8 + 4 * thenCode.length)
        let endOffset : Word width :=
          BitVec.ofNat width (4 + 4 * elseCode.length)
        let branchFalse ← match operator with
          | .equal => pure (.branchNe branchLeft right falseOffset)
          | .notEqual => pure (.branchEq branchLeft right falseOffset)
          | .less => pure (.branchGe branchLeft right falseOffset)
          | .notLess => pure (.branchLt branchLeft right falseOffset)
          | .lower => pure (.branchGeU branchLeft right falseOffset)
          | .notLower => pure (.branchLtU branchLeft right falseOffset)
          | .test => pure (.branchNe branchLeft right falseOffset)
          | .notTest => pure (.branchEq branchLeft right falseOffset)
        pure (prelude ++ [branchFalse] ++ thenCode ++
          [.branchEq 0 0 endOffset] ++ elseCode, thenReturns)
  | .mustTerminate body =>
      wordFunctionToRiscVWithCallsAndFfi context body
  | program => do
      let (code, returns) ← wordFunctionToRiscVWithCalls
        { targets := context.targets } program
      pure (code, returns)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

mutual
  def evalWordCallWithCallsAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (handler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordCallReturns (Word width) → Option Nat → List Nat →
        WordCallHandler (Word width) →
        Option (State width × List (Word width))
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, callHandler => do
        if callHandler.isSome then none
        else
          let target ← target
          let (parameters, body) ← lookupWordFunction target functions
          let values ← readWordRegisters state arguments
          let calleeState ← bindWordRegisters state parameters values
          let result ← evalWordFunctionWithCallsAndFfi functions handler fuel calleeState body
          let returnedState := { state with
            memory := result.1.memory
            privilege := result.1.privilege
            mode := result.1.mode }
          match returns with
          | none => some (returnedState, result.2)
          | some (names, _, _, _, _) => do
              let state ← assignWordRegisters returnedState names result.2
              some (state, [])
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordFunctionWithCallsAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (handler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) →
        Option (State width × List (Word width))
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments callHandler =>
        evalWordCallWithCallsAndFfi functions handler fuel state returns target arguments callHandler
    | fuel + 1, state, .ffi function configuration configurationLength array arrayLength _ =>
        evalWordFfi handler (fuel + 1) state
          (.ffi function configuration configurationLength array arrayLength ([], []))
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFunctionWithCallsAndFfi functions handler fuel state first
        if !result.2.isEmpty then some result
        else evalWordFunctionWithCallsAndFfi functions handler fuel result.1 second
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFunctionWithCallsAndFfi functions handler fuel state thenBranch
        else evalWordFunctionWithCallsAndFfi functions handler fuel state elseBranch
    | fuel + 1, state, .mustTerminate body =>
        evalWordFunctionWithCallsAndFfi functions handler fuel state body
    | _fuel + 1, state, program => evalWordFunction state program
    termination_by fuel _ _ => fuel
end

/-!
The normal path of a sequence is the semantic counterpart of the instruction
list concatenation used by the FFI-aware compiler.  Keeping this equation
named makes later handler and loop simulation proofs consume the evaluator
without unfolding its fuel recursion at every call site.
-/
theorem evalWordFunctionWithCallsAndFfi_seq_normal [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state middle final : State width)
    (first second : WordProg (Word width)) (values : List (Word width))
    (hfirst : evalWordFunctionWithCallsAndFfi functions handler fuel state first =
      some (middle, []))
    (hsecond : evalWordFunctionWithCallsAndFfi functions handler fuel middle second =
      some (final, values)) :
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.seq first second) = some (final, values) := by
  simp [evalWordFunctionWithCallsAndFfi, hfirst, hsecond]

theorem evalWordFunctionWithCallsAndFfi_seq_terminal [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state middle : State width)
    (first second : WordProg (Word width)) (values : List (Word width))
    (hfirst : evalWordFunctionWithCallsAndFfi functions handler fuel state first =
      some (middle, values))
    (hvalues : values ≠ []) :
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.seq first second) = some (middle, values) := by
  simp [evalWordFunctionWithCallsAndFfi, hfirst, hvalues]

theorem evalWordFunctionWithCallsAndFfi_ite_true [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state : State width) (operator : Cmp)
    (condition : Nat) (rightValue : WordRegImm (Word width))
    (thenBranch elseBranch : WordProg (Word width))
    (result : State width × List (Word width))
    (hcondition : evalWordCondition state operator condition rightValue = some true)
    (hthen : evalWordFunctionWithCallsAndFfi functions handler fuel state thenBranch =
      some result) :
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.ite operator condition rightValue thenBranch elseBranch) = some result := by
  simp [evalWordFunctionWithCallsAndFfi, hcondition, hthen]

theorem evalWordFunctionWithCallsAndFfi_ite_false [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state : State width) (operator : Cmp)
    (condition : Nat) (rightValue : WordRegImm (Word width))
    (thenBranch elseBranch : WordProg (Word width))
    (result : State width × List (Word width))
    (hcondition : evalWordCondition state operator condition rightValue = some false)
    ( helse : evalWordFunctionWithCallsAndFfi functions handler fuel state elseBranch =
      some result) :
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.ite operator condition rightValue thenBranch elseBranch) = some result := by
  simp [evalWordFunctionWithCallsAndFfi, hcondition, helse]

theorem wordFunctionToRiscVWithCallsAndFfi_ffi [NeZero width] :
    wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext width)
      (.ffi "sum" 2 3 4 5 ([], [])) =
      some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 (BitVec.ofNat width 7), .ecall], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, registerOfNat]

/-!
The loop-aware companion uses the same control-marker layout as
`wordFunctionToRiscVWithCallsAndLoops`, but delegates straight-line leaves to
the FFI-aware selector above.  Consequently an FFI operation can occur in a
loop body while break and continue offsets are still resolved after the body
length is known.
-/
mutual
  def wordFunctionToRiscVWithCallsAndFfiAndLoopsAux [NeZero width]
      (context : WordCallFfiContext width) :
      WordProg (Word width) →
        Option (List (WordControlInstruction width) × List (Fin 32))
    | .break 0 => some ([.breakJump], [])
    | .continue 0 => some ([.continueJump], [])
    | .loop _ body _ => do
        let (bodyCode, bodyReturns) ←
          wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context body
        if !bodyReturns.isEmpty then none
        else
          let bodyCode ← resolveWordLoopBody bodyCode
          pure (bodyCode.map .instruction ++
            [.instruction (.jal 0 (0 - BitVec.ofNat width (4 * bodyCode.length)))], [])
    | .ite operator condition rightValue thenBranch elseBranch => do
        let (branchLeft, right, prelude) ←
          wordConditionOperands operator condition rightValue
        let (thenCode, thenReturns) ←
          wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context thenBranch
        let (elseCode, elseReturns) ←
          wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context elseBranch
        if thenReturns != elseReturns then none
        else
          let falseOffset : Word width :=
            BitVec.ofNat width (8 + 4 * thenCode.length)
          let endOffset : Word width :=
            BitVec.ofNat width (4 + 4 * elseCode.length)
          let branchFalse ← match operator with
            | .equal => pure (.branchNe branchLeft right falseOffset)
            | .notEqual => pure (.branchEq branchLeft right falseOffset)
            | .less => pure (.branchGe branchLeft right falseOffset)
            | .notLess => pure (.branchLt branchLeft right falseOffset)
            | .lower => pure (.branchGeU branchLeft right falseOffset)
            | .notLower => pure (.branchLtU branchLeft right falseOffset)
            | .test => pure (.branchNe branchLeft right falseOffset)
            | .notTest => pure (.branchEq branchLeft right falseOffset)
          pure (prelude.map .instruction ++
            [.instruction branchFalse] ++ thenCode ++
            [.instruction (.branchEq 0 0 endOffset)] ++ elseCode, thenReturns)
    | .mustTerminate body =>
        wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context body
    | .seq first second => do
        let (firstCode, firstReturns) ←
          wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context first
        if !firstReturns.isEmpty then
          pure (firstCode, firstReturns)
        else
          let (secondCode, secondReturns) ←
            wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context second
          pure (firstCode ++ secondCode, secondReturns)
    | program => do
        let (code, returns) ← wordFunctionToRiscVWithCallsAndFfi context program
        pure (code.map .instruction, returns)
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
end

def wordFunctionToRiscVWithCallsAndFfiAndLoops [NeZero width]
    (context : WordCallFfiContext width) :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32)) :=
  fun program => do
    let (code, returns) ←
      wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context program
    let code ← wordControlInstructions code
    pure (code, returns)

theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_break [NeZero width] :
    wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := [] } : WordCallFfiContext width)
      ((.loop [] (.break 0) []) : WordProg (Word width)) =
      some ([.jal 0 (BitVec.ofNat width 8),
        .jal 0 (0 - BitVec.ofNat width 4)], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, resolveWordLoopBody,
    resolveWordLoopBodyAux, wordControlInstructions]

theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_continue [NeZero width] :
    wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := [] } : WordCallFfiContext width)
      ((.loop [] (.continue 0) []) : WordProg (Word width)) =
      some ([.jal 0 0,
        .jal 0 (0 - BitVec.ofNat width 4)], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, resolveWordLoopBody,
    resolveWordLoopBodyAux, wordControlInstructions]

end Flapjack.RiscV
