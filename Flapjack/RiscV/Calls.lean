import Flapjack.RiscV.Loops
import Flapjack.WordSemantics

/-!
RISC-V call-sequence selection for the first Flapjack calling convention.

The convention keeps Word parameter and return registers explicit. x31 is
reserved as the scratch register for materializing a callee entry address,
x1 is the link register, and JALR x0, x1, 0 is the callee return. x30 is
the downward-growing stack pointer for ordinary calls: the caller saves its
incoming x1 before the call and restores it after moving return values.
Calls with no destination registers are lowered as true tail calls and use
JALR x0, x31, 0; a later linker will resolve function labels to entry
addresses and validate the reserved-register conditions.
-/

namespace Flapjack.RiscV

def wordRegisterMoves [NeZero width] : List (Nat × Nat) →
    Option (List (Instruction width))
  | [] => some []
  | (destination, source) :: moves => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      let moves ← wordRegisterMoves moves
      pure (.addi destination source 0 :: moves)

def wordCallToRiscV [NeZero width]
    (entry : Word width) (parameters : List Nat) (returns : List Nat)
    (arguments : List Nat) (destinations : List Nat) :
    Option (List (Instruction width)) := do
  if parameters.length != arguments.length || returns.length != destinations.length then
    none
  else
    let parameterMoves ← wordRegisterMoves (parameters.zip arguments)
    let resultMoves ← wordRegisterMoves (destinations.zip returns)
    pure (parameterMoves ++ [.addi 31 0 entry, .jalr 1 31 0] ++ resultMoves)

def wordTailCallToRiscV [NeZero width]
    (entry : Word width) (parameters : List Nat) (arguments : List Nat) :
    Option (List (Instruction width)) := do
  if parameters.length != arguments.length then
    none
  else
    let parameterMoves ← wordRegisterMoves (parameters.zip arguments)
    pure (parameterMoves ++ [.addi 31 0 entry, .jalr 0 31 0])

def wordCallToRiscVWithStack [NeZero width]
    (entry : Word width) (parameters : List Nat) (returns : List Nat)
    (arguments : List Nat) (destinations : List Nat) :
    Option (List (Instruction width)) := do
  if parameters.length != arguments.length || returns.length != destinations.length then
    none
  else
    let parameterMoves ← wordRegisterMoves (parameters.zip arguments)
    let resultMoves ← wordRegisterMoves (destinations.zip returns)
    let stackStep : Word width := BitVec.ofNat width (width / 8)
    pure (parameterMoves ++
      [.addi 30 30 (0 - stackStep), .storeWord 1 30,
       .addi 31 0 entry, .jalr 1 31 0] ++
      resultMoves ++ [.loadWord 1 30, .addi 30 30 stackStep])

structure WordCallContext (width : Nat) [NeZero width] where
  targets : List (Nat × Word width × List Nat × List Nat)

def lookupWordCallTarget [NeZero width] (label : Nat) :
    List (Nat × Word width × List Nat × List Nat) →
      Option (Word width × List Nat × List Nat)
  | [] => none
  | (candidate, entry, parameters, returns) :: targets =>
      if label == candidate then some (entry, parameters, returns)
      else lookupWordCallTarget label targets

def wordFunctionToRiscVWithCalls [NeZero width]
    (context : WordCallContext width) :
  WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .skip => some ([], [])
  | .move _ moves => do
      let instructions ← wordMoveToInstructions moves
      pure (instructions, [])
  | .assign name value => do
      let instructions ← wordExpToInstructions name value
      pure (instructions, [])
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (instructions, [])
  | .inst instruction => do
      let instruction ← wordInstToInstruction instruction
      pure ([instruction], [])
  | .store address value => do
      let instructions ← wordStoreToInstructions address value
      pure (instructions, [])
  | .shareInst operator name address => do
      let instructions ← wordShareInstToInstructions operator name address
      pure (instructions, [])
  | .locValue destination source => do
      let instructions ← wordExpToInstructions destination (.var source)
      pure (instructions, [])
  | .tick => pure ([.addi 0 0 0], [])
  | .call (some ([], _, _, _, _)) (some label) arguments none => do
      let (entry, parameters, returns) ← lookupWordCallTarget label context.targets
      let code ← wordTailCallToRiscV entry parameters arguments
      let returns ← returns.mapM registerOfNat
      pure (code, returns)
  | .call (some (destinations, _, _, _, _)) (some label) arguments none => do
      let (entry, parameters, returns) ← lookupWordCallTarget label context.targets
      let code ← wordCallToRiscVWithStack entry parameters returns arguments destinations
      pure (code, [])
  | .call none (some label) arguments none => do
      let (entry, parameters, returns) ← lookupWordCallTarget label context.targets
      let code ← wordTailCallToRiscV entry parameters arguments
      let returns ← returns.mapM registerOfNat
      pure (code, returns)
  | .ite operator condition rightValue thenBranch elseBranch => do
      let (branchLeft, right, prelude) ←
        wordConditionOperands operator condition rightValue
      let (thenCode, thenReturns) ← wordFunctionToRiscVWithCalls context thenBranch
      let (elseCode, elseReturns) ← wordFunctionToRiscVWithCalls context elseBranch
      if thenReturns != elseReturns then none
      else
        let falseOffset : Word width := BitVec.ofNat width (8 + 4 * thenCode.length)
        let endOffset : Word width := BitVec.ofNat width (4 + 4 * elseCode.length)
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
  | .mustTerminate body => wordFunctionToRiscVWithCalls context body
  | .seq first second => do
      let (firstCode, firstReturns) ← wordFunctionToRiscVWithCalls context first
      if !firstReturns.isEmpty then
        pure (firstCode, firstReturns)
      else
        let (secondCode, secondReturns) ← wordFunctionToRiscVWithCalls context second
        pure (firstCode ++ secondCode, secondReturns)
  | .return _ values => do
      let values ← values.mapM registerOfNat
      pure ([], values)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

mutual
  def wordFunctionToRiscVWithCallsAndLoopsAux [NeZero width]
      (context : WordCallContext width) :
      WordProg (Word width) →
        Option (List (WordControlInstruction width) × List (Fin 32))
    | .break 0 => some ([.breakJump], [])
    | .continue 0 => some ([.continueJump], [])
    | .loop _ body _ => do
        let (bodyCode, bodyReturns) ←
          wordFunctionToRiscVWithCallsAndLoopsAux context body
        if !bodyReturns.isEmpty then none
        else
          let bodyCode ← resolveWordLoopBody bodyCode
          pure (bodyCode.map .instruction ++
            [.instruction (.jal 0 (0 - BitVec.ofNat width (4 * bodyCode.length)))], [])
    | .ite operator condition rightValue thenBranch elseBranch => do
        let (branchLeft, right, prelude) ←
          wordConditionOperands operator condition rightValue
        let (thenCode, thenReturns) ←
          wordFunctionToRiscVWithCallsAndLoopsAux context thenBranch
        let (elseCode, elseReturns) ←
          wordFunctionToRiscVWithCallsAndLoopsAux context elseBranch
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
        wordFunctionToRiscVWithCallsAndLoopsAux context body
    | .seq first second => do
        let (firstCode, firstReturns) ←
          wordFunctionToRiscVWithCallsAndLoopsAux context first
        if !firstReturns.isEmpty then
          pure (firstCode, firstReturns)
        else
          let (secondCode, secondReturns) ←
            wordFunctionToRiscVWithCallsAndLoopsAux context second
          pure (firstCode ++ secondCode, secondReturns)
    | program => do
        let (code, returns) ← wordFunctionToRiscVWithCalls context program
        pure (code.map .instruction, returns)
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
end

def wordFunctionToRiscVWithCallsAndLoops [NeZero width]
    (context : WordCallContext width) :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32)) :=
  fun program => do
    let (code, returns) ← wordFunctionToRiscVWithCallsAndLoopsAux context program
    let code ← wordControlInstructions code
    pure (code, returns)

theorem wordFunctionToRiscVWithCallsAndLoops_break [NeZero width]
    (context : WordCallContext width) :
    wordFunctionToRiscVWithCallsAndLoops context
        ((.loop [] (.break 0) []) : WordProg (Word width)) =
      some ([.jal 0 (BitVec.ofNat width 8),
        .jal 0 (0 - BitVec.ofNat width 4)], []) := by
  simp [wordFunctionToRiscVWithCallsAndLoops,
    wordFunctionToRiscVWithCallsAndLoopsAux, resolveWordLoopBody,
    resolveWordLoopBodyAux, wordControlInstructions]

theorem wordCallToRiscV_shape [NeZero width]
    (entry : Word width) :
    wordCallToRiscV entry [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 entry, .jalr 1 31 0, .addi 4 10 0] := by
  simp [wordCallToRiscV, wordRegisterMoves, registerOfNat]

theorem wordTailCallToRiscV_shape [NeZero width]
    (entry : Word width) :
    wordTailCallToRiscV entry [2] [6] =
      some [.addi 2 6 0, .addi 31 0 entry, .jalr 0 31 0] := by
  simp [wordTailCallToRiscV, wordRegisterMoves, registerOfNat]

theorem wordFunctionToRiscVWithCalls_shape [NeZero width] :
    wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.seq
        (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)
        (.return 0 [4])) =
      some ([.addi 2 6 0, .addi 30 30 (0 - BitVec.ofNat width (width / 8)),
        .storeWord 1 30, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 1 31 0, .addi 4 10 0, .loadWord 1 30,
        .addi 30 30 (BitVec.ofNat width (width / 8))], [4]) := by
  simp [wordFunctionToRiscVWithCalls, wordCallToRiscVWithStack,
    wordRegisterMoves, lookupWordCallTarget, registerOfNat]

theorem wordFunctionToRiscVWithCalls_tailCall [NeZero width] :
    wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.call none (some 7) [6] none) =
      some ([.addi 2 6 0, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 0 31 0], [10]) := by
  simp [wordFunctionToRiscVWithCalls, wordTailCallToRiscV,
    wordRegisterMoves, lookupWordCallTarget, registerOfNat]

theorem wordFunctionToRiscVWithCalls_emptyReturnDestinations [NeZero width] :
    wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.call (some ([], ([], []), .skip, 0, 0)) (some 7) [6] none) =
      some ([.addi 2 6 0, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 0 31 0], [10]) := by
  simp [wordFunctionToRiscVWithCalls, wordTailCallToRiscV,
    wordRegisterMoves, lookupWordCallTarget, registerOfNat]

theorem wordFunctionToRiscVWithCalls_addCarry [NeZero width] :
    wordFunctionToRiscVWithCalls
      ({ targets := [] } : WordCallContext width)
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some ([.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31], []) := by
  simp [wordFunctionToRiscVWithCalls, wordArithToInstructions, registerOfNat]

theorem wordFunctionToRiscVWithCalls_shareInst [NeZero width] :
    wordFunctionToRiscVWithCalls
      ({ targets := [] } : WordCallContext width)
      ((.shareInst .load32 5 (.var 6)) : WordProg (Word width)) =
      some ([.load32 5 6], []) := by
  simp [wordFunctionToRiscVWithCalls, wordShareInstToInstructions,
    wordInstToInstruction, registerOfNat]

/-! Word-level semantic contract for the stack-based call convention.  The
    theorem is parameterized by the argument word, so it can be reused by
    source-to-Word simulations rather than only checking one numeral. -/

theorem evalWordCall_return_general [NeZero width]
    (value : Word width) :
    (evalWordFunctionWithCalls
      [(7, [2], (.return 0 [2] : WordProg (Word width)))] 10
      (writeRegister (zeroState width) 2 value)
      (.call (some ([3], ([], []), .skip, 0, 0)) (some 7) [2] none)).map
        (fun result => readRegister result.1 3) = some value := by
  simp [evalWordFunctionWithCalls, evalWordCall,
    lookupWordFunction, readWordRegisters, bindWordRegisters,
    assignWordRegisters, clearWordRegisters, evalWordFunction,
    registerOfNat, writeRegister, readRegister]

theorem evalWordTailCall_return_general [NeZero width]
    (value : Word width) :
    (evalWordFunctionWithCalls
      [(7, [2], (.return 0 [2] : WordProg (Word width)))] 10
      (writeRegister (zeroState width) 2 value)
      (.call none (some 7) [2] none)).map
        (fun result => result.2) = some [value] := by
  simp [evalWordFunctionWithCalls, evalWordCall,
    lookupWordFunction, readWordRegisters, bindWordRegisters,
    clearWordRegisters, evalWordFunction, registerOfNat,
    writeRegister, readRegister]

end Flapjack.RiscV
