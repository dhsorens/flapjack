import Flapjack.RiscV.Backend

/-!
RISC-V lowering for the structured loop fragment of Word.

The ordinary selector handles straight-line Word code and conditionals.  This
module adds a small layout-aware pass for `WordProg.loop`: break and continue
are first represented as one-instruction control markers, then resolved once
the body length is known.  This is the same relative-PC convention used by
the existing conditional selector.
-/

namespace Flapjack.RiscV

inductive WordControlInstruction (width : Nat) where
  | instruction (value : Instruction width)
  | breakJump
  | continueJump

def wordControlInstructions [NeZero width] :
    List (WordControlInstruction width) → Option (List (Instruction width))
  | [] => some []
  | .instruction instruction :: instructions => do
      let instructions ← wordControlInstructions instructions
      pure (instruction :: instructions)
  | _ => none

def resolveWordLoopBodyAux [NeZero width] (loopEnd index : Nat)
    : List (WordControlInstruction width) →
      Option (List (Instruction width))
  | [] => some []
  | .instruction instruction :: instructions => do
      let instructions ← resolveWordLoopBodyAux loopEnd (index + 1) instructions
      pure (instruction :: instructions)
  | .breakJump :: instructions => do
      let instructions ← resolveWordLoopBodyAux loopEnd (index + 1) instructions
      pure (.jal 0 (BitVec.ofNat width (4 * (loopEnd - index))) :: instructions)
  | .continueJump :: instructions => do
      let instructions ← resolveWordLoopBodyAux loopEnd (index + 1) instructions
      pure (.jal 0 (0 - BitVec.ofNat width (4 * index)) :: instructions)

def resolveWordLoopBody [NeZero width]
    (body : List (WordControlInstruction width)) :
    Option (List (Instruction width)) :=
  resolveWordLoopBodyAux (body.length + 1) 0 body

mutual
  def wordFunctionToRiscVWithLoopsAux [NeZero width] :
      WordProg (Word width) →
        Option (List (WordControlInstruction width) × List (Fin 32))
    | .break 0 => some ([.breakJump], [])
    | .continue 0 => some ([.continueJump], [])
    | .loop _ body _ => do
        let (bodyCode, bodyReturns) ← wordFunctionToRiscVWithLoopsAux body
        if !bodyReturns.isEmpty then none
        else
          let bodyCode ← resolveWordLoopBody bodyCode
          pure (bodyCode.map .instruction ++
            [.instruction (.jal 0 (0 - BitVec.ofNat width (4 * bodyCode.length)))], [])
    | .ite operator condition rightValue thenBranch elseBranch => do
        let (branchLeft, right, prelude) ←
          wordConditionOperands operator condition rightValue
        let (thenCode, thenReturns) ← wordFunctionToRiscVWithLoopsAux thenBranch
        let (elseCode, elseReturns) ← wordFunctionToRiscVWithLoopsAux elseBranch
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
    | .seq first second => do
        let (firstCode, firstReturns) ← wordFunctionToRiscVWithLoopsAux first
        if !firstReturns.isEmpty then
          pure (firstCode, firstReturns)
        else
          let (secondCode, secondReturns) ← wordFunctionToRiscVWithLoopsAux second
          pure (firstCode ++ secondCode, secondReturns)
    | program => do
        let (code, returns) ← wordFunctionToRiscV program
        pure (code.map .instruction, returns)
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
end

def wordFunctionToRiscVWithLoops [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32)) :=
  fun program => do
    let (code, returns) ← wordFunctionToRiscVWithLoopsAux program
    let code ← wordControlInstructions code
    pure (code, returns)

theorem wordFunctionToRiscVWithLoops_break [NeZero width] :
    wordFunctionToRiscVWithLoops
        ((.loop [] (.break 0) []) : WordProg (Word width)) =
      some ([.jal 0 (BitVec.ofNat width 8),
        .jal 0 (0 - BitVec.ofNat width 4)], []) := by
  simp [wordFunctionToRiscVWithLoops, wordFunctionToRiscVWithLoopsAux,
    resolveWordLoopBody, resolveWordLoopBodyAux, wordControlInstructions]

theorem wordFunctionToRiscVWithLoops_continue [NeZero width] :
    wordFunctionToRiscVWithLoops
        ((.loop [] (.continue 0) []) : WordProg (Word width)) =
      some ([.jal 0 0, .jal 0 (0 - BitVec.ofNat width 4)], []) := by
  simp [wordFunctionToRiscVWithLoops, wordFunctionToRiscVWithLoopsAux,
    resolveWordLoopBody, resolveWordLoopBodyAux, wordControlInstructions]

theorem execute_lowered_loop_break :
    (wordFunctionToRiscVWithLoops
        ((.loop [] (.break 0) []) : WordProg (Word 64))).bind
        (fun result =>
          (executeCode 10 (0 : Word 64) result.1 (zeroState 64)).map
            (fun state => state.pc)) =
      some (BitVec.ofNat 64 8) := by
  decide +kernel

end Flapjack.RiscV
