import Flapjack.RiscV.CorrectnessFfiMachine

namespace Flapjack.RiscV

def ffiLoopRiscVContext : WordCallFfiContext 64 :=
  { targets := [], services := [("echo", 7)] }

def ffiLoopRiscVProgram : WordProg (Word 64) :=
  .loop []
    (.seq (.ffi "echo" 1 2 3 4 ([], [])) (.break 0))
    []

def ffiLoopRiscVHost : WordFfiHost 64 :=
  fun _ _ _ _ _ state => some { state with pc := nextPc state }

def ffiLoopRiscVCode : List (Instruction 64) :=
  [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
   .addi 14 0 (BitVec.ofNat 64 7), .ecall,
   .jal 0 (BitVec.ofNat 64 8),
   .jal 0 (0 - BitVec.ofNat 64 28)]

theorem ffiLoopRiscVCompiler_shape :
    wordFunctionToRiscVWithCallsAndFfiAndLoops ffiLoopRiscVContext
        ffiLoopRiscVProgram =
      some (ffiLoopRiscVCode, []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
    ffiLoopRiscVProgram, ffiLoopRiscVContext,
    wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, registerOfNat,
    resolveWordLoopBody, resolveWordLoopBodyAux, wordControlInstructions,
    ffiLoopRiscVCode]

/-! The emitted FFI action is executed before the resolved break jump.  The
    return PC is the first instruction after the loop, so this is a small
    machine-level simulation of the loop body’s normal break path. -/
theorem ffiLoopRiscV_execution :
    (wordFunctionToRiscVWithCallsAndFfiAndLoops ffiLoopRiscVContext
      ffiLoopRiscVProgram).bind (fun result =>
        (executeCodeUntilWithFfi ffiLoopRiscVHost 20 (0 : Word 64)
          (BitVec.ofNat 64 32) result.1 (zeroState 64)).map State.pc) =
      some (BitVec.ofNat 64 32) := by
  rw [ffiLoopRiscVCompiler_shape]
  decide +kernel

def ffiContinueRiscVProgram : WordProg (Word 64) :=
  .loop []
    (.seq (.ffi "echo" 1 2 3 4 ([], [])) (.continue 0))
    []

def ffiContinueRiscVCode : List (Instruction 64) :=
  [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
   .addi 14 0 (BitVec.ofNat 64 7), .ecall,
   .jal 0 (0 - BitVec.ofNat 64 24),
   .jal 0 (0 - BitVec.ofNat 64 28)]

theorem ffiContinueRiscVCompiler_shape :
    wordFunctionToRiscVWithCallsAndFfiAndLoops ffiLoopRiscVContext
        ffiContinueRiscVProgram =
      some (ffiContinueRiscVCode, []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
    ffiContinueRiscVProgram, ffiLoopRiscVContext,
    wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, registerOfNat,
    resolveWordLoopBody, resolveWordLoopBodyAux, wordControlInstructions,
    ffiContinueRiscVCode]

end Flapjack.RiscV
