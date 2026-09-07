import Flapjack.RiscV.CorrectnessFfiMachine
import Flapjack.RiscV.Lab

/-!
# Pipeline FFI machine correctness

This module closes the small gap between the executable
Word-to-Stack/StackRemove/LabLang pipeline and the RISC-V FFI machine
boundary.  The compiler theorem is concrete about the register allocation,
while the host and initial machine state remain abstract.
-/

namespace Flapjack.RiscV

def pipelineFfiWordConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7)]
    scratch := 31
    stackBase := 21 }

def pipelineFfiStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

theorem compileWordProgramNatToRiscV_pipeline_ffi :
    compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfig
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat) =
      some [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
        .addi 0 0 (BitVec.ofNat 64 28),
        .addi 14 0 (BitVec.ofNat 64 7), .ecall] := by
  decide +kernel

theorem executeCompiledPipelineFfi
    (host : WordFfiHost 64) (state : State 64)
    (hzero : readRegister state 0 = 0) :
    (compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfig
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat)).bind
        (executeInstructionsWithFfi host state) =
      host 7 (readRegister state 4) (readRegister state 5)
        (readRegister state 6) (readRegister state 7)
        (executeInstructions state
          [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
            .addi 0 0 (BitVec.ofNat 64 28),
            .addi 14 0 (BitVec.ofNat 64 7)]) := by
  rw [compileWordProgramNatToRiscV_pipeline_ffi]
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  simp [executeInstructionsWithFfi, executeWithFfi, executeInstructions,
    execute, writeRegister, readRegister, nextPc, hzero']

end Flapjack.RiscV
