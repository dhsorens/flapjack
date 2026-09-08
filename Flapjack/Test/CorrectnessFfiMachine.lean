import Flapjack.RiscV.CorrectnessFfiMachine
import Flapjack.RiscV.CorrectnessPipelineFfi

/-!
Concrete regression for the generated FFI ABI sequence.  The host is an
identity transition on the marshalled machine state; the abstract handler
models the same ABI writes so the theorem checks the complete instruction
sequence, including service selection and `ECALL` dispatch.
-/

namespace Flapjack.RiscV

def ffiMachineState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 2 10) 3 20) 4 30) 5 40

def ffiMachineHost : WordFfiHost 64 :=
  fun service _ _ _ _ state =>
    if service == 7 then some state else none

def ffiMachineWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun function _ _ _ _ state =>
    if function == "echo" then
      some (executeInstructions state
        [.addi 10 2 (0#64), .addi 11 3 (0#64),
         .addi 12 4 (0#64), .addi 13 5 (0#64),
         .addi 14 0 (BitVec.ofNat 64 7)])
    else none

example :
    (labCompileAsm ({ services := [("echo", 7)] } : WordFfiContext)
      2 [] 0 (.callFfi "echo")).bind
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState) =
      some (executeInstructions ffiMachineState
        [.addi 14 0 (BitVec.ofNat 64 7)]) := by
  apply labCompileAsm_callFfi_execute_agreement
    ({ services := [("echo", 7)] } : WordFfiContext)
    ffiMachineHost ffiMachineState 2 [] 0 "echo" 7
    (some (executeInstructions ffiMachineState
      [.addi 14 0 (BitVec.ofNat 64 7)]))
  all_goals try decide
  simp [ffiMachineHost]

example :
    (compileLabSection ({ services := [("echo", 7)] } : WordFfiContext)
      ⟨2, [.labAsm (.callFfi "echo") [] 0]⟩).bind
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState) =
      some (executeInstructions ffiMachineState
        [.addi 14 0 (BitVec.ofNat 64 7)]) := by
  apply compileLabSection_callFfi_execute_agreement
    ({ services := [("echo", 7)] } : WordFfiContext)
    ffiMachineHost ffiMachineState 2 "echo" 7
    (some (executeInstructions ffiMachineState
      [.addi 14 0 (BitVec.ofNat 64 7)]))
  all_goals try decide
  simp [ffiMachineHost]

example :
    (compileLabProgram ({ services := [("echo", 7)] } : WordFfiContext)
      [⟨2, [.labAsm (.callFfi "echo") [] 0]⟩]).bind
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState) =
      some (executeInstructions ffiMachineState
        [.addi 14 0 (BitVec.ofNat 64 7)]) := by
  apply compileLabProgram_callFfi_execute_agreement
    ({ services := [("echo", 7)] } : WordFfiContext)
    ffiMachineHost ffiMachineState 2 "echo" 7
    (some (executeInstructions ffiMachineState
      [.addi 14 0 (BitVec.ofNat 64 7)]))
  all_goals try decide
  simp [ffiMachineHost]

example :
    (wordFfiToRiscV ({ services := [("echo", 7)] } : WordFfiContext)
      "echo" 2 3 4 5).bind (fun code =>
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState code).map
          (fun result => (result, ([] : List (Word 64))))) =
      evalWordFfi ffiMachineWordHandler 1 ffiMachineState
        (.ffi "echo" 2 3 4 5 ([], [])) := by
  apply wordFfiToRiscV_execute_agreement
    ({ services := [("echo", 7)] } : WordFfiContext)
    ffiMachineHost ffiMachineWordHandler ffiMachineState "echo"
    2 3 4 5 7 2 3 4 5
  all_goals try decide
  simp [ffiMachineHost, ffiMachineWordHandler]

example :
    (wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := [("echo", 7)] } : WordCallFfiContext 64)
      (.ffi "echo" 2 3 4 5 ([], []))).bind (fun result =>
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState result.1).map
          (fun final => (final, ([] : List (Word 64))))) =
      evalWordFunctionWithCallsAndFfi [] ffiMachineWordHandler 1 ffiMachineState
        (.ffi "echo" 2 3 4 5 ([], [])) := by
  apply wordFunctionToRiscVWithCallsAndFfi_ffi_simulation
    ({ services := [("echo", 7)] } : WordFfiContext)
    ffiMachineHost ffiMachineWordHandler ffiMachineState "echo"
    2 3 4 5 7 2 3 4 5
  all_goals try decide
  simp [ffiMachineHost, ffiMachineWordHandler]

example :
    (compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfig
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat)).bind
        (executeInstructionsWithFfi ffiMachineHost ffiMachineState) =
      ffiMachineHost 7 (readRegister ffiMachineState 4)
        (readRegister ffiMachineState 5) (readRegister ffiMachineState 6)
        (readRegister ffiMachineState 7)
        (executeInstructions ffiMachineState
          [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
            .addi 0 0 (BitVec.ofNat 64 28),
            .addi 14 0 (BitVec.ofNat 64 7)]) := by
  apply executeCompiledPipelineFfi
  simp [ffiMachineState, zeroState, readRegister, writeRegister]

example [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfi context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState) :
    (wordFunctionToRiscVWithCallsAndFfi context (.seq first second)).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, returns))) =
      some (finalState, returns) := by
  exact wordFunctionToRiscVWithCallsAndFfi_seq_simulation context host state
    firstState finalState first second firstCode secondCode returns
    hfirstCompile hsecondCompile hfirstExec hsecondExec

end Flapjack.RiscV
