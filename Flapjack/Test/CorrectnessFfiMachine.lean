import Flapjack.RiscV.CorrectnessFfiMachine

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
  all_goals try native_decide
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
  all_goals try native_decide
  simp [ffiMachineHost, ffiMachineWordHandler]

end Flapjack.RiscV
