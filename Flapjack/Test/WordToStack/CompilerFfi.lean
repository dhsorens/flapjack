import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for the compiler-level FFI equation.  The theorem is applied
    to a nontrivial location map so the test exercises the emitted moves and
    the option-valued compiler result together. -/

namespace Flapjack.RiscV

def compilerFfiConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .stack 2),
      (2, .register 6), (3, .stack 4)]
    scratch := 31
    stackBase := 20 }

def compilerFfiState : WordStackMachineState 8 :=
  { registers := fun register => if register = 4 then 17 else
      if register = 6 then 23 else 0
    stack := fun slot => if slot = 22 then 29 else
      if slot = 24 then 31 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def compilerFfiHost : StackMachineFfiHandler 8 :=
  fun _ configuration configurationLength array arrayLength state =>
    some (wordStackMachineWriteRegister state 7
      (configuration + configurationLength + array + arrayLength))

example :
    (wordToStackProgWord compilerFfiConfig
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg (Word 8))).bind
        (fun program => evalStackProgFuelWithCodeAndFfi compilerFfiHost 6
          (fun _ => none) compilerFfiState program) =
      (compilerFfiHost "echo" 17 29 23 31
        (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister
            (wordStackMachineWriteRegister
              (wordStackMachineWriteRegister compilerFfiState 10 17) 11 29)
            12 23)
          13 31)).map .normal := by
  apply evalStackProgFuelWithCodeAndFfi_wordToStackProgWord_ffi
    (host := compilerFfiHost) (fuel := 1) (code := fun _ => none)
    (config := compilerFfiConfig) (state := compilerFfiState)
    (state1 := wordStackMachineWriteRegister compilerFfiState 10 17)
    (state2 := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister compilerFfiState 10 17) 11 29)
    (state3 := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister compilerFfiState 10 17) 11 29) 12 23)
    (final := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister compilerFfiState 10 17) 11 29) 12 23)
      13 31)
    (function := "echo") (configuration := 0)
    (configurationLength := 1) (array := 2) (arrayLength := 3)
    (live := ([], []))
    (configurationLocation := .register 4)
    (configurationLengthLocation := .stack 2)
    (arrayLocation := .register 6)
    (arrayLengthLocation := .stack 4)
    (configurationMove := .arith .or 10 4 4)
    (configurationLengthMove := .stackLoad 11 22)
    (arrayMove := .arith .or 12 6 6)
    (arrayLengthMove := .stackLoad 13 24)
    (configurationValue := 17) (configurationLengthValue := 29)
    (arrayValue := 23) (arrayLengthValue := 31)
  all_goals simp [compilerFfiConfig, compilerFfiState, wordStackLocation,
    lookupNatInfo, wordStackFfiSourcesSafe, wordStackFfiSourceSafe,
    wordStackFfiRegisterSafe, wordStackFfiMove, wordStackMachineValue,
    wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
    wordStackMachineBinOp]

end Flapjack.RiscV
