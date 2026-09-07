import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for state-threaded FFI execution correctness. -/

namespace Flapjack.RiscV

def statefulFfiCorrectnessConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .stack 2),
      (2, .register 6), (3, .stack 4)]
    scratch := 31
    stackBase := 20 }

def statefulFfiCorrectnessMachine : WordStackMachineState 8 :=
  { registers := fun register => if register = 4 then 17 else
      if register = 6 then 23 else 0
    stack := fun slot => if slot = 22 then 29 else
      if slot = 24 then 31 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def statefulFfiCorrectnessBitmap : WordStackBitmapState :=
  { data := [4, 12]
    length := 2 }

def statefulFfiCorrectnessHost : StackMachineFfiHandler 8 :=
  fun _ configuration configurationLength array arrayLength state =>
    some (wordStackMachineWriteRegister state 7
      (configuration + configurationLength + array + arrayLength))

example :
    (wordToStackProgNatWithBitmapBuilder statefulFfiCorrectnessConfig
      (fun live => live) 2 26 4 64 none statefulFfiCorrectnessBitmap
      (.ffi "echo" 0 1 2 3 ([], [4]) : WordProg Nat)).bind
        (fun result =>
          (evalStackProgFuelWithCodeAndFfi statefulFfiCorrectnessHost 6
            (fun _ => none) statefulFfiCorrectnessMachine result.1).map
            (fun control => (control, result.2))) =
      (statefulFfiCorrectnessHost "echo" 17 29 23 31
        (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister
            (wordStackMachineWriteRegister
              (wordStackMachineWriteRegister
                statefulFfiCorrectnessMachine 10 17) 11 29) 12 23)
            13 31)).map
        (fun machine => (.normal machine, statefulFfiCorrectnessBitmap)) := by
  apply evalStackProgFuelWithCodeAndFfi_wordToStackProgNatWithBitmapBuilder_ffi
    (host := statefulFfiCorrectnessHost) (fuel := 1)
    (code := fun _ => none)
    (config := statefulFfiCorrectnessConfig) (bitmapBuilder := fun live => live)
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (bitmapState := statefulFfiCorrectnessBitmap)
    (machineState := statefulFfiCorrectnessMachine)
    (state1 := wordStackMachineWriteRegister
      statefulFfiCorrectnessMachine 10 17)
    (state2 := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister statefulFfiCorrectnessMachine 10 17)
      11 29)
    (state3 := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister statefulFfiCorrectnessMachine 10 17)
        11 29) 12 23)
    (final := wordStackMachineWriteRegister
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister statefulFfiCorrectnessMachine 10 17)
          11 29) 12 23) 13 31)
    (function := "echo") (configuration := 0)
    (configurationLength := 1) (array := 2) (arrayLength := 3)
    (live := ([], [4]))
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
  all_goals simp [statefulFfiCorrectnessConfig,
    statefulFfiCorrectnessMachine,
    wordStackFfiSourcesSafe, wordStackFfiSourceSafe,
    wordStackFfiRegisterSafe, wordStackFfiMove, wordStackMachineValue,
    wordStackLocation, lookupNatInfo, wordStackOffset,
    evalWordStackMachine, wordStackMachineWriteRegister,
    wordStackMachineBinOp]

end Flapjack.RiscV
