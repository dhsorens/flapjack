import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness
import Flapjack.RiscV.CorrectnessWordToStack

namespace Flapjack.RiscV

def ffiStackShapeConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .stack 2), (3, .stack 3)]
    scratch := 31
    stackBase := 10 }

example :
    wordStackFfi ffiStackShapeConfig "echo" 0 1 2 3 =
      some (wordStackJoin (.arith .or 10 4 4)
        (wordStackJoin (.arith .or 11 5 5)
          (wordStackJoin (.stackLoad 12 12)
            (wordStackJoin (.stackLoad 13 13)
              (.ffi "echo" 10 11 12 13 0)))) : StackProg Nat) := by
  apply wordStackFfi_eq_join
  · decide
  all_goals simp [ffiStackShapeConfig, wordStackFfiMove,
    wordStackLocation, wordStackOffset, lookupNatInfo]
example [NeZero width]
    (state final : WordStackState width)
    (heval : (wordStackMove (α := Nat)
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1).bind
      (evalWordStackBasic state) = some final) :
    wordStackValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } final 0 =
      wordStackValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } state 1 := by
  apply evalWordStackBasic_move_preserves_value
    (destinationLocation := .stack 2) (sourceLocation := .register 5)
  · rfl
  · rfl
  · simp
  · simp
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackMove (α := Nat)
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } final 0 =
      wordStackMachineValue
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } state 1 := by
  apply evalWordStackMachine_move_preserves_value
    (destinationLocation := .stack 2) (sourceLocation := .register 5)
  · rfl
  · rfl
  · simp
  · simp
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.memory := by
  apply evalWordStackMachine_load_preserves_value
    (destinationLocation := .register 4) (addressLocation := .register 5)
  · rfl
  · rfl
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackCompileLoadNat
        { locations := [(0, .stack 2)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 (.const 37)).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 2)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (state.memory (BitVec.ofNat width 37)) := by
  apply evalWordStackMachine_load_const_assignment
    (destination := 0) (address := 37) (destinationLocation := .stack 2)
  · rfl
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (addressValue : Word width)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackCompileLoadNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 (.var 1)).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (state.memory addressValue) := by
  apply evalWordStackMachine_load_assignment
    (destination := 0) (address := 1)
    (destinationLocation := .stack 2) (addressLocation := .stack 3)
  · rfl
  · rfl
  · exact haddressValue
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.memory := by
  apply evalWordStackMachine_load_preserves_value
    (destinationLocation := .stack 2) (addressLocation := .stack 3)
  · rfl
  · rfl
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.memory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_store_preserves_memory
    (config := config)
    (state := state) (final := final) (source := 0) (address := 1)
    (sourceLocation := .register 4) (addressLocation := .register 5)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config]) (hsafe := by simp [wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackCompileStoreNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        (.var 1) (.var 0)).bind (evalWordStackMachine state) = some final) :
    final.memory addressValue = sourceValue := by
  apply evalWordStackMachine_store_assignment
    (config :=
      { locations := [(0, .stack 2), (1, .stack 3)],
        scratch := 31, stackBase := 10, addressScratch := 29 })
    (source := 0) (address := 1)
    (sourceLocation := .stack 2) (addressLocation := .stack 3)
    (sourceValue := sourceValue) (addressValue := addressValue)
  · rfl
  · rfl
  · exact hsourceValue
  · exact haddressValue
  · decide
  · decide
  · exact heval

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.memory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 2), (1, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_store_preserves_memory
    (config := config)
    (state := state) (final := final) (source := 0) (address := 1)
    (sourceLocation := .stack 2) (addressLocation := .stack 3)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config]) (hsafe := by simp [config, wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (dividendValue divisorValue : Word width)
    (hdividendValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some dividendValue)
    (hdivisorValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (heval : (wordStackDivInst
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 1 2).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_div_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (dividend := 1) (divisor := 2)
    (destinationLocation := .register 4)
    (dividendLocation := .register 5) (divisorLocation := .register 6)
    (dividendValue := dividendValue) (divisorValue := divisorValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividend := by simp [config, wordStackLocation, lookupNatInfo])
    (hdivisor := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividendValue := by simpa [config] using hdividendValue)
    (hdivisorValue := by simpa [config] using hdivisorValue)
    (hdivisorNonzero := hdivisorNonzero)
    (hscratch := by simp [config])
    (hdestinationSafe := by simp [config, wordStackDivLocationSafe])
    (hdividendSafe := by simp [config, wordStackDivLocationSafe])
    (hdivisorSafe := by simp [config, wordStackDivLocationSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (dividendValue divisorValue : Word width)
    (hdividendValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some dividendValue)
    (hdivisorValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (heval : (wordStackDivInst
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 1 2).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_div_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (dividend := 1) (divisor := 2)
    (destinationLocation := .stack 1)
    (dividendLocation := .stack 2) (divisorLocation := .stack 3)
    (dividendValue := dividendValue) (divisorValue := divisorValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividend := by simp [config, wordStackLocation, lookupNatInfo])
    (hdivisor := by simp [config, wordStackLocation, lookupNatInfo])
    (hdividendValue := by simpa [config] using hdividendValue)
    (hdivisorValue := by simpa [config] using hdivisorValue)
    (hdivisorNonzero := hdivisorNonzero)
    (hscratch := by simp [config])
    (hdestinationSafe := by simp [wordStackDivLocationSafe])
    (hdividendSafe := by simp [wordStackDivLocationSafe])
    (hdivisorSafe := by simp [wordStackDivLocationSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileBinaryNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .add (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineBinOp .add leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_binary_assignment
    (config := config) (state := state) (final := final)
    (operator := .add) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .register 4)
    (leftLocation := .register 5) (rightLocation := .register 6)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileBinaryNat
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .xor (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineBinOp .xor leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_binary_assignment
    (config := config) (state := state) (final := final)
    (operator := .xor) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .stack 1)
    (leftLocation := .stack 2) (rightLocation := .stack 3)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileShiftNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .lsl (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineShift .lsl leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shift_assignment
    (config := config) (state := state) (final := final)
    (operator := .lsl) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .register 4)
    (leftLocation := .register 5) (rightLocation := .register 6)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (leftValue rightValue : Word width)
    (hleftValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some leftValue)
    (hrightValue : wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 2 = some rightValue)
    (heval : (wordStackCompileShiftNat
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        0 .asr (.var 1) (.var 2)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 = some (wordStackMachineShift .asr leftValue rightValue) := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 1), (1, .stack 2), (2, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shift_assignment
    (config := config) (state := state) (final := final)
    (operator := .asr) (destination := 0) (left := 1) (right := 2)
    (destinationLocation := .stack 1)
    (leftLocation := .stack 2) (rightLocation := .stack 3)
    (leftValue := leftValue) (rightValue := rightValue)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hleft := by simp [config, wordStackLocation, lookupNatInfo])
    (hright := by simp [config, wordStackLocation, lookupNatInfo])
    (hleftValue := by simpa [config] using hleftValue)
    (hrightValue := by simpa [config] using hrightValue)
    (hsafe := by simp [config, wordStackBinaryLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackSharedMemoryInst
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .load 0 1).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        final 0 =
      (wordStackMachineValue
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1).map state.sharedMemory := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4), (1, .register 5)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shared_load_preserves_value
    (config := config) (state := state) (final := final)
    (destination := 0) (address := 1)
    (destinationLocation := .register 4) (addressLocation := .register 5)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hscratch := by simp [config])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue addressValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 0 = some sourceValue)
    (haddressValue : wordStackMachineValue
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        state 1 = some addressValue)
    (heval : (wordStackSharedMemoryInst
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        .store 0 1).bind (evalWordStackMachine state) = some final) :
    final.sharedMemory addressValue = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 2), (1, .stack 3)],
      scratch := 31, stackBase := 10, addressScratch := 29 }
  exact evalWordStackMachine_shared_store_preserves_memory
    (config := config) (state := state) (final := final)
    (source := 0) (address := 1)
    (sourceLocation := .stack 2) (addressLocation := .stack 3)
    (sourceValue := sourceValue) (addressValue := addressValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (haddress := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (haddressValue := by simpa [config] using haddressValue)
    (hscratch := by simp [config])
    (hsafe := by simp [config, wordStackStoreLocationsSafe])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (heval : (wordStackCompileExpNat
        { locations := [(0, .register 4)], scratch := 31, stackBase := 10 }
        0 (.lookup .currHeap)).bind
        (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(0, .register 4)], scratch := 31, stackBase := 10 }
        final 0 = some (state.stores .currHeap) := by
  let config : WordStackConfig :=
    { locations := [(0, .register 4)], scratch := 31, stackBase := 10 }
  exact evalWordStackMachine_lookup_assignment
    (config := config) (state := state) (final := final)
    (destination := 0) (store := .currHeap) (stackStore := .currHeap)
    (destinationLocation := .register 4)
    (hdestination := by simp [config, wordStackLocation, lookupNatInfo])
    (hstore := by simp [wordStackStoreNameNat])
    (by simpa [config] using heval)

example [NeZero width]
    (state final : WordStackMachineState width)
    (sourceValue : Word width)
    (hsourceValue : wordStackMachineValue
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        state 0 = some sourceValue)
    (heval : (wordStackSetNat
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        (.temp 4) (.var 0)).bind
        (evalWordStackMachine state) = some final) :
    final.stores (.temp 4) = sourceValue := by
  let config : WordStackConfig :=
    { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
  exact evalWordStackMachine_set_preserves_value
    (config := config) (state := state) (final := final)
    (store := .temp 4) (stackStore := .temp 4) (source := 0)
    (sourceLocation := .stack 2) (sourceValue := sourceValue)
    (hsource := by simp [config, wordStackLocation, lookupNatInfo])
    (hsourceValue := by simpa [config] using hsourceValue)
    (hstore := by simp [wordStackStoreNameNat])
    (by simpa [config] using heval)


end Flapjack.RiscV
