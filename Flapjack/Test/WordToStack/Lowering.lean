import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness

-- FFI ABI regressions are kept here with the other Word-to-Stack tests.

namespace Flapjack.RiscV

example :
    wordStackMove
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.arith .or 4 5 5 : StackProg Nat) := by
  exact wordStackMove_registers

example :
    wordStackMove
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.arith .or 31 5 5) (.stackStore 31 12) : StackProg Nat) := by
  exact wordStackMove_register_to_spill

example :
    wordToStackProg
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 }
        ((.seq (.assign 0 (.var 1)) (.locValue 1 0)) : WordProg Nat) =
      some (.seq
        (.seq (.arith .or 31 5 5) (.stackStore 31 12))
        (.seq (.stackLoad 31 12) (.arith .or 5 31 31)) : StackProg Nat) := by
  simp [wordToStackProg, wordStackMove, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackMemoryInst
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .load32 0 1 =
      some (.seq (.stackLoad 29 12) (.inst (.mem .load32 4 29)) : StackProg Nat) := by
  exact wordStackMemoryInst_load_spill_address

example :
    wordStackMemoryInst
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .store32 0 1 =
      some (.seq (.stackLoad 29 12)
        (.seq (.stackLoad 31 13) (.inst (.mem .store32 31 29))) : StackProg Nat) := by
  exact wordStackMemoryInst_store_spill_value_and_address

example :
    wordStackDivInst
        { locations := [(0, .stack 3), (1, .stack 2), (2, .register 6)],
          scratch := 31, stackBase := 10 } 0 1 2 =
      some (.seq (.stackLoad 31 12)
        (.seq (.inst (.arith (.div 31 31 6)))
          (.stackStore 31 13)) : StackProg Nat) := by
  exact wordStackDivInst_spill_operands

example :
    wordToStackProg
        { locations := [(0, .stack 2), (1, .stack 3),
            (2, .stack 4), (3, .stack 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat) =
      some (.seq (.stackLoad 31 14)
        (.seq (.stackLoad 29 15)
          (.seq (.inst (.arith (.longMul 28 31 31 29)))
            (.seq (.stackStore 28 12) (.stackStore 31 13)))) : StackProg Nat) := by
  simp [wordToStackProg, wordToStackInst, wordStackArithInst,
    wordStackLongMulInst, wordStackLongMulLocationsSafe,
    wordStackLongMulLocationSafe, wordStackLongMulMoveToPhysical,
    wordStackLongMulMoveFromPhysical, wordStackLocation, wordStackOffset,
    wordStackJoin, wordSpecialArithLocationsSafe, lookupNatInfo]

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5)],
        scratch := 31, stackBase := 10, addressScratch := 29 }
    let state : WordStackMachineState 8 :=
      { registers := fun _ => 0,
        stack := fun offset =>
          if offset = 14 then BitVec.ofNat 8 3
          else if offset = 15 then BitVec.ofNat 8 4 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    (evalWordStackMachine state
      ((wordToStackProg config
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat)).getD .skip)).map
      (fun state =>
        (wordStackMachineValue config state 0,
          wordStackMachineValue config state 1)) =
      some (some (BitVec.ofNat 8 0), some (BitVec.ofNat 8 12)) := by
  decide +kernel

example :
    let state : State 8 :=
      writeRegister
        (writeRegister
          (writeRegister (zeroState 8) 29 255) 28 1) 27 1
    let final := executeInstructions state
      [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
        .add 27 27 31, .sltu 31 27 31, .or 28 28 31]
    (readRegister final 27, readRegister final 28) =
      (BitVec.ofNat 8 1, BitVec.ofNat 8 1) := by
  decide

example [NeZero width] (state : State width)
    (zero : readRegister state 0 = 0) :
    (readRegister
        (executeInstructions state
          [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
            .add 27 27 31, .sltu 31 27 31, .or 28 28 31]) 27,
      readRegister
        (executeInstructions state
          [.sltu 31 0 27, .add 27 29 28, .sltu 28 27 28,
            .add 27 27 31, .sltu 31 27 31, .or 28 28 31]) 28) =
      addCarryWords (readRegister state 29) (readRegister state 28)
        (readRegister state 27) := by
  apply executeInstructions_addCarry_general state 27 28 29 28 27 zero
  all_goals decide

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5), (4, .stack 6)],
        scratch := 31, stackBase := 10, addressScratch := 29,
        specialScratch := 28, carryScratch := 27 }
    wordToStackProg config
      ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat) =
      some (.seq (.stackLoad 29 14)
        (.seq (.stackLoad 28 15)
          (.seq (.stackLoad 27 16)
            (.seq (.inst (.arith (.addCarry 27 28 29 28 27)))
              (.seq (.stackStore 27 12) (.stackStore 28 13))))) : StackProg Nat) := by
  simp [wordToStackProg, wordToStackInst, wordStackArithInst,
    wordStackAddCarryInst, wordStackAddCarryLocationSafe,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset,
    wordSpecialArithLocationsSafe, lookupNatInfo]

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3),
          (2, .stack 4), (3, .stack 5), (4, .stack 6)],
        scratch := 31, stackBase := 10, addressScratch := 29,
        specialScratch := 28, carryScratch := 27 }
    let state : WordStackMachineState 8 :=
      { registers := fun _ => 0,
        stack := fun offset =>
          if offset = 14 then BitVec.ofNat 8 255
          else if offset = 15 then BitVec.ofNat 8 1
          else if offset = 16 then BitVec.ofNat 8 1 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    (evalWordStackMachine state
      ((wordToStackProg config
        ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat)).getD .skip)).map
      (fun state =>
        (wordStackMachineValue config state 0,
          wordStackMachineValue config state 1)) =
      some (some (BitVec.ofNat 8 1), some (BitVec.ofNat 8 1)) := by
  decide +kernel

example :
    wordToStackProg
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10 }
        ((.ite .equal 0 (.reg 1) .skip .skip) : WordProg Nat) =
      some (.seq (.seq (.stackLoad 31 12) (.stackLoad 29 13))
        (.ite .equal 31 (.reg 29) .skip .skip) : StackProg Nat) := by
  simp [wordToStackProg, wordStackConditionOperands, wordStackReadRegister,
    wordStackJoin, wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordToStackProg
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        ((.return 0 [0]) : WordProg Nat) =
      some (.seq (.seq (.stackLoad 31 12) (.arith .or 2 31 31)) (.return 2) :
        StackProg Nat) := by
  simp [wordToStackProg, wordStackReturn, wordStackMovesToPhysical,
    wordStackPhysicalMovesTo, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMove, wordStackLocation,
    wordStackOffset, lookupNatInfo, wordStackJoin]

example :
    wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        ((.set .currHeap (.var 0)) : WordProg Nat) =
      some (.set .currHeap 5 : StackProg Nat) := by
  simp [wordToStackProg, wordStackStoreName, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin]

example :
    wordToStackProg
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 }
        ((.shareInst .load32 0 (.var 1)) : WordProg Nat) =
      some (.shMem .load32 4 5 : StackProg Nat) := by
  simp [wordToStackProg, wordStackSharedMemoryInst,
    wordStackSharedLoadInst, wordStackLocation, lookupNatInfo]

example :
    wordToStackProg
        { locations := [], scratch := 31, stackBase := 10 }
        ((.loop [] (.break 0) []) : WordProg Nat) =
      some (.loop (.break 0) : StackProg Nat) := by
  simp [wordToStackProg]

example :
    wordToStackProg
        { locations := [(2, .register 4), (3, .stack 2),
            (4, .register 6), (5, .register 7)],
          scratch := 31, stackBase := 10 }
        ((.ffi "sum" 2 3 4 5 ([], [])) : WordProg Nat) =
      some (.seq (.arith .or 10 4 4)
        (.seq (.stackLoad 11 12)
          (.seq (.arith .or 12 6 6)
            (.seq (.arith .or 13 7 7)
              (.ffi "sum" 10 11 12 13 0))))) := by
  simp [wordToStackProg, wordStackFfi, wordStackFfiSourcesSafe,
    wordStackFfiSourceSafe, wordStackFfiRegisterSafe, wordStackFfiMove,
    wordStackLocation,
    wordStackOffset, lookupNatInfo, wordStackJoin]

example (state final : WordStackMachineState 8)
    (heval : (wordStackFfiMove
      { locations := [(2, .register 4)], scratch := 31, stackBase := 10 }
      2 10).bind (evalWordStackMachine state) = some final) :
    final.registers 10 =
      wordStackMachineValue
        { locations := [(2, .register 4)], scratch := 31, stackBase := 10 }
        state 2 := by
  apply evalWordStackMachine_ffi_move_preserves_value
    (sourceLocation := .register 4)
  · decide
  · decide
  · exact heval

example (state final : WordStackMachineState 8)
    (heval : (wordStackFfiMove
      { locations := [(2, .stack 2)], scratch := 31, stackBase := 10 }
      2 10).bind (evalWordStackMachine state) = some final) :
    final.registers 10 =
      wordStackMachineValue
        { locations := [(2, .stack 2)], scratch := 31, stackBase := 10 }
        state 2 := by
  apply evalWordStackMachine_ffi_move_preserves_value
    (sourceLocation := .stack 2)
  · decide
  · decide
  · exact heval

example (state final : WordStackMachineState 8)
    (heval : (wordStackFfiMove
      { locations := [(2, .register 4), (3, .register 6)],
        scratch := 31, stackBase := 10 }
      2 10).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue
        { locations := [(2, .register 4), (3, .register 6)],
          scratch := 31, stackBase := 10 }
        final 3 =
      wordStackMachineValue
        { locations := [(2, .register 4), (3, .register 6)],
          scratch := 31, stackBase := 10 }
        state 3 := by
  apply evalWordStackMachine_ffi_move_preserves_other_value
    (source := 2) (destination := 10) (other := 3)
    (sourceLocation := .register 4) (otherLocation := .register 6)
  · decide
  · decide
  · decide
  · decide
  · exact heval

example (config : WordStackConfig)
    (state state1 state2 state3 final : WordStackMachineState 8)
    (configuration configurationLength array arrayLength : Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hsafe : ∀ location, location ∈
      [configurationLocation, configurationLengthLocation, arrayLocation,
        arrayLengthLocation] →
      ∀ destination, destination ∈ [10, 11, 12, 13] →
        location ≠ .register destination)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine state) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    some (final.registers 10) = wordStackMachineValue config state configuration ∧
    some (final.registers 11) = wordStackMachineValue config state configurationLength ∧
    some (final.registers 12) = wordStackMachineValue config state array ∧
    some (final.registers 13) = wordStackMachineValue config state arrayLength := by
  exact evalWordStackMachine_ffi_argument_moves
    (config := config) (state := state) (state1 := state1)
    (state2 := state2) (state3 := state3) (final := final)
    (configuration := configuration) (configurationLength := configurationLength)
    (array := array) (arrayLength := arrayLength)
    (configurationLocation := configurationLocation)
    (configurationLengthLocation := configurationLengthLocation)
    (arrayLocation := arrayLocation)
    (arrayLengthLocation := arrayLengthLocation)
    hconfiguration hconfigurationLength harray harrayLength hsafe
    hevalConfiguration hevalConfigurationLength hevalArray hevalArrayLength

example :
    wordToStackProgNat
        { locations := [(0, .register 4)], scratch := 31, stackBase := 10 }
        ((.assign 0 (.const 42)) : WordProg Nat) =
      some (.const 4 42 : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackWritePhysicalNat, wordStackLocation, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2)], scratch := 31, stackBase := 10 }
        ((.assign 0 (.const 42)) : WordProg Nat) =
      some (.seq (.const 31 42) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.op .add [.var 1, .const 3])) : WordProg Nat) =
      some (.seq (.const 29 3)
        (.seq (.arith .add 31 5 29) (.stackStore 31 12)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileBinaryNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.load (.var 1))) : WordProg Nat) =
      some (.seq (.stackLoad 29 13)
        (.seq (.inst (.mem .load 31 29)) (.stackStore 31 12)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileLoadNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .register 4), (1, .register 5), (2, .register 6)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.shift .lsl (.var 1) (.var 2))) : WordProg Nat) =
      some (.shift .lsl 4 5 6 : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileShiftNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin]

example :
    wordToStackProgNat
        { locations := [(0, .stack 2), (1, .stack 3)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        ((.assign 0 (.shift .lsr (.var 1) (.const 3))) : WordProg Nat) =
      some (.seq (.stackLoad 31 13)
        (.seq (.const 29 3)
          (.seq (.shift .lsr 31 31 29) (.stackStore 31 12))) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileShiftNat, wordStackAtomNat,
    wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
    lookupNatInfo, wordStackJoin, wordStackReadRegister]

example :
    wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10,
          addressScratch := 29 }
        ((.store (.const 100) 0) : WordProg Nat) =
      some (.seq (.const 29 100) (.inst (.mem .store 5 29)) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackCompileStoreNat,
    wordStackAtomNat, wordStackJoin, wordStackReadRegister,
    wordStackLocation, lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        ((.set (.temp 4) (.const 7)) : WordProg Nat) =
      some (.seq (.const 31 7) (.set (.temp 4) 31) : StackProg Nat) := by
  simp [wordToStackProgNat, wordStackSetNat, wordStackAtomNat,
    wordStackJoin, wordStackStoreNameNat]

example :
    (evalWordStackMachine
        { registers := fun register => if register = 5 then 9 else 0,
          stack := fun _ => 0,
          stores := fun _ => 0,
          memory := fun _ => 0,
          sharedMemory := fun _ => 0 }
        ((wordToStackProgNat
          { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
          ((.assign 0 (.const 42)) : WordProg Nat)).getD .skip)).bind
      (fun state => wordStackMachineValue
        { locations := [(0, .register 5)], scratch := 31, stackBase := 10 }
        state 0) =
      some (BitVec.ofNat 8 42) := by
  decide +kernel

example :
    (wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21 }
        ((.call (some ([0], ([], []), .skip, 0, 0)) (some 7) [0] none) : WordProg Nat)).isSome =
      true := by
  simp [wordToStackProg, wordStackReturnCode, wordStackMovesToPhysical,
    wordStackPhysicalMovesTo, wordStackMovesFromPhysical,
    wordStackPhysicalMovesFrom, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMove,
    wordStackLocation, lookupNatInfo]

example :
    (wordToStackProgNat
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21 }
        ((.call none (some 7) [0] none) : WordProg Nat)).map
        (fun program => match program with
          | .seq (.arith .or 2 5 5) _ => true
          | _ => false) = some true := by
  decide +kernel

example :
    (wordToStackProg
        { locations := [(0, .register 5)], scratch := 31, stackBase := 6,
          returnLabel := 20, entryLabel := 21, handlerLabel := 30 }
        ((.call none (some 7) [0] (some (1, .raise 0, 0, 0))) : WordProg Nat)).isSome =
      true := by
  simp [wordToStackProg, wordStackReturnCode, wordStackMovesToPhysical,
    wordStackPhysicalMovesTo,
    wordStackParallelLocationMove, wordStackParallelLocationMoveAux,
    wordStackLocationMoveDestinations, wordStackLocationMoveReady,
    wordStackLocationMoveRemoveDestination, wordStackLocationMove,
    wordStackLocation, wordStackOffset,
    lookupNatInfo, wordToStackRaise,
    wordStackJoin]

end Flapjack.RiscV
