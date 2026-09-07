import Flapjack.RiscV.CorrectnessAddCarrySpill

/-! Regression coverage for the fully spilled AddCarry lowering. -/

namespace Flapjack.RiscV

def addCarrySpillConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3), (2, .stack 4),
      (3, .stack 5), (4, .stack 6), (5, .register 6)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def addCarrySpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 14 then BitVec.ofNat 8 255
      else if offset = 15 then BitVec.ofNat 8 1
      else if offset = 16 then BitVec.ofNat 8 1 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def addCarrySpillValues : Nat → Option (Word 8)
  | 5 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues addCarrySpillConfig addCarrySpillValues
      addCarrySpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 5
  · subst name
    simp [addCarrySpillValues] at hvalue
    subst value
    simp [addCarrySpillConfig, addCarrySpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [addCarrySpillValues] at hvalue

example :
    wordStackMachineValue addCarrySpillConfig
      (((wordStackAddCarryInst addCarrySpillConfig
        (.addCarry 0 1 2 3 4)).bind
        (evalWordStackMachine addCarrySpillState)).getD addCarrySpillState) 5 =
      wordStackMachineValue addCarrySpillConfig addCarrySpillState 5 := by
  apply evalWordStackMachine_addCarry_spilled_preserves_other_value
    (config := addCarrySpillConfig) (state := addCarrySpillState)
    (final := ((wordStackAddCarryInst addCarrySpillConfig
      (.addCarry 0 1 2 3 4)).bind
      (evalWordStackMachine addCarrySpillState)).getD addCarrySpillState)
    (destination := 0) (resultCarry := 1) (sourceLeft := 2)
    (sourceRight := 3) (carryIn := 4) (other := 5)
    (destinationSlot := 2) (resultCarrySlot := 3)
    (sourceLeftSlot := 4) (sourceRightSlot := 5)
    (carryInSlot := 6) (otherLocation := .register 6)
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [addCarrySpillConfig, addCarrySpillState, wordStackAddCarryInst,
      wordStackAddCarryLocationSafe, wordStackLongMulMoveToPhysical,
      wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
      wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
