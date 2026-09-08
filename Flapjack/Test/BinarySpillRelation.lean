import Flapjack.RiscV.CorrectnessBinarySpill

/-! Regression coverage for binary lowering with a spilled operand. -/

namespace Flapjack.RiscV

def binarySpillConfig : WordStackConfig :=
  { locations := [(1, .register 5), (2, .stack 0), (3, .register 6),
      (4, .stack 1)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def binarySpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 4 else 0
    stack := fun offset =>
      if offset = 8 then BitVec.ofNat 8 17
      else if offset = 9 then BitVec.ofNat 8 23 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def binarySpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues binarySpillConfig binarySpillValues
      binarySpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 4
  · subst name
    simp [binarySpillValues] at hvalue
    subst value
    simp [binarySpillConfig, binarySpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [binarySpillValues] at hvalue

example :
    wordStackMappedValuesExcept binarySpillConfig 1 binarySpillValues
      (((wordStackCompileBinaryNat binarySpillConfig 1 .add
        (.var 2) (.var 3)).bind
        (evalWordStackMachine binarySpillState)).getD binarySpillState) := by
  apply evalWordStackMachine_binary_preserves_unrelated_values
    (config := binarySpillConfig)
    (state := binarySpillState)
    (final := ((wordStackCompileBinaryNat binarySpillConfig 1 .add
      (.var 2) (.var 3)).bind
      (evalWordStackMachine binarySpillState)).getD binarySpillState)
    (operator := .add) (destination := 1) (left := 2) (right := 3)
    (destinationLocation := .register 5)
    (leftLocation := .stack 0) (rightLocation := .register 6)
    (values := binarySpillValues)
  · simp [binarySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [binarySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [binarySpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hname : name = 4
      · subst name
        simp [binarySpillValues] at hvalue
        subst value
        simp [binarySpillConfig, binarySpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [binarySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [binarySpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [binarySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [binarySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [binarySpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [binarySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [binarySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [binarySpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [binarySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [binarySpillValues] at hvalue
  · simp [binarySpillConfig, binarySpillState, wordStackCompileBinaryNat,
      wordStackAtomNat, wordStackWritePhysicalNat, wordStackReadRegister,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, lookupNatInfo]

end Flapjack.RiscV
