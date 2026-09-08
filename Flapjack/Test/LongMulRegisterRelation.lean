import Flapjack.RiscV.CorrectnessDirectLongMulRegister

/-! Regression coverage for register-resident LongMul lowering. -/

namespace Flapjack.RiscV

def longMulRegisterConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7), (4, .register 8)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def longMulRegisterState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 8 then BitVec.ofNat 8 23
      else if register = 6 then BitVec.ofNat 8 3
      else if register = 7 then BitVec.ofNat 8 4 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def longMulRegisterValues : Nat → Option (Word 8) := fun name =>
  if name = 4 then some (BitVec.ofNat 8 23) else none

example :
    wordStackMachineValue longMulRegisterConfig
      (((wordStackLongMulInst longMulRegisterConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState) 4 =
      wordStackMachineValue longMulRegisterConfig longMulRegisterState 4 := by
  apply evalWordStackMachine_longMul_register_preserves_other_value
    (config := longMulRegisterConfig) (state := longMulRegisterState)
    (final := ((wordStackLongMulInst longMulRegisterConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftRegister := 4) (destinationRightRegister := 5)
    (sourceLeftRegister := 6) (sourceRightRegister := 7)
    (otherLocation := .register 8)
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · simp [longMulRegisterConfig, longMulRegisterState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLocation, lookupNatInfo, evalWordStackMachine,
      wordStackMachineWriteRegister]

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      longMulRegisterValues name = some value →
      wordStackLocation longMulRegisterConfig name = some location →
      wordStackMachineValue longMulRegisterConfig
        (((wordToStackProg (α := Nat) longMulRegisterConfig
          (.inst (.arith (.longMul 0 1 2 3)))).bind
          (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState)
        name = some value := by
  have hvalue_location : ∀ name value location,
      longMulRegisterValues name = some value →
      wordStackLocation longMulRegisterConfig name = some location →
      name = 4 ∧ value = BitVec.ofNat 8 23 ∧ location = .register 8 := by
    intro name value location hvalue hlocation
    simp [longMulRegisterValues] at hvalue
    by_cases hname : name = 4
    · subst name
      simp at hvalue
      subst value
      have hlocation' : location = .register 8 := by
        simpa [longMulRegisterConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      exact ⟨rfl, rfl, hlocation'⟩
    · simp [hname] at hvalue
  refine evalWordStackMachine_direct_longMul_register_preserves_unrelated_values
    (config := longMulRegisterConfig) (state := longMulRegisterState)
    (final := ((wordToStackProg (α := Nat) longMulRegisterConfig
      (.inst (.arith (.longMul 0 1 2 3)))).bind
      (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3)
    (destinationLeftRegister := 4) (destinationRightRegister := 5)
    (sourceLeftRegister := 6) (sourceRightRegister := 7)
    (values := longMulRegisterValues)
    (hdestinationLeft := by simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo])
    (hdestinationRight := by simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo])
    (hsourceLeft := by simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo])
    (hsourceRight := by simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo])
    (hspecial := by simp [longMulRegisterConfig, wordSpecialArithLocationsSafe,
      lookupNatInfo])
    (hsafe := by simp [longMulRegisterConfig, wordStackLongMulLocationsSafe,
      wordStackLongMulLocationSafe, wordStackLocation, lookupNatInfo])
    (hvalues := by
      intro name value location hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      simp [longMulRegisterConfig, longMulRegisterState, wordStackMachineValue,
        wordStackLocation, wordStackOffset, lookupNatInfo])
    (hnoaliasLeft := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hnoaliasRight := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (heval := by
      simp [longMulRegisterConfig, longMulRegisterState, wordToStackProg,
        wordToStackInst, wordStackArithInst, wordStackLongMulInst,
        wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
        wordSpecialArithLocationsSafe, wordStackLocation, lookupNatInfo,
        evalWordStackMachine, wordStackMachineWriteRegister])

end Flapjack.RiscV
