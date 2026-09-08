import Flapjack.RiscV.CorrectnessDirectAddCarryRegister

/-! Regression coverage for register-resident AddCarry lowering. -/

namespace Flapjack.RiscV

def addCarryRegisterConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7), (4, .register 8),
      (5, .register 9)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def addCarryRegisterState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 6 then BitVec.ofNat 8 3
      else if register = 7 then BitVec.ofNat 8 4
      else if register = 8 then BitVec.ofNat 8 1
      else if register = 9 then BitVec.ofNat 8 23 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def addCarryRegisterValues : Nat → Option (Word 8) := fun name =>
  if name = 5 then some (BitVec.ofNat 8 23) else none

example :
    wordStackMachineValue addCarryRegisterConfig
      (((wordStackAddCarryInst addCarryRegisterConfig
        (.addCarry 0 1 2 3 4)).bind
        (evalWordStackMachine addCarryRegisterState)).getD addCarryRegisterState) 5 =
      wordStackMachineValue addCarryRegisterConfig addCarryRegisterState 5 := by
  apply evalWordStackMachine_addCarry_register_preserves_other_value
    (config := addCarryRegisterConfig) (state := addCarryRegisterState)
    (final := ((wordStackAddCarryInst addCarryRegisterConfig
      (.addCarry 0 1 2 3 4)).bind
      (evalWordStackMachine addCarryRegisterState)).getD addCarryRegisterState)
    (destination := 0) (resultCarry := 1) (sourceLeft := 2)
    (sourceRight := 3) (carryIn := 4) (other := 5)
    (destinationRegister := 4) (resultCarryRegister := 5)
    (sourceLeftRegister := 6) (sourceRightRegister := 7)
    (carryInRegister := 8) (otherLocation := .register 9)
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [addCarryRegisterConfig, wordStackAddCarryInst,
      wordStackAddCarryLocationSafe, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · simp [addCarryRegisterConfig, addCarryRegisterState, wordStackAddCarryInst,
      wordStackAddCarryLocationSafe, wordStackLocation, lookupNatInfo,
      evalWordStackMachine, wordStackMachineWriteRegister]

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      addCarryRegisterValues name = some value →
      wordStackLocation addCarryRegisterConfig name = some location →
      wordStackMachineValue addCarryRegisterConfig
        (((wordToStackProg (α := Nat) addCarryRegisterConfig
          (.inst (.arith (.addCarry 0 1 2 3 4)))).bind
          (evalWordStackMachine addCarryRegisterState)).getD addCarryRegisterState)
        name = some value := by
  have hvalue_location : ∀ name value location,
      addCarryRegisterValues name = some value →
      wordStackLocation addCarryRegisterConfig name = some location →
      name = 5 ∧ value = BitVec.ofNat 8 23 ∧ location = .register 9 := by
    intro name value location hvalue hlocation
    simp [addCarryRegisterValues] at hvalue
    by_cases hname : name = 5
    · subst name
      simp at hvalue
      subst value
      have hlocation' : location = .register 9 := by
        simpa [addCarryRegisterConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      exact ⟨rfl, rfl, hlocation'⟩
    · simp [hname] at hvalue
  refine evalWordStackMachine_direct_addCarry_register_preserves_unrelated_values
    (config := addCarryRegisterConfig) (state := addCarryRegisterState)
    (final := ((wordToStackProg (α := Nat) addCarryRegisterConfig
      (.inst (.arith (.addCarry 0 1 2 3 4)))).bind
      (evalWordStackMachine addCarryRegisterState)).getD addCarryRegisterState)
    (destination := 0) (resultCarry := 1) (sourceLeft := 2)
    (sourceRight := 3) (carryIn := 4)
    (destinationRegister := 4) (resultCarryRegister := 5)
    (sourceLeftRegister := 6) (sourceRightRegister := 7)
    (carryInRegister := 8) (values := addCarryRegisterValues)
    (hdestination := by simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo])
    (hresultCarry := by simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo])
    (hsourceLeft := by simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo])
    (hsourceRight := by simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo])
    (hcarryIn := by simp [addCarryRegisterConfig, wordStackLocation, lookupNatInfo])
    (hspecial := by simp [addCarryRegisterConfig, wordSpecialArithLocationsSafe,
      lookupNatInfo])
    (hsafe := by simp [addCarryRegisterConfig, wordStackAddCarryInst,
      wordStackAddCarryLocationSafe, wordStackLocation, lookupNatInfo])
    (hvalues := by
      intro name value location hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      simp [addCarryRegisterConfig, addCarryRegisterState, wordStackMachineValue,
        wordStackLocation, wordStackOffset, lookupNatInfo])
    (hnoaliasDestination := by
      intro name value location hname hresult hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hnoaliasResultCarry := by
      intro name value location hname hresult hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (heval := by
      simp [addCarryRegisterConfig, addCarryRegisterState, wordToStackProg,
        wordToStackInst, wordStackArithInst, wordStackAddCarryInst,
        wordStackAddCarryLocationSafe, wordSpecialArithLocationsSafe,
        wordStackLocation, lookupNatInfo, evalWordStackMachine,
        wordStackMachineWriteRegister])

end Flapjack.RiscV
