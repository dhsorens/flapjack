import Flapjack.RiscV.CorrectnessDirectSet

/-! Regression coverage for the public WordProg Set lowering. -/

namespace Flapjack.RiscV

def directSetConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def directSetState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset => if offset = 9 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def directSetValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues directSetConfig directSetValues directSetState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [directSetValues] at hvalue
    subst value
    simp [directSetConfig, directSetState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [directSetValues] at hvalue

example :
    wordStackMappedValues directSetConfig directSetValues
      (((wordToStackProg (α := Nat) directSetConfig
        (.set .currHeap (.var 2))).bind
        (evalWordStackMachine directSetState)).getD directSetState) := by
  apply evalWordStackMachine_direct_set_preserves_mapped_values
    (config := directSetConfig) (state := directSetState)
    (final := ((wordToStackProg (α := Nat) directSetConfig
      (.set .currHeap (.var 2))).bind
      (evalWordStackMachine directSetState)).getD directSetState)
    (store := .currHeap) (source := 2) (stackStore := .currHeap)
    (sourceLocation := .stack 1) (values := directSetValues)
  · simp [directSetConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [directSetValues] at hvalue
        subst value
        simp [directSetConfig, directSetState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [directSetValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [directSetValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [directSetConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [directSetValues] at hvalue
  · simp [directSetConfig, directSetState, wordToStackProg,
      wordStackStoreName, wordStackReadRegister, wordStackLocation, wordStackOffset,
      wordStackJoin, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteStore, lookupNatInfo]

end Flapjack.RiscV
