import Flapjack.RiscV.CorrectnessStoreSpill

/-!
# Spill-aware constant-assignment contracts

The constant expression lowering writes the destination directly or uses
`scratch` before storing a spilled destination.  This gives the corresponding
unrelated-value preservation contract.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_const_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination other value : Nat)
    (destinationLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordStackCompileExpNat config destination (.const value)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo other config.locations = some otherLocation at hother
  simp [wordStackCompileExpNat, wordStackWritePhysicalNat] at heval
  cases destinationLocation <;> cases otherLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      hdestination, hother] at heval ⊢
  all_goals
    cases heval
    simp_all [wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_const_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination value : Nat) (destinationLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hvalues : wordStackMappedValues config values state)
    (hnoalias : ∀ name value location,
      name ≠ destination →
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ destinationLocation)
    (hno_scratch : ∀ name value location,
      name ≠ destination →
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordStackCompileExpNat config destination (.const value)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name mappedValue location hname hvalue hlocation
  have hstateValue := hvalues name mappedValue location hvalue hlocation
  have hpreserved := evalWordStackMachine_const_preserves_other_value
    config state final destination name value destinationLocation location
    hdestination hlocation
    (hnoalias name mappedValue location hname hvalue hlocation)
    (hno_scratch name mappedValue location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
