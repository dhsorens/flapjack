import Flapjack.RiscV.CorrectnessConstSpill

/-!
# Spill-aware lookup-assignment contracts

Lookup assignment has the same physical write footprint as a constant
assignment.  Its source is a StackStore value, so the contract additionally
keeps the store-name mapping explicit.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_lookup_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination other : Nat) (store : WordStore Nat)
    (destinationLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordStackCompileExpNat config destination (.lookup store)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases destinationLocation <;> cases otherLocation <;>
      simp [wordStackCompileExpNat, wordStackStoreNameNat,
        wordStackWritePhysicalNat, evalWordStackMachine,
        wordStackMachineValue, wordStackLocation, wordStackOffset,
        wordStackMachineWriteRegister,
        hdestination, hother] at heval ⊢
  all_goals
    cases heval
    simp_all [wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_lookup_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination : Nat) (store : WordStore Nat)
    (destinationLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
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
    (heval : (wordStackCompileExpNat config destination (.lookup store)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_lookup_preserves_other_value
    config state final destination name store destinationLocation location
    hdestination hlocation hstore
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
