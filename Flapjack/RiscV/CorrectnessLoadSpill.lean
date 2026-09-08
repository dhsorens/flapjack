import Flapjack.RiscV.CorrectnessShiftSpill

/-!
# Spill-aware load expression contracts

Loads materialize a spilled address in `addressScratch` and may materialize a
spilled destination through `scratch`.  The following contracts expose the
non-interference needed to carry the frame relation through that lowering.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_load_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address other : Nat)
    (destinationLocation addressLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (heval : (wordStackCompileLoadNat config destination (.var address)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases destinationLocation <;> cases addressLocation <;> cases otherLocation <;>
    simp [wordStackCompileLoadNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset,
      hdestination, haddress] at heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_load_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
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
    (hno_addressScratch : ∀ name value location,
      name ≠ destination →
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.addressScratch)
    (heval : (wordStackCompileLoadNat config destination (.var address)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_load_preserves_other_value
    config state final destination address name
    destinationLocation addressLocation location
    hdestination haddress hlocation
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation)
    (hno_addressScratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
