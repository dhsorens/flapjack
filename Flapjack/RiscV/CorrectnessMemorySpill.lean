import Flapjack.RiscV.CorrectnessGetSpill

/-!
# Spill-aware direct memory contracts

The direct WordProg memory path uses `wordStackMemoryInst`, rather than the
expression compiler.  These contracts carry the frame relation through its
ordinary load and store branches.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_memory_load_preserves_other_value [NeZero width]
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
    (heval : (wordStackMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases destinationLocation <;> cases addressLocation <;> cases otherLocation <;>
    simp [wordStackMemoryInst, wordStackLoadInst, wordStackLocation,
      wordStackOffset, hdestination, haddress, evalWordStackMachine] at heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_memory_load_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hvalues : wordStackMappedValues config values state)
    (hnoalias : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ destinationLocation)
    (hno_scratch : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (hno_addressScratch : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.addressScratch)
    (heval : (wordStackMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_memory_load_preserves_other_value
    config state final destination address name destinationLocation
    addressLocation location hdestination haddress hlocation
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation)
    (hno_addressScratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

theorem evalWordStackMachine_memory_store_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address other : Nat)
    (sourceLocation addressLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (heval : (wordStackMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases sourceLocation <;> cases addressLocation <;> cases otherLocation <;>
    simp [wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
      wordStackOffset, hsource, haddress, evalWordStackMachine] at heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory]

theorem evalWordStackMachine_memory_store_preserves_mapped_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hvalues : wordStackMappedValues config values state)
    (hno_scratch : ∀ name value location,
      values name = some value → wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (hno_addressScratch : ∀ name value location,
      values name = some value → wordStackLocation config name = some location →
      location ≠ .register config.addressScratch)
    (heval : (wordStackMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  intro name value location hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_memory_store_preserves_other_value
    config state final source address name sourceLocation addressLocation location
    hsource haddress hlocation
    (hno_scratch name value location hvalue hlocation)
    (hno_addressScratch name value location hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
