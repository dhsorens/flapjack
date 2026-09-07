import Flapjack.RiscV.CorrectnessMemorySpill

/-!
# Public WordProg memory contracts

The public WordProg compiler dispatches ordinary loads through `wordToStackInst`
and stores through its dedicated `.store` branch.  These theorems compose those
entry points with the spill-aware `wordStackMemoryInst` contracts.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_load_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination = some destinationLocation)
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
    (heval : (wordToStackProg (α := Nat) config
      (.inst (.mem .load destination address))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  have heval' : (wordStackMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg, wordToStackInst] using heval
  exact evalWordStackMachine_memory_load_preserves_unrelated_values config state final
    destination address destinationLocation addressLocation values hdestination haddress
    hvalues hnoalias hno_scratch hno_addressScratch heval'

theorem evalWordStackMachine_direct_store_preserves_mapped_values [NeZero width]
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
    (heval : (wordToStackProg (α := Nat) config
      (.store (.var address) source)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  have heval' : (wordStackMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg] using heval
  exact evalWordStackMachine_memory_store_preserves_mapped_values config state final
    source address sourceLocation addressLocation values hsource haddress hvalues
    hno_scratch hno_addressScratch heval'

end Flapjack.RiscV
