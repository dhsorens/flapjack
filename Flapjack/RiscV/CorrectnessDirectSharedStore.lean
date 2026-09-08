import Flapjack.RiscV.CorrectnessDirectSharedLoad

/-!
# Public shared-memory store contract

The public `shareInst` store path uses the direct shared-memory StackLang
instruction.  It changes shared memory only, apart from the temporary
registers used to materialize spilled source and address operands.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_shared_store_preserves_other_value
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address other : Nat)
    (sourceLocation addressLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (heval : (wordStackSharedMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases sourceLocation <;> cases addressLocation <;> cases otherLocation <;>
    simp [wordStackSharedMemoryInst, wordStackSharedStoreInst,
      wordStackLocation, wordStackOffset, hsource, haddress,
      evalWordStackMachine] at heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSharedMemory]

theorem evalWordStackMachine_direct_shared_store_preserves_mapped_values
    [NeZero width]
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
      (.shareInst .store source (.var address))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  have heval' : (wordStackSharedMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg] using heval
  intro name value location hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_direct_shared_store_preserves_other_value
    config state final source address name sourceLocation addressLocation location
    hsource haddress hlocation
    (hno_scratch name value location hvalue hlocation)
    (hno_addressScratch name value location hvalue hlocation) heval'
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
