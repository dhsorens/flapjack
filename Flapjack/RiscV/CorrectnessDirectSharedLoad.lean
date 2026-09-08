import Flapjack.RiscV.CorrectnessSharedLoadSpill

/-!
# Public shared-memory load contract

The public `shareInst` lowering uses `wordStackSharedMemoryInst`, while the
existing expression-level theorem is phrased using `wordStackCompileSharedNat`.
This theorem composes the two equivalent `.var` paths at the public boundary.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_shared_load_preserves_unrelated_values
    [NeZero width]
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
      (.shareInst .load destination (.var address))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  have hcompile : wordStackCompileSharedNat config .load destination (.var address) =
      wordStackSharedMemoryInst config .load destination address := by
    change lookupNatInfo destination config.locations = some destinationLocation
      at hdestination
    change lookupNatInfo address config.locations = some addressLocation at haddress
    cases destinationLocation <;> cases addressLocation <;>
      simp [wordStackCompileSharedNat, wordStackAtomNat,
        wordStackWritePhysicalNat, wordStackReadRegister, wordStackJoin,
        wordStackSharedMemoryInst, wordStackSharedLoadInst,
        wordStackLocation, wordStackOffset, hdestination, haddress]
  have heval' : (wordStackCompileSharedNat config .load destination (.var address)).bind
      (evalWordStackMachine state) = some final := by
    rw [hcompile]
    simpa [wordToStackProg] using heval
  exact evalWordStackMachine_shared_load_preserves_unrelated_values config state final
    destination address destinationLocation addressLocation values hdestination haddress
    hvalues hnoalias hno_scratch hno_addressScratch heval'

end Flapjack.RiscV
