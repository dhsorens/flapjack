import Flapjack.RiscV.CorrectnessLookupSpill

/-!
# Spill-aware StackStore Set contracts

Set lowering changes the StackStore component of the executable state, while
its only frame-register scratch use is the materialization of a spilled source.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_set_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (source other : Nat)
    (sourceLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordStackSetNat config store (.var source)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases sourceLocation <;> cases otherLocation <;>
      simp [wordStackSetNat, wordStackStoreNameNat, wordStackAtomNat,
        wordStackReadRegister, wordStackLocation, wordStackOffset,
        wordStackJoin, evalWordStackMachine, wordStackMachineValue,
        wordStackMachineWriteRegister, wordStackMachineWriteStore,
        hsource, hother] at heval ⊢
  all_goals
    cases heval
    simp_all

theorem evalWordStackMachine_set_preserves_mapped_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (source : Nat)
    (sourceLocation : WordLocation) (values : Nat → Option (Word width))
    (hsource : wordStackLocation config source = some sourceLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (hvalues : wordStackMappedValues config values state)
    (hno_scratch : ∀ name value location,
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordStackSetNat config store (.var source)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  intro name value location hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_set_preserves_other_value
    config state final store source name sourceLocation location
    hsource hlocation hstore
    (hno_scratch name value location hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
