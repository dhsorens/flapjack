import Flapjack.RiscV.CorrectnessMemorySpill

/-!
# Direct WordProg Set contracts

The public Word-to-Stack compiler has a dedicated `WordProg.set` branch.  Its
source materialization is equivalent to the compact Set helper but it uses the
polymorphic StackStore mapping, so the relation is stated at the compiler
entry point itself.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_set_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (source other : Nat)
    (sourceLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hstore : wordStackStoreName store = some stackStore)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordToStackProg config (.set store (.var source))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases store <;> simp [wordStackStoreName] at hstore
  all_goals
    cases hstore
    cases sourceLocation <;> cases otherLocation <;>
      simp [wordToStackProg, wordStackReadRegister, wordStackLocation,
        wordStackOffset, wordStackJoin, wordStackMachineValue,
        hsource, hother] at heval ⊢
  all_goals
    cases heval
    simp_all [wordStackMachineWriteRegister, wordStackMachineWriteStore]

theorem evalWordStackMachine_direct_set_preserves_mapped_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (source : Nat) (values : Nat → Option (Word width))
    (hsource : wordStackLocation config source = some sourceLocation)
    (hstore : wordStackStoreName store = some stackStore)
    (hvalues : wordStackMappedValues config values state)
    (hno_scratch : ∀ name value location,
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordToStackProg config (.set store (.var source))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  intro name value location hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_direct_set_preserves_other_value
    config state final store source name sourceLocation location
    hsource hlocation hstore
    (hno_scratch name value location hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
