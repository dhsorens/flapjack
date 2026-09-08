import Flapjack.RiscV.CorrectnessSpill

/-!
# Spill-aware binary expression contracts

Binary expressions may materialize either operand in one of the two scratch
registers, and a stack destination may use the ordinary scratch register for
the final store.  This theorem packages the corresponding non-interference
fact for the frame relation.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_binary_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : BinOp) (destination left right other : Nat)
    (destinationLocation leftLocation rightLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (heval : (wordStackCompileBinaryNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo left config.locations = some leftLocation at hleft
  change lookupNatInfo right config.locations = some rightLocation at hright
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases destinationLocation <;> cases leftLocation <;> cases rightLocation <;>
    cases otherLocation <;>
    simp [wordStackCompileBinaryNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset,
      hdestination, hleft, hright,
      wordStackBinaryLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_binary_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : BinOp) (destination left right : Nat)
    (destinationLocation leftLocation rightLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
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
    (heval : (wordStackCompileBinaryNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_binary_preserves_other_value
    config state final operator destination left right name
    destinationLocation leftLocation rightLocation location
    hdestination hleft hright hlocation hsafe
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation)
    (hno_addressScratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
