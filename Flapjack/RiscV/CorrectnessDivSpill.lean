import Flapjack.RiscV.CorrectnessSharedLoadSpill

/-!
# Spill-aware division contracts

Division has separate scratch requirements for its dividend and divisor, and
uses `scratch` again for a spilled destination.  This file lifts its complete
location-matrix execution equation to the reusable frame relation.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_div_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination dividend divisor other : Nat)
    (destinationLocation dividendLocation divisorLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hdividend : wordStackLocation config dividend = some dividendLocation)
    (hdivisor : wordStackLocation config divisor = some divisorLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (heval : (wordStackDivInst config destination dividend divisor).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo dividend config.locations = some dividendLocation at hdividend
  change lookupNatInfo divisor config.locations = some divisorLocation at hdivisor
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases destinationLocation <;> cases dividendLocation <;>
    cases divisorLocation <;> cases otherLocation <;>
    simp [wordStackDivInst, wordStackJoin, wordStackLocation, wordStackOffset,
      evalWordStackMachine, hdestination, hdividend, hdivisor] at heval
  all_goals
    cases heval
    simp_all [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_div_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination dividend divisor : Nat)
    (destinationLocation dividendLocation divisorLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hdividend : wordStackLocation config dividend = some dividendLocation)
    (hdivisor : wordStackLocation config divisor = some divisorLocation)
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
    (heval : (wordStackDivInst config destination dividend divisor).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_div_preserves_other_value
    config state final destination dividend divisor name
    destinationLocation dividendLocation divisorLocation location
    hdestination hdividend hdivisor hlocation
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation)
    (hno_addressScratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
