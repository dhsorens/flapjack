import Flapjack.RiscV.CorrectnessDirectSet

/-!
# Public arithmetic division contract

The direct WordProg compiler routes arithmetic division through
`wordStackArithInst` and its reserved-location guard.  This theorem composes
that public dispatch with the lower-level division spill relation.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_div_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination dividend divisor : Nat)
    (destinationLocation dividendLocation divisorLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hdividend : wordStackLocation config dividend = some dividendLocation)
    (hdivisor : wordStackLocation config divisor = some divisorLocation)
    (hspecial : wordSpecialArithLocationsSafe
      (.div destination dividend divisor) config.locations = true)
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
      (.inst (.arith (.div destination dividend divisor)))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  have heval' : (wordStackDivInst config destination dividend divisor).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg, wordToStackInst, wordStackArithInst, hspecial] using heval
  exact evalWordStackMachine_div_preserves_unrelated_values config state final
    destination dividend divisor destinationLocation dividendLocation divisorLocation
    values hdestination hdividend hdivisor hvalues hnoalias hno_scratch
    hno_addressScratch heval'

end Flapjack.RiscV
