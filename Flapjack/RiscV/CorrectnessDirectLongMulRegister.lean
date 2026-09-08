import Flapjack.RiscV.CorrectnessLongMulRegister

/-!
# Public register-resident LongMul contract

This composes the public arithmetic dispatcher with the direct register
fast-path relation.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_longMul_register_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (destinationLeftRegister destinationRightRegister sourceLeftRegister
      sourceRightRegister : Nat)
    (values : Nat → Option (Word width))
    (hdestinationLeft : wordStackLocation config destinationLeft =
      some (.register destinationLeftRegister))
    (hdestinationRight : wordStackLocation config destinationRight =
      some (.register destinationRightRegister))
    (hsourceLeft : wordStackLocation config sourceLeft =
      some (.register sourceLeftRegister))
    (hsourceRight : wordStackLocation config sourceRight =
      some (.register sourceRightRegister))
    (hspecial : wordSpecialArithLocationsSafe
      (.longMul destinationLeft destinationRight sourceLeft sourceRight)
      config.locations = true)
    (hsafe : wordStackLongMulLocationsSafe config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight) = true)
    (hvalues : wordStackMappedValues config values state)
    (hnoaliasLeft : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register destinationLeftRegister)
    (hnoaliasRight : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register destinationRightRegister)
    (heval : (wordToStackProg (α := Nat) config
      (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)))).bind
      (evalWordStackMachine state) = some final) :
    ∀ name value location, name ≠ destinationLeft → name ≠ destinationRight →
      values name = some value → wordStackLocation config name = some location →
      wordStackMachineValue config final name = some value := by
  have heval' : (wordStackLongMulInst config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight)).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg, wordToStackInst, wordStackArithInst, hspecial] using heval
  intro name value location hname hright hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_longMul_register_preserves_other_value
    config state final destinationLeft destinationRight sourceLeft sourceRight name
    destinationLeftRegister destinationRightRegister sourceLeftRegister
    sourceRightRegister location
    hdestinationLeft hdestinationRight hsourceLeft hsourceRight hlocation hsafe
    (hnoaliasLeft name value location hname hright hvalue hlocation)
    (hnoaliasRight name value location hname hright hvalue hlocation)
    heval'
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
