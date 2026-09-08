import Flapjack.RiscV.CorrectnessLongMulMixed

/-!
# Public mixed-source LongMul contract

This composes public arithmetic dispatch with the spilled-destination LongMul
relation, retaining arbitrary source locations.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_longMul_stackDest_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (destinationLeftSlot destinationRightSlot : Nat)
    (sourceLeftLocation sourceRightLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestinationLeft : wordStackLocation config destinationLeft =
      some (.stack destinationLeftSlot))
    (hdestinationRight : wordStackLocation config destinationRight =
      some (.stack destinationRightSlot))
    (hsourceLeft : wordStackLocation config sourceLeft = some sourceLeftLocation)
    (hsourceRight : wordStackLocation config sourceRight = some sourceRightLocation)
    (hspecial : wordSpecialArithLocationsSafe
      (.longMul destinationLeft destinationRight sourceLeft sourceRight)
      config.locations = true)
    (hsafe : wordStackLongMulLocationsSafe config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight) = true)
    (hreserved : config.scratch ≠ config.addressScratch)
    (hvalues : wordStackMappedValues config values state)
    (hnoaliasLeft : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .stack destinationLeftSlot)
    (hnoaliasRight : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .stack destinationRightSlot)
    (hno_scratch : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (hno_addressScratch : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.addressScratch)
    (hno_specialScratch : ∀ name value location,
      name ≠ destinationLeft → name ≠ destinationRight → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.specialScratch)
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
  have hpreserved := evalWordStackMachine_longMul_stackDest_preserves_other_value
    config state final destinationLeft destinationRight sourceLeft sourceRight name
    destinationLeftSlot destinationRightSlot sourceLeftLocation sourceRightLocation location
    hdestinationLeft hdestinationRight hsourceLeft hsourceRight hlocation hsafe hreserved
    (hnoaliasLeft name value location hname hright hvalue hlocation)
    (hnoaliasRight name value location hname hright hvalue hlocation)
    (hno_scratch name value location hname hright hvalue hlocation)
    (hno_addressScratch name value location hname hright hvalue hlocation)
    (hno_specialScratch name value location hname hright hvalue hlocation) heval'
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
