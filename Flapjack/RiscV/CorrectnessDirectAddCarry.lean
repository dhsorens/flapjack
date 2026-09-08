import Flapjack.RiscV.CorrectnessAddCarrySpill

/-!
# Public fully spilled AddCarry contract

The public arithmetic dispatcher adds the special-location safety check before
calling `wordStackAddCarryInst`.  This theorem composes that dispatcher with
the fully spilled AddCarry relation.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_addCarry_spilled_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (destinationSlot resultCarrySlot sourceLeftSlot sourceRightSlot carryInSlot : Nat)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination = some (.stack destinationSlot))
    (hresultCarry : wordStackLocation config resultCarry = some (.stack resultCarrySlot))
    (hsourceLeft : wordStackLocation config sourceLeft = some (.stack sourceLeftSlot))
    (hsourceRight : wordStackLocation config sourceRight = some (.stack sourceRightSlot))
    (hcarryIn : wordStackLocation config carryIn = some (.stack carryInSlot))
    (hspecial : wordSpecialArithLocationsSafe
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)
      config.locations = true)
    (hvalues : wordStackMappedValues config values state)
    (hnoaliasDestination : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .stack destinationSlot)
    (hnoaliasResultCarry : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .stack resultCarrySlot)
    (hno_scratch : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (hno_addressScratch : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.addressScratch)
    (hno_specialScratch : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.specialScratch)
    (hno_carryScratch : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.carryScratch)
    (heval : (wordToStackProg (α := Nat) config
      (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)))).bind
      (evalWordStackMachine state) = some final) :
    ∀ name value location, name ≠ destination → name ≠ resultCarry →
      values name = some value → wordStackLocation config name = some location →
      wordStackMachineValue config final name = some value := by
  have heval' : (wordStackAddCarryInst config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg, wordToStackInst, wordStackArithInst, hspecial] using heval
  intro name value location hname hresult hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_addCarry_spilled_preserves_other_value
    config state final destination resultCarry sourceLeft sourceRight carryIn name
    destinationSlot resultCarrySlot sourceLeftSlot sourceRightSlot carryInSlot location
    hdestination hresultCarry hsourceLeft hsourceRight hcarryIn hlocation
    (hnoaliasDestination name value location hname hresult hvalue hlocation)
    (hnoaliasResultCarry name value location hname hresult hvalue hlocation)
    (hno_scratch name value location hname hresult hvalue hlocation)
    (hno_addressScratch name value location hname hresult hvalue hlocation)
    (hno_specialScratch name value location hname hresult hvalue hlocation)
    (hno_carryScratch name value location hname hresult hvalue hlocation) heval'
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
