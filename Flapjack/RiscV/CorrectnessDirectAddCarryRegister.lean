import Flapjack.RiscV.CorrectnessAddCarryRegister

/-!
# Public register-resident AddCarry contract

This composes the public arithmetic dispatcher with the direct register
fast-path relation for the two-result AddCarry instruction.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_addCarry_register_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (destinationRegister resultCarryRegister sourceLeftRegister sourceRightRegister
      carryInRegister : Nat) (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some (.register destinationRegister))
    (hresultCarry : wordStackLocation config resultCarry =
      some (.register resultCarryRegister))
    (hsourceLeft : wordStackLocation config sourceLeft =
      some (.register sourceLeftRegister))
    (hsourceRight : wordStackLocation config sourceRight =
      some (.register sourceRightRegister))
    (hcarryIn : wordStackLocation config carryIn =
      some (.register carryInRegister))
    (hspecial : wordSpecialArithLocationsSafe
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)
      config.locations = true)
    (hsafe : wordStackAddCarryInst (α := Nat) config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn) =
      some (.inst (.arith (.addCarry destinationRegister resultCarryRegister
        sourceLeftRegister sourceRightRegister carryInRegister)) : StackProg Nat))
    (hvalues : wordStackMappedValues config values state)
    (hnoaliasDestination : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register destinationRegister)
    (hnoaliasResultCarry : ∀ name value location,
      name ≠ destination → name ≠ resultCarry → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register resultCarryRegister)
    (heval : (wordToStackProg (α := Nat) config
      (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)))).bind
      (evalWordStackMachine state) = some final) :
    ∀ name value location, name ≠ destination → name ≠ resultCarry →
      values name = some value → wordStackLocation config name = some location →
      wordStackMachineValue config final name = some value := by
  have heval' : (wordStackAddCarryInst (α := Nat) config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg, wordToStackInst, wordStackArithInst, hspecial] using heval
  intro name value location hname hresult hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_addCarry_register_preserves_other_value
    config state final destination resultCarry sourceLeft sourceRight carryIn name
    destinationRegister resultCarryRegister sourceLeftRegister sourceRightRegister
    carryInRegister location hdestination hresultCarry hsourceLeft hsourceRight hcarryIn
    hlocation hsafe
    (hnoaliasDestination name value location hname hresult hvalue hlocation)
    (hnoaliasResultCarry name value location hname hresult hvalue hlocation) heval'
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
