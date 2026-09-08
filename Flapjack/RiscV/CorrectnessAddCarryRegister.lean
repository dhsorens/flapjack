import Flapjack.RiscV.CorrectnessDirectAddCarry

/-!
# Register-resident AddCarry contract

The register-resident AddCarry path executes one special instruction and writes
its two result registers.  This theorem records preservation of any unrelated
register- or stack-backed value.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_addCarry_register_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination resultCarry sourceLeft sourceRight carryIn other : Nat)
    (destinationRegister resultCarryRegister sourceLeftRegister sourceRightRegister
      carryInRegister : Nat) (otherLocation : WordLocation)
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
    (hother : wordStackLocation config other = some otherLocation)
    (hsafe : wordStackAddCarryInst (α := Nat) config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn) =
      some (.inst (.arith (.addCarry destinationRegister resultCarryRegister
        sourceLeftRegister sourceRightRegister carryInRegister)) : StackProg Nat))
    (hother_destination : otherLocation ≠ .register destinationRegister)
    (hother_resultCarry : otherLocation ≠ .register resultCarryRegister)
    (heval : (wordStackAddCarryInst config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations =
      some (.register destinationRegister) at hdestination
  change lookupNatInfo resultCarry config.locations =
      some (.register resultCarryRegister) at hresultCarry
  change lookupNatInfo sourceLeft config.locations =
      some (.register sourceLeftRegister) at hsourceLeft
  change lookupNatInfo sourceRight config.locations =
      some (.register sourceRightRegister) at hsourceRight
  change lookupNatInfo carryIn config.locations =
      some (.register carryInRegister) at hcarryIn
  change lookupNatInfo other config.locations = some otherLocation at hother
  simp [hsafe] at heval
  cases heval
  cases otherLocation <;>
    simp at hother_destination hother_resultCarry
  all_goals
    simp [wordStackMachineValue, wordStackLocation, hother,
      wordStackMachineWriteRegister, hother_destination,
      hother_resultCarry]

end Flapjack.RiscV
