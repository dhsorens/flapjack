import Flapjack.RiscV.CorrectnessDirectLongMul

/-!
# Register-resident LongMul contract

The register-resident LongMul path executes one special instruction directly.
This theorem records that only its two result registers can change.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_longMul_register_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight other : Nat)
    (destinationLeftRegister destinationRightRegister sourceLeftRegister
      sourceRightRegister : Nat) (otherLocation : WordLocation)
    (hdestinationLeft : wordStackLocation config destinationLeft =
      some (.register destinationLeftRegister))
    (hdestinationRight : wordStackLocation config destinationRight =
      some (.register destinationRightRegister))
    (hsourceLeft : wordStackLocation config sourceLeft =
      some (.register sourceLeftRegister))
    (hsourceRight : wordStackLocation config sourceRight =
      some (.register sourceRightRegister))
    (hother : wordStackLocation config other = some otherLocation)
    (hsafe : wordStackLongMulLocationsSafe config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight) = true)
    (hother_destinationLeft : otherLocation ≠ .register destinationLeftRegister)
    (hother_destinationRight : otherLocation ≠ .register destinationRightRegister)
    (heval : (wordStackLongMulInst config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destinationLeft config.locations =
      some (.register destinationLeftRegister) at hdestinationLeft
  change lookupNatInfo destinationRight config.locations =
      some (.register destinationRightRegister) at hdestinationRight
  change lookupNatInfo sourceLeft config.locations =
      some (.register sourceLeftRegister) at hsourceLeft
  change lookupNatInfo sourceRight config.locations =
      some (.register sourceRightRegister) at hsourceRight
  change lookupNatInfo other config.locations = some otherLocation at hother
  simp [wordStackLongMulInst, hsafe, wordStackLocation, hdestinationLeft,
    hdestinationRight, hsourceLeft, hsourceRight] at heval
  cases heval
  cases otherLocation <;>
    simp at hother_destinationLeft hother_destinationRight
  all_goals
    simp [wordStackMachineValue, wordStackLocation, hother,
      wordStackMachineWriteRegister, hother_destinationLeft,
      hother_destinationRight]

end Flapjack.RiscV
