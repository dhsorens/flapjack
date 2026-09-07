import Flapjack.RiscV.CorrectnessDirectAddCarry

/-!
# Fully spilled LongMul contract

The fully spilled LongMul path uses `scratch` and `addressScratch` for the
operands and `specialScratch`/`scratch` for the two results.  This theorem
isolates its frame-preservation footprint and makes the required distinctness
of those reserved registers explicit.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_longMul_spilled_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight other : Nat)
    (destinationLeftSlot destinationRightSlot sourceLeftSlot sourceRightSlot : Nat)
    (otherLocation : WordLocation)
    (hdestinationLeft : wordStackLocation config destinationLeft =
      some (.stack destinationLeftSlot))
    (hdestinationRight : wordStackLocation config destinationRight =
      some (.stack destinationRightSlot))
    (hsourceLeft : wordStackLocation config sourceLeft =
      some (.stack sourceLeftSlot))
    (hsourceRight : wordStackLocation config sourceRight =
      some (.stack sourceRightSlot))
    (hother : wordStackLocation config other = some otherLocation)
    (hreserved : config.scratch ≠ config.addressScratch)
    (hother_destinationLeft : otherLocation ≠ .stack destinationLeftSlot)
    (hother_destinationRight : otherLocation ≠ .stack destinationRightSlot)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (hother_specialScratch : otherLocation ≠ .register config.specialScratch)
    (heval : (wordStackLongMulInst config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destinationLeft config.locations =
      some (.stack destinationLeftSlot) at hdestinationLeft
  change lookupNatInfo destinationRight config.locations =
      some (.stack destinationRightSlot) at hdestinationRight
  change lookupNatInfo sourceLeft config.locations =
      some (.stack sourceLeftSlot) at hsourceLeft
  change lookupNatInfo sourceRight config.locations =
      some (.stack sourceRightSlot) at hsourceRight
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases otherLocation <;>
    simp [wordStackLongMulInst, wordStackLongMulLocationsSafe,
      wordStackLongMulLocationSafe, wordStackLongMulMoveToPhysical,
      wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
      wordStackOffset, evalWordStackMachine, hdestinationLeft,
      hdestinationRight, hsourceLeft, hsourceRight] at heval
  all_goals
    cases heval
    simp at hother_destinationLeft hother_destinationRight hother_scratch hother_addressScratch hother_specialScratch
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset, hother,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      hreserved,
      hother_destinationLeft, hother_destinationRight, hother_scratch,
      hother_addressScratch, hother_specialScratch]

end Flapjack.RiscV
