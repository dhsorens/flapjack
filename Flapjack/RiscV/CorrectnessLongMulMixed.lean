import Flapjack.RiscV.CorrectnessDirectAddCarryRegister

/-!
# Mixed-source LongMul contract

When both LongMul results are spilled, either source may be register-resident or
spilled.  This bounded matrix theorem covers those four source layouts while
keeping the proof’s simplification footprint local.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_longMul_stackDest_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight other : Nat)
    (destinationLeftSlot destinationRightSlot : Nat)
    (sourceLeftLocation sourceRightLocation otherLocation : WordLocation)
    (hdestinationLeft : wordStackLocation config destinationLeft =
      some (.stack destinationLeftSlot))
    (hdestinationRight : wordStackLocation config destinationRight =
      some (.stack destinationRightSlot))
    (hsourceLeft : wordStackLocation config sourceLeft =
      some sourceLeftLocation)
    (hsourceRight : wordStackLocation config sourceRight =
      some sourceRightLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hsafe : wordStackLongMulLocationsSafe config
      (.longMul destinationLeft destinationRight sourceLeft sourceRight) = true)
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
  change lookupNatInfo sourceLeft config.locations = some sourceLeftLocation at hsourceLeft
  change lookupNatInfo sourceRight config.locations = some sourceRightLocation at hsourceRight
  change lookupNatInfo other config.locations = some otherLocation at hother
  have hsafeConditions := hsafe
  simp [wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
    wordStackLocation, hdestinationLeft, hdestinationRight, hsourceLeft,
    hsourceRight] at hsafeConditions
  cases sourceLeftLocation <;> cases sourceRightLocation <;> cases otherLocation <;>
    simp_all [wordStackLongMulInst, wordStackLongMulMoveToPhysical,
      wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
      wordStackOffset, evalWordStackMachine]
  all_goals
    cases heval
    simp only [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]
    simp_all

end Flapjack.RiscV
