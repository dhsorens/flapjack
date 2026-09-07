import Flapjack.RiscV.CorrectnessDirectMove

/-!
# Spill-aware AddCarry contracts

`AddCarry` has two destinations and three source operands.  The spill-aware
lowering materializes those sources in the three reserved arithmetic
registers, executes the special instruction, and writes both results back.
This contract records the resulting frame non-interference footprint.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_addCarry_spilled_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination resultCarry sourceLeft sourceRight carryIn other : Nat)
    (destinationSlot resultCarrySlot sourceLeftSlot sourceRightSlot carryInSlot : Nat)
    (otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some (.stack destinationSlot))
    (hresultCarry : wordStackLocation config resultCarry = some (.stack resultCarrySlot))
    (hsourceLeft : wordStackLocation config sourceLeft = some (.stack sourceLeftSlot))
    (hsourceRight : wordStackLocation config sourceRight = some (.stack sourceRightSlot))
    (hcarryIn : wordStackLocation config carryIn = some (.stack carryInSlot))
    (hother : wordStackLocation config other = some otherLocation)
    (hother_destination : otherLocation ≠ .stack destinationSlot)
    (hother_resultCarry : otherLocation ≠ .stack resultCarrySlot)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (hother_addressScratch : otherLocation ≠ .register config.addressScratch)
    (hother_specialScratch : otherLocation ≠ .register config.specialScratch)
    (hother_carryScratch : otherLocation ≠ .register config.carryScratch)
    (heval : (wordStackAddCarryInst config
      (.addCarry destination resultCarry sourceLeft sourceRight carryIn)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some (.stack destinationSlot)
    at hdestination
  change lookupNatInfo resultCarry config.locations = some (.stack resultCarrySlot)
    at hresultCarry
  change lookupNatInfo sourceLeft config.locations = some (.stack sourceLeftSlot)
    at hsourceLeft
  change lookupNatInfo sourceRight config.locations = some (.stack sourceRightSlot)
    at hsourceRight
  change lookupNatInfo carryIn config.locations = some (.stack carryInSlot) at hcarryIn
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases otherLocation <;>
    simp [wordStackAddCarryInst, wordStackAddCarryLocationSafe,
      wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
      wordStackJoin, wordStackLocation, wordStackOffset,
      evalWordStackMachine, hdestination, hresultCarry, hsourceLeft,
      hsourceRight, hcarryIn] at heval
  all_goals
    cases heval
    simp at hother_destination hother_resultCarry hother_scratch hother_addressScratch hother_specialScratch hother_carryScratch
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset, hother,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      hother_destination, hother_resultCarry,
      hother_addressScratch, hother_specialScratch, hother_carryScratch]

end Flapjack.RiscV
