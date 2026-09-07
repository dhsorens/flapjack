import Flapjack.RiscV.CorrectnessWordToStack

/-!
# Spill-aware Word-to-Stack state contracts

The single-destination move theorem establishes the value at the destination,
but a compiler simulation also needs the frame relation for every unrelated
variable.  This file adds that preservation contract with the two necessary
side conditions: the unrelated location is not the move destination and is
not the scratch register used by stack moves.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_move_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source other : Nat)
    (destinationLocation sourceLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hdestination_scratch :
      destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  simp [wordStackMove] at heval
  cases destinationLocation <;> cases sourceLocation <;>
    cases otherLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, hsource, hother] at heval ⊢
  all_goals
    cases heval
    simp_all

end Flapjack.RiscV
