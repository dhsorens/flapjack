import Flapjack.StackAlloc.CollectorSemantics

/-!
API regression for the complete bitmap-root/heap-scan collector boundary.
The component witnesses remain explicit so callers can instantiate the
contract with their own root and loop invariants.
-/

namespace Flapjack.RiscV

example [NeZero width] (config : StackGcConfig) (fuel : Nat)
    (state roots final : StackFrameMachineState width)
    (bitmaps : List Nat) (stack : List StackGcNatValue)
    (newBase oldBase : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (moved : StackGcValueRootsResult)
    (scanned : StackGcNatMoveLoopResult)
    (simulation : StackGcFullSimulation config fuel state roots final bitmaps
      stack newBase oldBase memory domain moved scanned) :
    evalStackFrameFuel (fuel + 1) state
        (stackSeq [stackGcMoveRootsBitmapsCode config,
          stackGcMoveLoopCode config]) = some (.normal final) ∧
      stackGcNatFullBitmaps config bitmaps stack newBase oldBase memory domain fuel =
        some { values := moved.values
               nextIndex := scanned.nextIndex
               nextAddress := scanned.nextAddress
               memory := scanned.memory
               condition := scanned.condition } := by
  exact evalStackFrameFuel_stackGcFullBitmaps_simulates config fuel state roots
    final bitmaps stack newBase oldBase memory domain moved scanned simulation

end Flapjack.RiscV
