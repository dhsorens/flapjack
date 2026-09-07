import Flapjack.RiscV.CorrectnessDirectSharedStore

/-!
# Public WordProg move contracts

Both public variable-move forms lower to the same scratch-aware StackLang move
fragment.  These wrappers expose the reusable spill relation at the public
WordProg entry point.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_direct_assign_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat)
    (destinationLocation sourceLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination_scratch : destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (hvalues : wordStackMappedValues config values state)
    (hnoalias : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ destinationLocation)
    (hno_scratch : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordToStackProg (α := Nat) config
      (.assign destination (.var source))).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  have heval' : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg] using heval
  exact evalWordStackMachine_move_preserves_unrelated_values config state final
    destination source destinationLocation sourceLocation values hdestination hsource
    hdestination_scratch hsource_scratch hvalues hnoalias hno_scratch heval'

theorem evalWordStackMachine_direct_locValue_preserves_unrelated_values
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat)
    (destinationLocation sourceLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination_scratch : destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (hvalues : wordStackMappedValues config values state)
    (hnoalias : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ destinationLocation)
    (hno_scratch : ∀ name value location,
      name ≠ destination → values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordToStackProg (α := Nat) config
      (.locValue destination source)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  have heval' : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final := by
    simpa [wordToStackProg] using heval
  exact evalWordStackMachine_move_preserves_unrelated_values config state final
    destination source destinationLocation sourceLocation values hdestination hsource
    hdestination_scratch hsource_scratch hvalues hnoalias hno_scratch heval'

end Flapjack.RiscV
