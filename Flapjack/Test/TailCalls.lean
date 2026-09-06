import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def tailCallTestConfig : WordStackConfig :=
  { locations := [(6, .register 2)]
    scratch := 31
    stackBase := 0 }

theorem tailCallArgumentMoves :
    wordStackMovesToPhysical tailCallTestConfig [6] 2 =
      some (.skip : StackProg Nat) := by
  have hdest :
      wordStackLocationMoveDestinations
          [(WordLocation.register 2, WordLocation.register 2)] =
        [WordLocation.register 2] := by
    rfl
  have hnodup : ([WordLocation.register 2] : List WordLocation).Nodup := by
    decide
  have hremove :
      wordStackLocationMoveRemoveDestination (WordLocation.register 2)
          [(WordLocation.register 2, WordLocation.register 2)] = [] := by
    decide
  have hreserved :
      ([(WordLocation.register 2, WordLocation.register 2)]).any
          (fun move =>
            move.1 = WordLocation.register 31 ||
              move.1 = WordLocation.register 29 ||
              move.2 = WordLocation.register 31 ||
              move.2 = WordLocation.register 29) = false := by
    decide
  simp [wordStackMovesToPhysical, wordStackPhysicalMovesTo,
    tailCallTestConfig, wordStackLocation, lookupNatInfo, hdest, hnodup,
    hremove, hreserved, wordStackLocationMove,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMoveDestinations,
    wordStackParallelLocationMove, wordStackParallelLocationMoveAux,
    wordStackJoin]

example :
    wordToStackProg tailCallTestConfig
        (.call none (some 7) [6] none : WordProg Nat) =
      some (.call none (.label 7) none) := by
  simp [wordToStackProg, tailCallArgumentMoves, wordStackJoin]

example :
    wordToStackProgNat tailCallTestConfig
        (.call none (some 7) [6] none : WordProg Nat) =
      some (.call none (.label 7) none) := by
  simp [wordToStackProgNat, tailCallArgumentMoves, wordStackJoin]

end Flapjack
