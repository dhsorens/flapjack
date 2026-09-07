import Flapjack.RiscV.RegAlloc

namespace Flapjack

/-! Regression for CakeML's `full_ssa_cc_trans` function entry sequence. -/

example :
    wordSsaRenameFunctionWithEntry [2, 3]
        (.return 0 [2, 3] : WordProg Nat) =
      ({ current := [(3, 9), (2, 5)], next := 13 },
        [5, 9],
        .seq (.move 1 [(5, 2), (9, 3)]) (.return 0 [5, 9])) := by
  simp [wordSsaRenameFunctionWithEntry, wordSsaEntryMove,
    wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRead,
    wordSsaFreshList, wordSsaFresh, lookupNatInfo]

example :
    (wordSsaEntryMove [2, 3] [5, 9] : WordProg Nat) =
      .move 1 [(5, 2), (9, 3)] := by
  rfl

/- The entry-aware graph boundary accepts an unused ABI formal and returns a
   coloured program containing its setup move. -/
example :
    (wordAllocateGraphFunctionWithEntry [2]
      (.skip : WordProg (RiscV.Word 64)) [2] 13 0).isSome := by
  decide +kernel

example :
    (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

example :
    (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

example :
    wordAllocateVarsWithFixedSources [2, 5] [] [] [2] =
      some { locations := [(5, .register 7), (2, .register 2)], nextSpill := 0 } := by
  rfl

example (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources [2, 5] [] [] [2] = some state) :
    lookupNatInfo 2 state.locations = some (.register 2) := by
  exact wordAllocateVarsWithFixedSources_preserves_fixed_source
    [2, 5] [] [] [2] state hstate 2 (by simp)

end Flapjack
