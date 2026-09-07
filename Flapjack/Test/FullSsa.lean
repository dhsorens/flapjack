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

/- The FFI SSA boundary refreshes the live cut set around the ABI call and
   restores it afterwards, matching CakeML's `ssa_cc_trans` shape. -/
example :
    wordSsaRenameProgram ({ current := [], next := 10 } : WordSsaState)
      (.ffi "f" 1 2 3 4 ([5], [6]) : WordProg Nat) =
      ({ current := [(6, 26), (5, 22)], next := 30 },
        .seq (.move 0 [(12, 5), (16, 6)])
          (.seq (.move 0 [(2, 1), (4, 2), (6, 3), (8, 4)])
            (.seq (.ffi "f" 2 4 6 8 ([12], [16]))
              (.move 0 [(22, 12), (26, 16)])))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, wordSsaReadCutsets, wordSsaFreshList,
    wordSsaFresh, wordSsaRead, wordSsaRestrict, wordSsaSeq, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop, lookupNatInfo]

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

example (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources [2, 5] [] [] [2] = some state) :
    ∀ name, name ∈ [2, 5].eraseDups →
      ∃ location, lookupNatInfo name state.locations = some location := by
  exact wordAllocateVarsWithFixedSources_maps_slots
    [2, 5] [] [] [2] state hstate

end Flapjack
