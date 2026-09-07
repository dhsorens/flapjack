import Flapjack.Pipeline

namespace Flapjack

/-! Regression tests for the CakeML-style function boundary around SSA
    renaming and ABI parameter entry moves. -/

example :
    wordSsaRenameFunction [2, 3]
        (.return 0 [2, 3] : WordProg Nat) =
      ({ current := [(3, 9), (2, 5)], next := 13 },
        [5, 9], .seq (.move 0 [(2, 5), (4, 9)])
          (.return 0 [2, 4])) := by
  have hAbi : wordSsaCallAbiRegisters 1 2 = [2, 4] := by rfl
  simp [wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRead,
    wordSsaFreshList, wordSsaFresh, wordSsaSeq, hAbi, lookupNatInfo]

/- An unused formal is still included in the allocation input, because the
   generated entry move must have a destination. -/
example :
    (wordAllocateSsaFunctionWithSpills [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

example (result : WordSsaState × List Nat × WordProg (RiscV.Word 64) ×
    WordSpillState)
    (hresult : wordAllocateSsaFunctionWithSpills [2]
    (.skip : WordProg (RiscV.Word 64)) = some result) :
    ∀ name, name ∈ result.2.1 →
      ∃ location, lookupNatInfo name result.2.2.2.locations = some location := by
  exact wordAllocateSsaFunctionWithSpills_maps_parameters [2]
    (.skip : WordProg (RiscV.Word 64)) result.1 result.2.1 result.2.2.1
    result.2.2.2 hresult

/- The preference-aware function entry point also handles an unused formal. -/
example :
    (wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

example (result : WordSsaState × List Nat × WordProg (RiscV.Word 64) ×
    WordSpillState)
    (hresult :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences [2]
        (.skip : WordProg (RiscV.Word 64)) = some result) :
    ∀ name, name ∈ result.2.1 →
      ∃ location, lookupNatInfo name result.2.2.2.locations = some location := by
  exact wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_maps_parameters
    [2] (.skip : WordProg (RiscV.Word 64)) result.1 result.2.1
    result.2.2.1 result.2.2.2 hresult

end Flapjack
