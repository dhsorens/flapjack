import Flapjack.Pipeline

namespace Flapjack

theorem wordAllocateSsaProgramWithSpills_example :
    wordAllocateSsaProgramWithSpills
        ({ current := [], next := 10 } : WordSsaState)
        ((.assign 1 (.var 0)) : WordProg Nat) =
      some (({ current := [(1, 10)], next := 14 },
        .assign 10 (.var 0),
        { locations := [(10, .register 12), (0, .register 2)],
          nextSpill := 0 }) : WordSsaState × WordProg Nat × WordSpillState) := by
  simp [wordAllocateSsaProgramWithSpills, wordSsaRenameProgram,
    wordSsaRenameProgramWithLoops, wordSsaRenameExp, wordSsaFresh,
    wordSsaRead, wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordProgVariables, wordAllocateVarsWithSpills,
    wordGreedyAllocateWithSpills, wordUsedLocationRegisters,
    wordColourCandidates, wordFirstAvailable, wordNeighbours,
    wordPreferredRegister, wordAllocatableRegisters,
    wordSpillAllocationRespectsClashes, lookupNatInfo,
    wordProgSpecialLocationsSafe,
    wordExpReadVars, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

example :
    wordSpillAllocationRespectsClashes
        (wordProgClashAnalysis ((.assign 10 (.var 0)) : WordProg Nat) []).snd
        [(10, .register 12), (0, .register 2)] = true := by
  apply wordAllocateSsaProgramWithSpills_respects_clashes
    ({ current := [], next := 10 } : WordSsaState)
    ((.assign 1 (.var 0)) : WordProg Nat)
    ({ current := [(1, 10)], next := 14 } : WordSsaState)
    ((.assign 10 (.var 0)) : WordProg Nat)
    { locations := [(10, .register 12), (0, .register 2)], nextSpill := 0 }
  exact wordAllocateSsaProgramWithSpills_example

example :
    ∀ name, name ∈ [10] →
      ∃ location, lookupNatInfo name
        ([(10, .register 12), (0, .register 2)] : NatInfoMap WordLocation) =
        some location := by
  have halloc : wordAllocateSsaProgramWithSpills
        ({ current := [], next := 10 } : WordSsaState)
        ((.assign 1 (.var 0)) : WordProg Nat) =
      some (({ current := [(1, 10)], next := 14 },
        .assign 10 (.var 0),
        { locations := [(10, .register 12), (0, .register 2)],
          nextSpill := 0 }) : WordSsaState × WordProg Nat × WordSpillState) := by
    simp [wordAllocateSsaProgramWithSpills, wordSsaRenameProgram,
      wordSsaRenameProgramWithLoops, wordSsaRenameExp, wordSsaFresh,
      wordSsaRead, wordProgClashAnalysis, wordProgReadVars,
      wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
      wordClashPairs, wordProgVariables, wordAllocateVarsWithSpills,
      wordGreedyAllocateWithSpills, wordUsedLocationRegisters,
      wordColourCandidates, wordFirstAvailable, wordNeighbours,
      wordPreferredRegister, wordAllocatableRegisters,
      wordSpillAllocationRespectsClashes, lookupNatInfo,
      wordProgSpecialLocationsSafe,
      wordExpReadVars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop]
  have h := wordAllocateSsaProgramWithSpills_maps_variables
    ({ current := [], next := 10 } : WordSsaState)
    ((.assign 1 (.var 0)) : WordProg Nat)
    ({ current := [(1, 10)], next := 14 } : WordSsaState)
    ((.assign 10 (.var 0)) : WordProg Nat)
    { locations := [(10, .register 12), (0, .register 2)], nextSpill := 0 }
    halloc
  intro name hname
  simp at hname
  rcases hname with rfl
  apply h
  simp [wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordExpReadVars]

example :
    (wordAllocateVarsWithSpills (List.range 29)
      (wordPairwiseClashes (List.range 29))).map
        (fun state => state.nextSpill != 0) = some true := by
  exact wordAllocateVarsWithSpills_spills_example

example :
    wordClashTree
        (.seq (.assign 4 (.var 2))
          (.inst (.arith (.longMul 5 6 4 3))) : WordProg Nat) [] =
      .seq (.delta [4] [2]) (.delta [5, 6] [3, 4]) := by
  simp [wordClashTree, wordClashTreeDeltaInst, wordExpReadVars]

example :
    wordClashTree
        (.ite .equal 1 (.reg 2)
          (.return 0 [3]) (.return 0 [4]) : WordProg Nat) [] =
      .seq (.delta [] [1, 2])
        (.branch none (.delta [] [3]) (.delta [] [4])) := by
  simp [wordClashTree]

example :
    wordClashTree
        (.loop [1]
          (.seq (.continue 0) (.break 0)) [2] : WordProg Nat) [] =
      .seq (.set [1])
        (.seq (.set [2])
          (.seq (.seq (.set [1]) (.set [2])) (.set [1]))) := by
  simp [wordClashTree, wordClashTreeFindLoopFrame]

example :
    wordCheckColour id [1, 2] =
      some ([1, 2], [1, 2]) := by
  native_decide

example :
    wordCheckColour (fun _ => 0) [1, 2] = none := by
  native_decide

example :
    wordClashTreeCheck id
        (wordClashTree
          (.seq (.assign 0 (.var 1)) (.assign 2 (.var 1)) : WordProg Nat) []) [] [] =
      some ([1], [1]) := by
  native_decide

example :
    wordClashTreeCheck (fun _ => 0)
        (wordClashTree
          (.seq (.assign 0 (.var 1)) (.assign 2 (.var 1)) : WordProg Nat) []) [] [] =
      none := by
  native_decide

example :
    ([1] : List Nat).Nodup := by
  have hcheck :
      wordClashTreeCheck id
          (wordClashTree
            (.seq (.assign 0 (.var 1)) (.assign 2 (.var 1)) : WordProg Nat) [])
          [] [] = some ([1], [1]) := by
    native_decide
  have hsound := wordClashTreeCheck_sound id
    (wordClashTree
      (.seq (.assign 0 (.var 1)) (.assign 2 (.var 1)) : WordProg Nat) [])
    [] [] [1] [1] (fun _ _ h => h) (by simp) (by simp) (by simp) hcheck
  exact hsound.1

example :
    wordAllocateSsaProgramWithClashTreeWithSpills
        ({ current := [], next := 10 } : WordSsaState)
        ((.assign 1 (.var 0)) : WordProg Nat) =
      some (({ current := [(1, 10)], next := 14 },
        .assign 10 (.var 0),
        { locations := [(10, .register 12), (0, .register 2)],
          nextSpill := 0 }) : WordSsaState × WordProg Nat × WordSpillState) := by
  simp [wordAllocateSsaProgramWithClashTreeWithSpills,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRenameExp,
    wordSsaFresh, wordSsaRead, wordClashTree, wordClashTreeAnalyze,
    wordClashPairs, wordListUnion, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordExpReadVars, wordAllocateVarsWithSpills,
    wordGreedyAllocateWithSpills, wordUsedLocationRegisters,
    wordColourCandidates, wordFirstAvailable, wordNeighbours,
    wordPreferredRegister, wordAllocatableRegisters,
    wordSpillAllocationRespectsClashes, 
    wordProgSpecialLocationsSafe, lookupNatInfo, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordAllocateVarsWithSpillsAndPreferences [0, 4] [] [(4, 0)] =
      some (⟨[(4, .register 2), (0, .register 2)], 0⟩ : WordSpillState) := by
  rfl

example :
    wordAllocateVarsWithSpillsAndPreferences [0, 4] [(0, 4)] [(4, 0)] =
      some (⟨[(4, .register 6), (0, .register 2)], 0⟩ : WordSpillState) := by
  rfl

example (slots : List Nat) (edges preferences : List (Nat × Nat))
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpillsAndPreferences slots edges preferences =
      some state) :
    wordSpillAllocationRespectsClashes edges state.locations = true := by
  exact wordAllocateVarsWithSpillsAndPreferences_sound slots edges preferences
    state hstate

example :
    wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences
        ({ current := [], next := 10 } : WordSsaState)
        ((.assign 1 (.var 0)) : WordProg Nat) =
      some (({ current := [(1, 10)], next := 14 },
        .assign 10 (.var 0),
        { locations := [(10, .register 2), (0, .register 2)],
          nextSpill := 0 }) : WordSsaState × WordProg Nat × WordSpillState) := by
  simp [wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRenameExp,
    wordSsaFresh, wordSsaRead, wordClashTree, wordClashTreeAnalyze,
    wordClashPairs, wordListUnion, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordExpReadVars,
    wordAllocateVarsWithSpillsAndPreferences,
    wordGreedyAllocateWithSpillsAndPreferences,
    wordPreferenceLocationRegisters,
    wordColourCandidatesWithSpillPreferences,
    wordUsedLocationRegisters, wordColourCandidates, wordFirstAvailable,
    wordNeighbours, wordPreferredRegister, 
    wordAllocatableRegisters, wordSpillAllocationRespectsClashes,
    wordProgSpecialLocationsSafe,
    wordProgPreferenceEdges, lookupNatInfo, wordSpillClashTreeChecked,
    wordSpillLocationColour, wordClashTreeCheck, wordCheckPartialColour,
    wordNumSetDelete, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

example (slots : List Nat) (edges : List (Nat × Nat))
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpills slots edges = some state)
    (name : Nat) (hname : name ∈ slots.eraseDups) :
    ∃ location, lookupNatInfo name state.locations = some location := by
  exact wordAllocateVarsWithSpills_maps_slots slots edges state hstate name hname

example (slots : List Nat) (edges preferences : List (Nat × Nat))
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpillsAndPreferences slots edges preferences =
      some state)
    (name : Nat) (hname : name ∈ slots.eraseDups) :
    ∃ location, lookupNatInfo name state.locations = some location := by
  exact wordAllocateVarsWithSpillsAndPreferences_maps_slots slots edges
    preferences state hstate name hname

example :
    wordProgSpecialLocationsSafe
        [(0, .stack 0), (1, .register 5), (2, .register 6), (3, .register 7)]
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat) = true := by
  native_decide

example :
    wordProgSpecialLocationsSafe
        [(0, .register 4), (1, .register 5), (2, .register 6),
          (3, .register 7), (4, .register 8)]
        ((.seq (.inst (.arith (.addCarry 0 1 2 3 4))) .skip) : WordProg Nat) = true := by
  native_decide

example :
    wordProgSpecialLocationsSafe
        [(0, .stack 0), (1, .register 5), (2, .stack 1),
          (3, .register 6), (4, .stack 2)]
        ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat) = true := by
  native_decide

end Flapjack
