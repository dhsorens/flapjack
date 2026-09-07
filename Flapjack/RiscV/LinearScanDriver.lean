import Flapjack.RiscV.LinearScan

/-!
# Function-level linear-scan allocation

This is the function boundary corresponding to CakeML's
`linear_scan_reg_alloc` path.  The Word function is SSA-renamed first, the
formal-parameter set is retained in the clash tree, and the checked
program-level linear allocator supplies the locations consumed by
`word_to_stack`.
-/

namespace Flapjack

def wordAllocateLinearScanFunction (parameters : List Nat)
    (program : WordProg α) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordLinearScanState × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordPreferenceMoves
    (wordProgPreferenceEdges renamedProgram)
  (wordLinearScanAllocateClashTreeChecked colours stackStart tree forced moves).map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

theorem wordAllocateLinearScanFunction_safe
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunction parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordLinearScanAllocationSafe
      (WordClashTree.seq
        (.set (wordSsaRenameFunction parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
      (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
      allocation = true := by
  simp [wordAllocateLinearScanFunction] at halloc
  rcases halloc with ⟨allocation', hchecked, rfl, rfl, rfl, rfl⟩
  exact wordLinearScanAllocateClashTreeChecked_safe
    colours stackStart
    (WordClashTree.seq
      (.set (wordSsaRenameFunction parameters program).2.fst)
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
    (wordPreferenceMoves
      (wordProgPreferenceEdges (wordSsaRenameFunction parameters program).2.snd))
    allocation' hchecked

theorem wordLinearScanLocationsComplete_mem
    (state : WordLinearScanState) (names : List Nat)
    (hcomplete : wordLinearScanLocationsComplete state names = true) :
    ∀ name, name ∈ names →
      ∃ location, lookupNatInfo name state.locations = some location := by
  induction names with
  | nil =>
      simp
  | cons head tail ih =>
      intro name hname
      simp only [wordLinearScanLocationsComplete, Bool.and_eq_true] at hcomplete
      rcases List.mem_cons.mp hname with hhead | htail
      · subst name
        cases hlookup : lookupNatInfo head state.locations with
        | none => simp [hlookup] at hcomplete
        | some location => exact ⟨location, rfl⟩
      · exact ih hcomplete.2 name htail

theorem wordAllocateLinearScanFunction_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunction parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateLinearScanFunction] at halloc
  rcases halloc with ⟨allocation', hchecked, rfl, rfl, rfl, rfl⟩
  have hsafe := wordLinearScanAllocateClashTreeChecked_safe
    colours stackStart
    (WordClashTree.seq
      (.set (wordSsaRenameFunction parameters program).2.fst)
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
    (wordPreferenceMoves
      (wordProgPreferenceEdges (wordSsaRenameFunction parameters program).2.snd))
    allocation' hchecked
  have hcomplete :
      wordLinearScanLocationsComplete allocation'
        (wordLiveTreeRegisters
          (wordGetLiveTree
      (WordClashTree.seq
        (.set (wordSsaRenameFunction parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])))) = true := by
    simp [wordLinearScanAllocationSafe] at hsafe
    exact hsafe.1.1
  intro name hname
  apply wordLinearScanLocationsComplete_mem allocation' _ hcomplete name
  simp [wordGetLiveTree, wordLiveTreeRegisters, wordListUnion, hname]

end Flapjack
