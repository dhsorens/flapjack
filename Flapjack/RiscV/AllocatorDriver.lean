import Flapjack.RiscV.OracleAllocator
import Flapjack.RiscV.AllocatorCorrectness

/-!
The composed function-level allocator driver.

CakeML first tries a supplied colouring oracle.  If that colouring is not
accepted, it invokes the register allocator on the SSA-renamed program,
including the backward stack-only analysis and forced sources.  Keeping the
two outcomes explicit makes the boundary useful to later lowering and
correctness proofs without pretending that a failed allocation is a valid
compiler result.
-/

namespace Flapjack

inductive WordFunctionAllocationResult (α : Type) where
  | oracle (state : WordSsaState) (parameters : List Nat)
      (program : WordProg α)
  | graph (state : WordSsaState) (parameters : List Nat)
      (allocation : WordGraphAllocation) (program : WordProg α)
  | spill (state : WordSsaState) (parameters : List Nat)
      (allocation : WordSpillState) (program : WordProg α)
  deriving Repr

def wordFunctionAllocationResultIsOracle :
    Option (WordFunctionAllocationResult α) → Bool
  | some (.oracle _ _ _) => true
  | _ => false

def wordFunctionAllocationResultIsGraph :
    Option (WordFunctionAllocationResult α) → Bool
  | some (.graph _ _ _ _) => true
  | _ => false

def wordFunctionAllocationResultIsSpill :
    Option (WordFunctionAllocationResult α) → Bool
  | some (.spill _ _ _ _) => true
  | _ => false

def wordAllocateFunctionWithOracleOrGraph (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (colours stackStart : Nat) (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else
    match wordAllocateGraphFunctionWithStackOnlyRenamed parameters program
        fixedSources colours stackStart with
    | none => none
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)

/-!
Add the spill-aware CakeML-shaped allocator as a final fallback.  The graph
allocator is preferred because it retains its explicit interference graph;
the spill allocator remains available for programs whose graph colouring
cannot produce a result.
-/
def wordAllocateFunctionWithOracleOrGraphOrSpill (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (colours stackStart : Nat) (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  match wordAllocateFunctionWithOracleOrGraph parameters program fixedSources
      colours stackStart oracle with
  | some result => some result
  | none =>
      match wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
          parameters program with
      | none => none
      | some (state, renamedParameters, renamedProgram, allocation) =>
          some (.spill state renamedParameters allocation renamedProgram)

theorem wordAllocateFunctionWithOracleOrGraph_oracle_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracleOrGraph parameters program
      fixedSources colours stackStart oracle =
      some (.oracle state renamedParameters renamedProgram)) :
    wordOracleColouringOk colours stackStart
      (WordClashTree.seq
        (.set (wordSsaRenameFunction parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
      (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
      oracle = true := by
  simp [wordAllocateFunctionWithOracleOrGraph] at halloc
  split at halloc
  · assumption
  · cases hgraph : wordAllocateGraphFunctionWithStackOnlyRenamed parameters
      program fixedSources colours stackStart <;> simp [hgraph] at halloc

theorem wordAllocateFunctionWithOracleOrGraph_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracleOrGraph parameters program
      fixedSources colours stackStart oracle =
      some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrGraph] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithStackOnlyRenamed parameters
      program fixedSources colours stackStart with
    | none => simp [hgraph] at halloc
    | some value =>
        cases value with
        | mk graphState rest =>
            cases rest with
            | mk graphParameters rest =>
                cases rest with
                | mk graphAllocation graphProgram =>
                    simp [hgraph] at halloc
                    rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                    exact wordAllocateGraphFunctionWithStackOnlyRenamed_sound
                      parameters program fixedSources colours stackStart
                      graphState graphParameters graphAllocation graphProgram hgraph

theorem wordAllocateFunctionWithOracleOrGraph_ne_spill
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordSpillState)
    (renamedProgram : WordProg α) :
    wordAllocateFunctionWithOracleOrGraph parameters program fixedSources
      colours stackStart oracle ≠
      some (.spill state renamedParameters allocation renamedProgram) := by
  intro halloc
  simp [wordAllocateFunctionWithOracleOrGraph] at halloc
  split at halloc
  · cases halloc
  · cases hgraph : wordAllocateGraphFunctionWithStackOnlyRenamed parameters
      program fixedSources colours stackStart <;> simp [hgraph] at halloc

theorem wordAllocateFunctionWithOracleOrGraphOrSpill_spill_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordSpillState)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracleOrGraphOrSpill parameters program
      fixedSources colours stackStart oracle =
      some (.spill state renamedParameters allocation renamedProgram)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunction parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
        allocation.locations = true := by
  cases hbase : wordAllocateFunctionWithOracleOrGraph parameters program
      fixedSources colours stackStart oracle with
  | some result =>
      cases result with
      | oracle oracleState oracleParameters oracleProgram =>
          simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase] at halloc
      | graph graphState graphParameters graphAllocation graphProgram =>
          simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase] at halloc
      | spill spillState spillParameters spillAllocation spillProgram =>
          exact False.elim (wordAllocateFunctionWithOracleOrGraph_ne_spill
            parameters program fixedSources colours stackStart oracle
            spillState spillParameters spillAllocation spillProgram hbase)
  | none =>
      cases hspill : wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
          parameters program with
      | none =>
          simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase, hspill] at halloc
      | some value =>
          cases value with
          | mk spillState rest =>
              cases rest with
              | mk spillParameters rest =>
                  cases rest with
                  | mk spillProgram spillAllocation =>
                      simp [wordAllocateFunctionWithOracleOrGraphOrSpill,
                        hbase, hspill] at halloc
                      rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                      exact wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_sound
                        parameters program spillState spillParameters spillProgram
                        spillAllocation hspill

/-! A single witness theorem for the allocator decision boundary.  Downstream
    lowering does not need to duplicate the oracle/graph/spill case split: a
    successful result carries exactly the contract belonging to its chosen
    allocation strategy. -/

theorem wordAllocateFunctionWithOracleOrGraphOrSpill_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (result : WordFunctionAllocationResult α)
    (halloc : wordAllocateFunctionWithOracleOrGraphOrSpill parameters program
      fixedSources colours stackStart oracle = some result) :
    match result with
    | .oracle _ _ _ =>
        wordOracleColouringOk colours stackStart
          (WordClashTree.seq
            (.set (wordSsaRenameFunction parameters program).2.fst)
            (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
          (wordProgForcedClashes
            (wordSsaRenameFunction parameters program).2.snd) oracle = true
    | .graph _ _ allocation _ =>
        wordGraphTagsAreFixed allocation.graph = true ∧
          wordGraphColouringRespectsEdges allocation.graph = true ∧
          (wordClashTreeCheck
            (wordGraphColouringAt allocation.colouring)
            (WordClashTree.seq
              (.set (wordSsaRenameFunction parameters program).2.fst)
              (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
            [] []).isSome = true
    | .spill _ _ allocation _ =>
        wordSpillAllocationRespectsClashes
            (wordClashTreeAnalyze
              (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
              []).snd allocation.locations = true ∧
          wordProgSpecialLocationsSafe allocation.locations
            (wordSsaRenameFunction parameters program).2.snd = true ∧
          wordSpillClashTreeChecked
            (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
            allocation.locations = true := by
  cases result with
  | oracle state parameters' program' =>
      have hbase : wordAllocateFunctionWithOracleOrGraph parameters program
          fixedSources colours stackStart oracle =
          some (.oracle state parameters' program') := by
        cases hbase' : wordAllocateFunctionWithOracleOrGraph parameters program
            fixedSources colours stackStart oracle with
        | none =>
            cases hspill : wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
                parameters program with
            | none =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase', hspill]
                  at halloc
            | some value =>
                cases value with
                | mk spillState rest =>
                    cases rest with
                    | mk spillParameters rest =>
                        cases rest with
                        | mk spillProgram spillAllocation =>
                            simp [wordAllocateFunctionWithOracleOrGraphOrSpill,
                              hbase', hspill] at halloc
        | some value =>
            cases value with
            | oracle baseState baseParameters baseProgram =>
                simpa [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase']
                  using halloc
            | graph baseState baseParameters baseAllocation baseProgram =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase'] at halloc
            | spill baseState baseParameters baseAllocation baseProgram =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase'] at halloc
      exact wordAllocateFunctionWithOracleOrGraph_oracle_sound
        parameters program fixedSources colours stackStart oracle state
        parameters' program' hbase
  | graph state parameters' allocation program' =>
      have hbase : wordAllocateFunctionWithOracleOrGraph parameters program
          fixedSources colours stackStart oracle =
          some (.graph state parameters' allocation program') := by
        cases hbase' : wordAllocateFunctionWithOracleOrGraph parameters program
            fixedSources colours stackStart oracle with
        | none =>
            cases hspill : wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
                parameters program with
            | none =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase', hspill]
                  at halloc
            | some value =>
                cases value with
                | mk spillState rest =>
                    cases rest with
                    | mk spillParameters rest =>
                        cases rest with
                        | mk spillProgram spillAllocation =>
                            simp [wordAllocateFunctionWithOracleOrGraphOrSpill,
                              hbase', hspill] at halloc
        | some value =>
            cases value with
            | oracle baseState baseParameters baseProgram =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase'] at halloc
            | graph baseState baseParameters baseAllocation baseProgram =>
                simpa [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase']
                  using halloc
            | spill baseState baseParameters baseAllocation baseProgram =>
                simp [wordAllocateFunctionWithOracleOrGraphOrSpill, hbase'] at halloc
      exact wordAllocateFunctionWithOracleOrGraph_graph_sound
        parameters program fixedSources colours stackStart oracle state
        parameters' allocation program' hbase
  | spill state parameters' allocation program' =>
      exact wordAllocateFunctionWithOracleOrGraphOrSpill_spill_sound
        parameters program fixedSources colours stackStart oracle state
        parameters' allocation program' halloc

end Flapjack
