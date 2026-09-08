import Flapjack.RiscV.SpillCosts
import Flapjack.RiscV.AllocatorDriver

/-!
# Heuristic function-allocation driver

This is the executable composition corresponding to CakeML's allocator
decision boundary: an accepted oracle wins first, then the prioritized graph
allocator is attempted, and finally the checked spill allocator is used.  The
linear-scan and Simple/IRC distinctions remain explicit future work; the
current graph engine is the implementation used by this boundary.
-/

namespace Flapjack

def wordAllocateFunctionWithOracleOrHeuristicOrSpill
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
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
    match wordAllocateGraphFunctionWithHeuristics parameters program fixedSources
        algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

def wordHeuristicDriverUsesOracle
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsOracle result

def wordHeuristicDriverUsesGraph
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsGraph result

def wordHeuristicDriverUsesSpill
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsSpill result

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpill_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpill parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpill] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart with
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value => simp [hgraph, hspill] at halloc
    | some value =>
        cases value with
        | mk graphState rest =>
            cases rest with
            | mk graphParameters rest =>
                cases rest with
                | mk graphAllocation graphProgram =>
                    simp [hgraph] at halloc
                    rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                    exact wordAllocateGraphFunctionWithHeuristics_sound
                      parameters program fixedSources algorithm currentFunction
                      colours stackStart graphState graphParameters
                      graphAllocation graphProgram hgraph

/-! Full-SSA version of the heuristic decision boundary.  The entry moves
    are included in the oracle check, graph allocation, and spill fallback. -/
def wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else
    match wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
        fixedSources algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters
      program fixedSources algorithm currentFunction colours stackStart with
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value => simp [hgraph, hspill] at halloc
    | some value =>
        cases value with
        | mk graphState rest =>
            cases rest with
            | mk graphParameters rest =>
                cases rest with
                | mk graphAllocation graphProgram =>
                    simp [hgraph] at halloc
                    rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                    exact wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound
                      parameters program fixedSources algorithm currentFunction
                      colours stackStart graphState graphParameters
                      graphAllocation graphProgram hgraph

end Flapjack
