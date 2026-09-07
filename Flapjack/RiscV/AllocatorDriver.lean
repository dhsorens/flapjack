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
  deriving Repr

def wordFunctionAllocationResultIsOracle :
    Option (WordFunctionAllocationResult α) → Bool
  | some (.oracle _ _ _) => true
  | _ => false

def wordFunctionAllocationResultIsGraph :
    Option (WordFunctionAllocationResult α) → Bool
  | some (.graph _ _ _ _) => true
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

end Flapjack
