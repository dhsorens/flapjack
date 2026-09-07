import Flapjack.RiscV.AllocatorDriver

/-!
Regression coverage for the composed CakeML allocator decision boundary.
The first example accepts a supplied colouring; the second deliberately
collides the two LongMul destinations under the oracle and therefore reaches
the graph allocator fallback.
-/

namespace Flapjack

example :
    wordFunctionAllocationResultIsOracle
      (wordAllocateFunctionWithOracleOrGraph
        [] (.skip : WordProg Nat) [] 13 26 []) = true := by
  decide +kernel

example :
    wordFunctionAllocationResultIsGraph
      (wordAllocateFunctionWithOracleOrGraph
        [] (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat)
        [] 13 26 []) = true := by
  decide +kernel

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (result : WordFunctionAllocationResult Nat)
    (halloc : wordAllocateFunctionWithOracleOrGraph parameters program
      fixedSources colours stackStart oracle = some result) :
    match result with
    | .oracle _ _ _ => True
    | .graph _ _ allocation _ =>
        wordGraphTagsAreFixed allocation.graph = true ∧
          wordGraphColouringRespectsEdges allocation.graph = true
    | .spill _ _ _ _ => True := by
  cases result with
  | oracle oracleState oracleParameters oracleProgram =>
      trivial
  | graph graphState graphParameters allocation graphProgram =>
      have hsound := wordAllocateFunctionWithOracleOrGraph_graph_sound
        parameters program fixedSources colours stackStart oracle graphState
        graphParameters allocation graphProgram halloc
      exact ⟨hsound.1, hsound.2.1⟩
  | spill spillState spillParameters allocation spillProgram =>
      trivial

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (result : WordFunctionAllocationResult Nat)
    (halloc : wordAllocateFunctionWithOracleOrGraphOrSpill parameters program
      fixedSources colours stackStart oracle = some result) :
    match result with
    | .oracle _ _ _ => True
    | .graph _ _ allocation _ =>
        wordGraphTagsAreFixed allocation.graph = true ∧
          wordGraphColouringRespectsEdges allocation.graph = true
    | .spill _ _ allocation _ =>
        wordSpillAllocationRespectsClashes
          (wordClashTreeAnalyze
            (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
            []).snd allocation.locations = true := by
  have hsound := wordAllocateFunctionWithOracleOrGraphOrSpill_sound
    parameters program fixedSources colours stackStart oracle result halloc
  cases result with
  | oracle state parameters' program' =>
      trivial
  | graph state parameters' allocation program' =>
      exact ⟨hsound.1, hsound.2.1⟩
  | spill state parameters' allocation program' =>
      exact hsound.1

end Flapjack
