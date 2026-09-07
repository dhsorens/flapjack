import Flapjack.RiscV.HeuristicDriver

/-! Regression coverage for the composed heuristic allocation decision. -/

namespace Flapjack

example :
    wordHeuristicDriverUsesOracle
      (wordAllocateFunctionWithOracleOrHeuristicOrSpill
        [] (.skip : WordProg Nat) [] 1 7 13 26 []) = true := by
  native_decide

example :
    wordHeuristicDriverUsesGraph
      (wordAllocateFunctionWithOracleOrHeuristicOrSpill
        [] (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat)
          [] 1 7 13 26 []) = true := by
  native_decide

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg Nat)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpill parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true := by
  exact (wordAllocateFunctionWithOracleOrHeuristicOrSpill_graph_sound
    parameters program fixedSources algorithm currentFunction colours stackStart
    oracle state renamedParameters allocation renamedProgram halloc).1

end Flapjack
