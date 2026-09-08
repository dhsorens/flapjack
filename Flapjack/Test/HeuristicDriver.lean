import Flapjack.RiscV.HeuristicDriver

/-! Regression coverage for the composed heuristic allocation decision. -/

namespace Flapjack

example :
    wordHeuristicDriverUsesOracle
      (wordAllocateFunctionWithOracleOrHeuristicOrSpill
        [] (.skip : WordProg Nat) [] 1 7 13 26 []) = true := by
  decide +kernel

example :
    wordHeuristicDriverUsesGraph
      (wordAllocateFunctionWithOracleOrHeuristicOrSpill
        [] (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat)
          [] 1 7 13 26 []) = true := by
  decide +kernel

example :
    wordHeuristicDriverUsesOracle
      (wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry
        [] (.skip : WordProg Nat) [] 1 7 13 26 []) = true := by
  decide +kernel

example :
    wordHeuristicDriverUsesGraph
      (wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry
        [] (.inst (.arith (.longMul 0 1 2 3)) : WordProg Nat)
          [] 1 7 13 26 []) = true := by
  decide +kernel

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

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (renamedProgram : WordProg Nat)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.oracle state renamedParameters renamedProgram)) :
    wordOracleColouringOk colours stackStart
      (WordClashTree.seq
        (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
      (wordProgForcedClashes
        (wordSsaRenameFunctionWithEntry parameters program).2.snd) oracle = true := by
  exact wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_oracle_sound
    parameters program fixedSources algorithm currentFunction colours stackStart
    oracle state renamedParameters renamedProgram halloc

example (parameters : List Nat) (program : WordProg Nat)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordSpillState)
    (renamedProgram : WordProg Nat)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.spill state renamedParameters allocation renamedProgram)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true := by
  exact (wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_spill_sound
    parameters program fixedSources algorithm currentFunction colours stackStart
    oracle state renamedParameters allocation renamedProgram halloc).1

end Flapjack
