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

end Flapjack
