import Flapjack.RiscV.OracleAllocator

namespace Flapjack

example :
    wordOracleColouringOk 13 26
      (.delta [4] [2]) [] [] = true := by
  native_decide

example :
    wordOracleColouringOk 13 26
      (.delta [3] [2]) [] [(3, 3)] = false := by
  native_decide

example :
    (wordAllocateFunctionWithOracle [2]
      (.assign 4 (.var 2) : WordProg Nat) 13 26 []).isSome = true := by
  native_decide

example (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat) (oracle : NatInfoMap Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracle parameters program colours stackStart oracle =
      some (state, renamedParameters, renamedProgram)) :
    wordOracleColouringOk colours stackStart
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
        oracle = true := by
  exact wordAllocateFunctionWithOracle_sound parameters program colours stackStart oracle
    state renamedParameters renamedProgram halloc

end Flapjack
