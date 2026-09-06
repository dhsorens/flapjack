import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def wordOperationTestConfig : WordStackConfig :=
  { locations := [(0, .register 5), (1, .register 6),
      (2, .register 7), (3, .register 8)]
    scratch := 31
    stackBase := 10 }

example :
    wordStackStoreNameNat (.bitmapBase : WordStore Nat) = some .bitmapBase := by
  rfl

example :
    wordToStackProgNat wordOperationTestConfig
        (.get 0 .heapLength : WordProg Nat) =
      some (.get 5 .heapLength) := by
  simp [wordToStackProgNat, wordStackGet, wordStackStoreNameNat,
    wordStackStoreName, wordStackLocation, lookupNatInfo,
    wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.opCurrHeap .add 0 1 : WordProg Nat) =
      some (.opCurrHeap .add 5 6) := by
  simp [wordToStackProgNat, wordStackOpCurrHeap, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin,
    wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.install 0 1 2 3 ([], []) : WordProg Nat) =
      some (.install 5 6 7 8 0) := by
  simp [wordToStackProgNat, wordStackInstall, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.codeBufferWrite 0 1 : WordProg Nat) =
      some (.codeBufferWrite 5 6) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.dataBufferWrite 1 2 : WordProg Nat) =
      some (.dataBufferWrite 6 7) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

def wordOperationSpillConfig : WordStackConfig :=
  { locations := [(0, .stack 3), (1, .register 6)]
    scratch := 31
    stackBase := 10 }

example :
    wordToStackProgNat wordOperationSpillConfig
        (.get 0 .heapLength : WordProg Nat) =
      some (.seq (.get 31 .heapLength) (.stackStore 31 13)) := by
  simp [wordToStackProgNat, wordStackGet, wordStackStoreNameNat,
    wordStackStoreName, wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin,
    wordOperationSpillConfig]

example :
    wordToStackProgNat wordOperationSpillConfig
        (.opCurrHeap .add 0 1 : WordProg Nat) =
      some (.seq (.opCurrHeap .add 31 6) (.stackStore 31 13)) := by
  simp [wordToStackProgNat, wordStackOpCurrHeap, wordStackReadRegister,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin,
    wordOperationSpillConfig]

end Flapjack
