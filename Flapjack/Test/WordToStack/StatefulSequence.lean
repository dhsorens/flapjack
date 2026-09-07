import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for composing a bitmap-changing allocation with a later FFI
    through the state-threaded Word-to-Stack compiler. -/

namespace Flapjack.RiscV

def statefulSequenceConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .stack 2),
      (2, .register 6), (3, .stack 4)]
    scratch := 31
    stackBase := 20 }

def statefulSequenceInitial : WordStackBitmapState :=
  { data := [4]
    length := 1 }

example :
    wordToStackProgNatWithBitmapBuilder statefulSequenceConfig (fun _ => [7])
      2 26 4 64 none statefulSequenceInitial
      (.seq (.alloc 9 ([], [2]))
        (.ffi "echo" 0 1 2 3 ([], [4])) : WordProg Nat) =
      some
        (.seq
          (.seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1))
          (.seq (.arith .or 10 4 4)
            (.seq (.stackLoad 11 22)
              (.seq (.arith .or 12 6 6)
                (.seq (.stackLoad 13 24)
                  (.ffi "echo" 10 11 12 13 0))))),
          { data := [4, 7]
            length := 2 }) := by
  apply wordToStackProgNatWithBitmapBuilder_seq
    (config := statefulSequenceConfig) (bitmapBuilder := fun _ => [7])
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulSequenceInitial)
    (state1 := { data := [4, 7], length := 2 })
    (finalState := { data := [4, 7], length := 2 })
    (first := (.alloc 9 ([], [2]) : WordProg Nat))
    (second := (.ffi "echo" 0 1 2 3 ([], [4]) : WordProg Nat))
    (firstCode := .seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1))
    (secondCode := .seq (.arith .or 10 4 4)
      (.seq (.stackLoad 11 22)
        (.seq (.arith .or 12 6 6)
          (.seq (.stackLoad 13 24)
            (.ffi "echo" 10 11 12 13 0))))
            )
  · simp [wordToStackProgNatWithBitmapBuilder,
      wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      wordStackInsertBitmap, wordStackJoin, wordStackOffset,
      statefulSequenceConfig, statefulSequenceInitial]
  · simp [wordToStackProgNatWithBitmapBuilder, wordToStackProgNat,
      wordStackFfi, wordStackFfiSourcesSafe, wordStackFfiSourceSafe,
      wordStackFfiRegisterSafe, wordStackFfiMove, wordStackJoin,
      wordStackLocation, lookupNatInfo, wordStackOffset,
      statefulSequenceConfig]

end Flapjack.RiscV
