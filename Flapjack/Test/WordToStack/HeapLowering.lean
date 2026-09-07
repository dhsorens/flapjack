import Flapjack.RiscV.CorrectnessWordToStack

/-! Regressions for the state-threaded heap-producing Word-to-Stack leaves. -/

namespace Flapjack.RiscV

def heapLoweringConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    stackBase := 20 }

def heapLoweringInitial : WordStackBitmapState :=
  { data := [4]
    length := 1 }

example :
    wordToStackProgNatWithBitmapBuilder heapLoweringConfig (fun _ => [7])
      2 26 4 64 none heapLoweringInitial
      (.alloc 9 ([], [2]) : WordProg Nat) =
      some (.seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1),
        { data := [4, 7]
          length := 2 }) := by
  simpa [wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
    wordStackInsertBitmap, wordStackJoin, wordStackOffset,
    heapLoweringConfig, heapLoweringInitial] using
    (wordToStackProgNatWithBitmapBuilder_alloc
      (config := heapLoweringConfig) (bitmapBuilder := fun _ => [7])
      (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
      (wordBits := 64) (storeConstsStub := none)
      (state := heapLoweringInitial) (destination := 9)
      (nonGc := []) (gc := [2]))

example :
    wordToStackProgNatWithBitmapBuilder heapLoweringConfig (fun _ => [7])
      2 26 4 64 (some 77) heapLoweringInitial
      (.storeConsts 0 1 2 3 [(true, 9), (false, 10)] : WordProg Nat) =
      some (.seq (.const 28 1) (.storeConsts 2 3 (some 77)),
        { data := [4, 5, 9, 10]
          length := 4 }) := by
  simpa [wordStackStoreConstsWithBitmaps, wordStackConstBitmapWords,
    wordStackConstBitmapWordsAux, wordStackBitmapChunk, wordStackBitsToNat,
    wordStackInsertBitmap, heapLoweringConfig, heapLoweringInitial] using
    (wordToStackProgNatWithBitmapBuilder_storeConsts
      (config := heapLoweringConfig) (bitmapBuilder := fun _ => [7])
      (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
      (wordBits := 64) (storeConstsStub := some 77)
      (state := heapLoweringInitial) (source := 0) (bitmap := 1)
      (codeLength := 2) (dataLength := 3)
      (constants := [(true, 9), (false, 10)]))

end Flapjack.RiscV
