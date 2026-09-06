import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def wordBitmapTestConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    stackBase := 10
    specialScratch := 28 }

example :
    wordStackBitsToNat [true, false] = 5 := by
  rfl

example :
    wordStackBitmapChunk [(true, 7), (false, 9)] = [5, 7, 9] := by
  rfl

example :
    wordStackConstBitmapWords 8 [(true, 7), (false, 9)] = [5, 7, 9] := by
  rfl

example :
    wordStackInsertBitmap (wordStackInitialBitmaps false) [5, 7, 9] =
      ({ data := [4, 5, 7, 9], length := 4 }, 1) := by
  rfl

example :
    wordStackLiveBitmap 1 3 8 [2] = [28] := by
  rfl

example :
    wordStackAllocWithBitmaps wordBitmapTestConfig 30 3
        (wordStackInitialBitmaps false) [2] 1 8 =
      (.seq (.seq (.const 30 2) (.stackStore 30 10)) (.alloc 1),
        { data := [4, 28], length := 2 }) := by
  rfl

example :
    wordStackStoreConstsWithBitmaps wordBitmapTestConfig 1 28 8 none
        (wordStackInitialBitmaps false) [(true, 7), (false, 9)] =
      (.seq (.const 28 1) (.storeConsts 1 2 none),
        { data := [4, 5, 7, 9], length := 4 }) := by
  rfl

example :
    wordToStackProgNatWithBitmaps wordBitmapTestConfig 1 30 3 8 none
        (wordStackInitialBitmaps false)
        (.seq
          (.alloc 0 ([], [2]))
          (.storeConsts 0 1 2 3 [(true, 7), (false, 9)])) =
      some
        (.seq
          (.seq (.seq (.const 30 2) (.stackStore 30 10)) (.alloc 1))
          (.seq (.const 28 2) (.storeConsts 1 2 none)),
          { data := [4, 28, 5, 7, 9], length := 5 }) := by
  simp [wordToStackProgNatWithBitmaps, wordToStackProgNatWithBitmapBuilder,
    wordStackAllocWithBitmaps, wordStackAllocWithBitmapBuilder,
    wordStackStoreConstsWithBitmaps, wordStackBitmapWrite,
    wordStackBitmapWriteWithBuilder,
    wordStackInsertBitmap, wordStackLiveBitmap, wordStackConstBitmapWords,
    wordStackConstBitmapWordsAux, wordStackBitmapWords,
    wordStackBitmapWordsAux, wordStackInitialBitmaps, wordStackJoin,
    wordStackOffset, wordStackBitsToNat, wordStackBitmapChunk,
    wordBitmapTestConfig]
  native_decide

end Flapjack
