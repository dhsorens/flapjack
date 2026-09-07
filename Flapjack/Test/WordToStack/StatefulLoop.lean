import Flapjack.RiscV.CorrectnessWordToStack

/-! Regressions for state-threaded loop and MustTerminate compilation. -/

namespace Flapjack.RiscV

def statefulLoopConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    stackBase := 20 }

def statefulLoopInitial : WordStackBitmapState :=
  { data := [4]
    length := 1 }

example :
    wordToStackProgNatWithBitmapBuilder statefulLoopConfig (fun _ => [7])
      2 26 4 64 none statefulLoopInitial
      (.loop [0] (.alloc 9 ([], [2])) [0] : WordProg Nat) =
      some (.loop (.seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1)),
        { data := [4, 7]
          length := 2 }) := by
  apply wordToStackProgNatWithBitmapBuilder_loop
    (config := statefulLoopConfig) (bitmapBuilder := fun _ => [7])
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulLoopInitial)
    (finalState := { data := [4, 7], length := 2 })
    (liveIn := [0]) (liveOut := [0])
    (body := (.alloc 9 ([], [2]) : WordProg Nat))
    (bodyCode := .seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1))
  simp [wordToStackProgNatWithBitmapBuilder,
    wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
    wordStackInsertBitmap, wordStackJoin, wordStackOffset,
    statefulLoopConfig, statefulLoopInitial]

example :
    wordToStackProgNatWithBitmapBuilder statefulLoopConfig (fun _ => [7])
      2 26 4 64 none statefulLoopInitial
      (.mustTerminate (.skip : WordProg Nat)) =
      some (.skip, statefulLoopInitial) := by
  apply wordToStackProgNatWithBitmapBuilder_mustTerminate
    (config := statefulLoopConfig) (bitmapBuilder := fun _ => [7])
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulLoopInitial) (finalState := statefulLoopInitial)
    (body := (.skip : WordProg Nat)) (bodyCode := .skip)
  simp [wordToStackProgNatWithBitmapBuilder, wordToStackProgNat]

end Flapjack.RiscV
