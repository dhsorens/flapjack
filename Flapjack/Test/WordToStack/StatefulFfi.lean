import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for state-threaded FFI lowering. -/

namespace Flapjack.RiscV

def statefulFfiConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7)]
    scratch := 31
    stackBase := 10 }

def statefulFfiBitmaps : WordStackBitmapState :=
  { data := [4, 12]
    length := 2 }

example :
    wordToStackProgNatWithBitmapBuilder statefulFfiConfig (fun live => live)
      2 26 4 64 none statefulFfiBitmaps
      (.ffi "echo" 0 1 2 3 ([], [4]) : WordProg Nat) =
      some (.seq (.arith .or 10 4 4)
        (.seq (.arith .or 11 5 5)
          (.seq (.arith .or 12 6 6)
            (.seq (.arith .or 13 7 7)
              (.ffi "echo" 10 11 12 13 0)))), statefulFfiBitmaps) := by
  apply wordToStackProgNatWithBitmapBuilder_ffi
    (config := statefulFfiConfig) (bitmapBuilder := fun live => live)
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulFfiBitmaps) (function := "echo")
    (configuration := 0) (configurationLength := 1) (array := 2)
    (arrayLength := 3) (live := ([], [4]))
    (configurationMove := .arith .or 10 4 4)
    (configurationLengthMove := .arith .or 11 5 5)
    (arrayMove := .arith .or 12 6 6)
    (arrayLengthMove := .arith .or 13 7 7)
  all_goals simp [statefulFfiConfig,
    wordStackFfiSourcesSafe, wordStackFfiSourceSafe,
    wordStackFfiRegisterSafe, wordStackFfiMove, wordStackLocation,
    lookupNatInfo]

end Flapjack.RiscV
