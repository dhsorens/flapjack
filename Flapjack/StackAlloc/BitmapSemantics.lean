import Flapjack.StackAlloc.Correctness

namespace Flapjack

/-!
  Bitmap words are stored least-significant bit first.  A set high bit marks
  another bitmap word, while the final word uses its highest set bit as the
  terminator.  These definitions are the Nat-executable counterpart of
  CakeML bit_length, get_bits, read_bitmap, and full_read_bitmap.
-/

def stackGcNatBitLength : Nat → Nat
  | 0 => 0
  | value + 1 => stackGcNatBitLength ((value + 1) / 2) + 1
termination_by value => value
decreasing_by
  omega

def stackGcNatBitAt (value index : Nat) : Bool :=
  decide ((value / 2 ^ index) % 2 = 1)

def stackGcNatGetBits (value : Nat) : List Bool :=
  (List.range (stackGcNatBitLength value - 1)).map
    (stackGcNatBitAt value)

def stackGcNatBitmapBits (config : StackGcConfig) (value : Nat) : List Bool :=
  (List.range (config.wordBits - 1)).map (stackGcNatBitAt value)

def stackGcNatWordMsb (config : StackGcConfig) (value : Nat) : Bool :=
  stackGcNatBitAt value (config.wordBits - 1)

def stackGcNatReadBitmap (config : StackGcConfig) : List Nat → Option (List Bool)
  | [] => none
  | word :: words =>
      if stackGcNatWordMsb config word then
        do
          let rest ← stackGcNatReadBitmap config words
          pure (stackGcNatBitmapBits config word ++ rest)
      else
        some (stackGcNatGetBits word)

def stackGcNatFullReadBitmap (config : StackGcConfig)
    (bitmaps : List Nat) : StackGcNatValue → Option (List Bool)
  | .word value =>
      if value = 0 then none
      else stackGcNatReadBitmap config (bitmaps.drop (value - 1))
  | .loc _ _ => none

@[simp] theorem stackGcNatBitLength_zero :
    stackGcNatBitLength 0 = 0 := by
  simp [stackGcNatBitLength]

@[simp] theorem stackGcNatGetBits_zero :
    stackGcNatGetBits 0 = [] := by
  simp [stackGcNatGetBits, stackGcNatBitLength]

@[simp] theorem stackGcNatReadBitmap_nil (config : StackGcConfig) :
    stackGcNatReadBitmap config [] = none := by
  rfl

@[simp] theorem stackGcNatFullReadBitmap_zero (config : StackGcConfig)
    (bitmaps : List Nat) :
    stackGcNatFullReadBitmap config bitmaps (.word 0) = none := by
  rfl

example : stackGcNatGetBits 5 = [true, false] := by
  native_decide

example :
    stackGcNatReadBitmap { wordBits := 8 } [5] = some [true, false] := by
  native_decide

example :
    stackGcNatFullReadBitmap { wordBits := 8 } [5] (.word 1) =
      some [true, false] := by
  native_decide

end Flapjack
