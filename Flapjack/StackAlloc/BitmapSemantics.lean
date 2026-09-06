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

theorem stackGcNatFilterBitmap_length_rest
    (bits : List Bool) (values selected rest : List StackGcNatValue)
    (hresult : stackGcNatFilterBitmap bits values = some (selected, rest)) :
    rest.length ≤ values.length := by
  induction bits generalizing values selected rest with
  | nil =>
      have hpair : ([], values) = (selected, rest) := by
        simpa [stackGcNatFilterBitmap] using hresult
      cases hpair
      exact Nat.le_refl _
  | cons bit bits ih =>
      cases values with
      | nil =>
          simp [stackGcNatFilterBitmap] at hresult
      | cons value values =>
          cases bit with
          | false =>
              simp only [stackGcNatFilterBitmap] at hresult
              exact Nat.le_trans (ih values selected rest hresult) (Nat.le_succ _)
          | true =>
              cases hrecursive : stackGcNatFilterBitmap bits values with
              | none =>
                  simp [stackGcNatFilterBitmap, hrecursive] at hresult
              | some pair =>
                  cases pair with
                  | mk selectedNext restNext =>
                      have hpair :
                          (value :: selectedNext, restNext) = (selected, rest) := by
                        simpa [stackGcNatFilterBitmap, hrecursive] using hresult
                      have hrest : restNext = rest := congrArg Prod.snd hpair
                      have hlen := ih values selectedNext restNext hrecursive
                      cases hrest
                      exact Nat.le_trans hlen (Nat.le_succ _)

theorem stackGcNatMapBitmap_length_remainders
    (bits : List Bool) (moved values mapped restMoved restValues : List StackGcNatValue)
    (hresult : stackGcNatMapBitmap bits moved values =
      some (mapped, restMoved, restValues)) :
    restMoved.length ≤ moved.length ∧ restValues.length ≤ values.length := by
  induction bits generalizing moved values mapped restMoved restValues with
  | nil =>
      have htuple : ([], moved, values) = (mapped, restMoved, restValues) := by
        simpa [stackGcNatMapBitmap] using hresult
      cases htuple
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons bit bits ih =>
      cases values with
      | nil =>
          simp [stackGcNatMapBitmap] at hresult
      | cons value values =>
          cases bit with
          | false =>
              cases hrecursive : stackGcNatMapBitmap bits moved values with
              | none =>
                  simp [stackGcNatMapBitmap, hrecursive] at hresult
              | some pair =>
                  cases pair with
                  | mk mappedNext restPair =>
                      cases restPair with
                      | mk restMovedNext restValuesNext =>
                          have htuple :
                              (value :: mappedNext, restMovedNext, restValuesNext) =
                                (mapped, restMoved, restValues) := by
                            simpa [stackGcNatMapBitmap, hrecursive] using hresult
                          have hlength :=
                            ih moved values mappedNext restMovedNext restValuesNext hrecursive
                          have hmoved : restMovedNext = restMoved :=
                            congrArg (fun triple => triple.2.1) htuple
                          have hvalues : restValuesNext = restValues :=
                            congrArg (fun triple => triple.2.2) htuple
                          cases hmoved
                          cases hvalues
                          exact ⟨hlength.1,
                            Nat.le_trans hlength.2 (Nat.le_succ _)⟩
          | true =>
              cases moved with
              | nil =>
                  simp [stackGcNatMapBitmap] at hresult
              | cons movedValue moved =>
                  cases hrecursive : stackGcNatMapBitmap bits moved values with
                  | none =>
                      simp [stackGcNatMapBitmap, hrecursive] at hresult
                  | some pair =>
                      cases pair with
                      | mk mappedNext restPair =>
                          cases restPair with
                          | mk restMovedNext restValuesNext =>
                              have htuple :
                                  (movedValue :: mappedNext, restMovedNext, restValuesNext) =
                                    (mapped, restMoved, restValues) := by
                                simpa [stackGcNatMapBitmap, hrecursive] using hresult
                              have hlength :=
                                ih moved values mappedNext restMovedNext restValuesNext hrecursive
                              have hmoved : restMovedNext = restMoved :=
                                congrArg (fun triple => triple.2.1) htuple
                              have hvalues : restValuesNext = restValues :=
                                congrArg (fun triple => triple.2.2) htuple
                              cases hmoved
                              cases hvalues
                              exact ⟨Nat.le_trans hlength.1 (Nat.le_succ _),
                                Nat.le_trans hlength.2 (Nat.le_succ _)⟩

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
