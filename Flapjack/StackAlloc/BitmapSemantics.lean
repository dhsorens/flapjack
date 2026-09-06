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

/-! Fuel-bounded counterparts of the CakeML stack codec.  The wrapper
    supplies one more step than the input stack length, which is enough for
    every successful recursive call because each frame consumes its header.
-/

def stackGcNatEncodeStackFuel (config : StackGcConfig)
    (bitmaps : List Nat) : Nat → List StackGcNatValue → Option (List StackGcNatValue)
  | 0, _ => none
  | fuel + 1, [] => none
  | fuel + 1, [.word 0] => some []
  | fuel + 1, .word 0 :: _ => none
  | fuel + 1, value :: values =>
      match stackGcNatFullReadBitmap config bitmaps value with
      | none => none
      | some bits =>
          match stackGcNatFilterBitmap bits values with
          | none => none
          | some (selected, rest) =>
              match stackGcNatEncodeStackFuel config bitmaps fuel rest with
              | none => none
              | some encoded => some (selected ++ encoded)

def stackGcNatEncodeStack (config : StackGcConfig)
    (bitmaps : List Nat) (stack : List StackGcNatValue) :
    Option (List StackGcNatValue) :=
  stackGcNatEncodeStackFuel config bitmaps (stack.length + 1) stack

def stackGcNatDecodeStackFuel (config : StackGcConfig)
    (bitmaps : List Nat) : Nat → List StackGcNatValue →
      List StackGcNatValue → Option (List StackGcNatValue)
  | 0, _, _ => none
  | fuel + 1, _, [] => none
  | fuel + 1, [], [.word 0] => some [.word 0]
  | fuel + 1, _, [.word 0] => none
  | fuel + 1, _, .word 0 :: _ => none
  | fuel + 1, encoded, value :: values =>
      match stackGcNatFullReadBitmap config bitmaps value with
      | none => none
      | some bits =>
          match stackGcNatMapBitmap bits encoded values with
          | none => none
          | some (mapped, restEncoded, restValues) =>
              match stackGcNatDecodeStackFuel config bitmaps fuel
                  restEncoded restValues with
              | none => none
              | some rest => some (value :: mapped ++ rest)

def stackGcNatDecodeStack (config : StackGcConfig)
    (bitmaps : List Nat) (encoded stack : List StackGcNatValue) :
    Option (List StackGcNatValue) :=
  stackGcNatDecodeStackFuel config bitmaps (stack.length + 1) encoded stack

structure StackGcValueRootsResult where
  values : List StackGcNatValue
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

def stackGcNatMoveValueRoots (config : StackGcConfig) :
    List StackGcNatValue → Nat → Nat → Nat → (Nat → Nat) → (Nat → Bool) →
      StackGcValueRootsResult
  | [], index, destination, _, memory, _ =>
      { values := []
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := true }
  | value :: values, index, destination, oldBase, memory, domain =>
      let moved := stackGcValueMove config value index destination oldBase
        memory domain
      let rest := stackGcNatMoveValueRoots config values moved.nextIndex
        moved.nextAddress oldBase moved.memory domain
      { values := moved.value :: rest.values
        nextIndex := rest.nextIndex
        nextAddress := rest.nextAddress
        memory := rest.memory
        condition := moved.condition && rest.condition }

structure StackGcBitmapMoveResult where
  values : List StackGcNatValue
  remainder : List StackGcNatValue
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

def stackGcNatMoveBitmap (config : StackGcConfig)
    (bitmaps : List Nat) (descriptor : StackGcNatValue)
    (stack : List StackGcNatValue) (index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    Option StackGcBitmapMoveResult :=
  match stackGcNatFullReadBitmap config bitmaps descriptor with
  | none => none
  | some bits =>
      match stackGcNatFilterBitmap bits stack with
      | none => none
      | some (selected, remainder) =>
          let moved := stackGcNatMoveValueRoots config selected index destination
            oldBase memory domain
          match stackGcNatMapBitmap bits moved.values stack with
          | none => none
          | some (values, _, _) =>
              some
                { values := values
                  remainder := remainder
                  nextIndex := moved.nextIndex
                  nextAddress := moved.nextAddress
                  memory := moved.memory
                  condition := moved.condition }

def stackGcNatMoveRootsBitmaps (config : StackGcConfig)
    (bitmaps : List Nat) (stack : List StackGcNatValue)
    (index destination oldBase : Nat) (memory : Nat → Nat) (domain : Nat → Bool) :
    Option StackGcValueRootsResult :=
  match stackGcNatEncodeStack config bitmaps stack with
  | none => none
  | some encoded =>
      let moved := stackGcNatMoveValueRoots config encoded index destination
        oldBase memory domain
      match stackGcNatDecodeStack config bitmaps moved.values stack with
      | none => none
      | some values =>
          some
            { values := values
              nextIndex := moved.nextIndex
              nextAddress := moved.nextAddress
              memory := moved.memory
              condition := moved.condition }

def stackGcNatFullBitmaps (config : StackGcConfig)
    (bitmaps : List Nat) (stack : List StackGcNatValue)
    (newBase oldBase : Nat) (memory : Nat → Nat) (domain : Nat → Bool)
    (fuel : Nat) : Option StackGcValueRootsResult :=
  match stackGcNatMoveRootsBitmaps config bitmaps stack 0 newBase oldBase
      memory domain with
  | none => none
  | some moved =>
      let scanned := stackGcNatMoveLoop config fuel newBase moved.nextIndex
        moved.nextAddress oldBase moved.memory domain moved.condition
      some
        { values := moved.values
          nextIndex := scanned.nextIndex
          nextAddress := scanned.nextAddress
          memory := scanned.memory
          condition := scanned.condition }

theorem stackGcNatMoveValueRoots_length (config : StackGcConfig)
    (values : List StackGcNatValue) (index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveValueRoots config values index destination oldBase memory domain).values.length =
      values.length := by
  induction values generalizing index destination memory with
  | nil =>
      rfl
  | cons value values ih =>
      simp [stackGcNatMoveValueRoots, ih]

example :
    stackGcNatEncodeStack { wordBits := 8 } [3]
        [.word 1, .word 11, .word 0] = some [.word 11] := by
  native_decide

example :
    stackGcNatDecodeStack { wordBits := 8 } [3] [.word 11]
        [.word 1, .word 11, .word 0] = some [.word 1, .word 11, .word 0] := by
  native_decide

example :
    stackGcNatEncodeStack { wordBits := 8 } [3]
        [.word 1, .word 11] = none := by
  native_decide

example :
    stackGcNatDecodeStack { wordBits := 8 } [3] []
        [.word 1, .word 0] = none := by
  native_decide

example :
    (stackGcNatMoveValueRoots { wordBits := 8 }
      [.loc 4 0, .word 2] 0 100 0 (fun _ => 0) (fun _ => true)).values =
      [.loc 4 0, .word 2] := by
  native_decide

example :
    (stackGcNatMoveValueRoots { wordBits := 8 }
      [.loc 4 1] 0 100 0 (fun _ => 0) (fun _ => true)).condition = false := by
  native_decide

example :
    (stackGcNatMoveBitmap { wordBits := 8 } [3] (.word 1)
      [.word 2, .word 0] 0 100 0 (fun _ => 0) (fun _ => true)).map
        (fun result => result.values) = some [.word 2] := by
  native_decide

example :
    (stackGcNatMoveBitmap { wordBits := 8 } [3] (.word 1)
      [.word 2, .word 0] 0 100 0 (fun _ => 0) (fun _ => true)).map
        (fun result => result.remainder) = some [.word 0] := by
  native_decide

example :
    stackGcNatMoveBitmap { wordBits := 8 } [3] (.loc 1 0)
      [.word 2, .word 0] 0 100 0 (fun _ => 0) (fun _ => true) = none := by
  native_decide

example :
    (stackGcNatMoveRootsBitmaps { wordBits := 8 } [3]
      [.word 1, .word 2, .word 0] 0 100 0 (fun _ => 0) (fun _ => true)).map
        (fun result => result.values) =
      some [.word 1, .word 2, .word 0] := by
  native_decide

example :
    stackGcNatMoveRootsBitmaps { wordBits := 8 } [3]
      [.word 1, .word 2] 0 100 0 (fun _ => 0) (fun _ => true) = none := by
  native_decide

example :
    (stackGcNatFullBitmaps { wordBits := 8 } [3]
      [.word 1, .word 2, .word 0] 100 0 (fun _ => 0) (fun _ => true) 0).map
        (fun result => result.values) =
      some [.word 1, .word 2, .word 0] := by
  native_decide


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
