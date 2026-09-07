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
  | Nat.succ fuel, [] => none
  | Nat.succ fuel, [.word 0] => some []
  | Nat.succ fuel, .word 0 :: _ => none
  | Nat.succ fuel, value :: values =>
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
  | Nat.succ fuel, _, [] => none
  | Nat.succ fuel, [], [.word 0] => some [.word 0]
  | Nat.succ fuel, _, [.word 0] => none
  | Nat.succ fuel, _, .word 0 :: _ => none
  | Nat.succ fuel, encoded, value :: values =>
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

theorem stackGcNatFilterBitmap_length_partition
    (bits : List Bool) (values selected rest : List StackGcNatValue)
    (hresult : stackGcNatFilterBitmap bits values = some (selected, rest)) :
    selected.length + rest.length + bits.count false = values.length := by
  induction bits generalizing values selected rest with
  | nil =>
      have hpair : ([], values) = (selected, rest) := by
        simpa [stackGcNatFilterBitmap] using hresult
      cases hpair
      simp
  | cons bit bits ih =>
      cases values with
      | nil =>
          simp [stackGcNatFilterBitmap] at hresult
      | cons value values =>
          cases bit with
          | false =>
              have hrecursive :
                  stackGcNatFilterBitmap bits values = some (selected, rest) := by
                simpa [stackGcNatFilterBitmap] using hresult
              have hlength := ih values selected rest hrecursive
              have hcount :
                  (false :: bits).count false = bits.count false + 1 := by
                simp
              rw [hcount]
              simp only [List.length_cons]
              omega
          | true =>
              cases hrecursive : stackGcNatFilterBitmap bits values with
              | none =>
                  simp [stackGcNatFilterBitmap, hrecursive] at hresult
              | some pair =>
                  cases pair with
                  | mk selectedNext restNext =>
                      have htuple :
                          (value :: selectedNext, restNext) = (selected, rest) := by
                        simpa [stackGcNatFilterBitmap, hrecursive] using hresult
                      have hlength := ih values selectedNext restNext hrecursive
                      have hselected : value :: selectedNext = selected :=
                        congrArg Prod.fst htuple
                      have hrest : restNext = rest :=
                        congrArg Prod.snd htuple
                      cases hselected
                      cases hrest
                      have hcount :
                          (true :: bits).count false = bits.count false := by
                        simp
                      rw [hcount]
                      simp only [List.length_cons]
                      omega

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

theorem stackGcNatFilterBitmap_mapBitmap_remainders
    (bits : List Bool) (values moved selected remainder mapped restMoved restValues :
      List StackGcNatValue)
    (hfilter : stackGcNatFilterBitmap bits values = some (selected, remainder))
    (hmoved : moved.length = selected.length)
    (hmap : stackGcNatMapBitmap bits moved values =
      some (mapped, restMoved, restValues)) :
    restMoved = [] ∧ restValues = remainder := by
  induction bits generalizing values moved selected remainder mapped restMoved restValues with
  | nil =>
      have hfilterPair : ([], values) = (selected, remainder) := by
        simpa [stackGcNatFilterBitmap] using hfilter
      have hmapTuple : ([], moved, values) = (mapped, restMoved, restValues) := by
        simpa [stackGcNatMapBitmap] using hmap
      cases hfilterPair
      cases hmapTuple
      have hmovedZero : moved.length = 0 := by
        simpa using hmoved
      cases moved with
      | nil =>
          exact ⟨rfl, rfl⟩
      | cons movedValue moved =>
          simp at hmovedZero
  | cons bit bits ih =>
      cases values with
      | nil =>
          simp [stackGcNatFilterBitmap] at hfilter
      | cons value values =>
          cases bit with
          | false =>
              cases hmapRec : stackGcNatMapBitmap bits moved values with
              | none =>
                  simp [stackGcNatMapBitmap, hmapRec] at hmap
              | some pair =>
                  cases pair with
                  | mk mappedNext restPair =>
                      cases restPair with
                      | mk restMovedNext restValuesNext =>
                          have htuple :
                              (value :: mappedNext, restMovedNext, restValuesNext) =
                                (mapped, restMoved, restValues) := by
                            simpa [stackGcNatMapBitmap, hmapRec] using hmap
                          have hbridge := ih values moved selected remainder
                            mappedNext restMovedNext restValuesNext hfilter hmoved hmapRec
                          have hmovedRest : restMovedNext = restMoved :=
                            congrArg (fun triple => triple.2.1) htuple
                          have hvaluesRest : restValuesNext = restValues :=
                            congrArg (fun triple => triple.2.2) htuple
                          cases hmovedRest
                          cases hvaluesRest
                          exact hbridge
          | true =>
              cases moved with
              | nil =>
                  simp [stackGcNatMapBitmap] at hmap
              | cons movedValue moved =>
                  cases hfilterRec : stackGcNatFilterBitmap bits values with
                  | none =>
                      simp [stackGcNatFilterBitmap, hfilterRec] at hfilter
                  | some filterPair =>
                      cases filterPair with
                      | mk selectedNext remainderNext =>
                          cases hmapRec : stackGcNatMapBitmap bits moved values with
                          | none =>
                              simp [stackGcNatMapBitmap, hmapRec] at hmap
                          | some mapPair =>
                              cases mapPair with
                              | mk mappedNext mapRest =>
                                  cases mapRest with
                                  | mk restMovedNext restValuesNext =>
                                      have hfilterTuple :
                                          (value :: selectedNext, remainderNext) =
                                            (selected, remainder) := by
                                        simpa [stackGcNatFilterBitmap, hfilterRec] using hfilter
                                      have htuple :
                                          (movedValue :: mappedNext, restMovedNext,
                                            restValuesNext) =
                                              (mapped, restMoved, restValues) := by
                                        simpa [stackGcNatMapBitmap, hmapRec] using hmap
                                      have hmovedRestLength : moved.length = selectedNext.length := by
                                        have hselected : selected = value :: selectedNext :=
                                          (congrArg Prod.fst hfilterTuple).symm
                                        simpa [hselected] using hmoved
                                      have hbridge := ih values moved selectedNext remainderNext
                                        mappedNext restMovedNext restValuesNext hfilterRec
                                        hmovedRestLength hmapRec
                                      have hrem : remainderNext = remainder :=
                                        congrArg Prod.snd hfilterTuple
                                      have hmovedRest : restMovedNext = restMoved :=
                                        congrArg (fun triple => triple.2.1) htuple
                                      have hvaluesRest : restValuesNext = restValues :=
                                        congrArg (fun triple => triple.2.2) htuple
                                      cases hrem
                                      cases hmovedRest
                                      cases hvaluesRest
                                      exact hbridge

theorem stackGcNatMapBitmap_length_partition
    (bits : List Bool) (moved values mapped restMoved restValues :
      List StackGcNatValue)
    (hresult : stackGcNatMapBitmap bits moved values =
      some (mapped, restMoved, restValues)) :
    mapped.length = bits.length ∧
      values.length = mapped.length + restValues.length := by
  induction bits generalizing moved values mapped restMoved restValues with
  | nil =>
      have htuple : ([], moved, values) = (mapped, restMoved, restValues) := by
        simpa [stackGcNatMapBitmap] using hresult
      cases htuple
      simp
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
                          have hlength := ih moved values mappedNext restMovedNext
                            restValuesNext hrecursive
                          have hmapped : value :: mappedNext = mapped :=
                            congrArg Prod.fst htuple
                          have hvalues : restValuesNext = restValues :=
                            congrArg (fun triple => triple.2.2) htuple
                          cases hmapped
                          cases hvalues
                          exact ⟨by simp [hlength.1], by
                            simpa [hlength.2, Nat.add_assoc, Nat.add_comm]⟩
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
                                  (movedValue :: mappedNext, restMovedNext,
                                    restValuesNext) =
                                      (mapped, restMoved, restValues) := by
                                simpa [stackGcNatMapBitmap, hrecursive] using hresult
                              have hlength := ih moved values mappedNext restMovedNext
                                restValuesNext hrecursive
                              have hmapped : movedValue :: mappedNext = mapped :=
                                congrArg Prod.fst htuple
                              have hvalues : restValuesNext = restValues :=
                                congrArg (fun triple => triple.2.2) htuple
                              cases hmapped
                              cases hvalues
                              exact ⟨by simp [hlength.1], by
                                simpa [hlength.2, Nat.add_assoc, Nat.add_comm]⟩

theorem stackGcNatMoveBitmap_values_length
    (config : StackGcConfig) (bitmaps : List Nat)
    (descriptor : StackGcNatValue) (stack : List StackGcNatValue)
    (index destination oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool) (result : StackGcBitmapMoveResult)
    (hresult :
      stackGcNatMoveBitmap config bitmaps descriptor stack index destination oldBase
        memory domain = some result) :
    ∃ bits, stackGcNatFullReadBitmap config bitmaps descriptor = some bits ∧
      result.values.length = bits.length := by
  unfold stackGcNatMoveBitmap at hresult
  cases hfull : stackGcNatFullReadBitmap config bitmaps descriptor with
  | none =>
      simp [hfull] at hresult
  | some bits =>
      cases hfilter : stackGcNatFilterBitmap bits stack with
      | none =>
          simp [hfull, hfilter] at hresult
      | some pair =>
          cases pair with
          | mk selected remainder =>
              let moved := stackGcNatMoveValueRoots config selected index destination
                oldBase memory domain
              cases hmap : stackGcNatMapBitmap bits moved.values stack with
              | none =>
                  simp [hfull, hfilter, moved, hmap] at hresult
              | some pair =>
                  cases pair with
                  | mk values restPair =>
                      cases restPair with
                      | mk restMoved restValues =>
                          have hpartition :=
                            stackGcNatMapBitmap_length_partition bits moved.values stack
                              values restMoved restValues hmap
                          simp [hfull, hfilter, moved, hmap] at hresult
                          cases hresult
                          exact ⟨bits, rfl, hpartition.1⟩

theorem stackGcNatMoveBitmap_remainder
    (config : StackGcConfig) (bitmaps : List Nat)
    (descriptor : StackGcNatValue) (stack : List StackGcNatValue)
    (index destination oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool) (result : StackGcBitmapMoveResult)
    (hresult :
      stackGcNatMoveBitmap config bitmaps descriptor stack index destination oldBase
        memory domain = some result) :
    ∃ bits selected remainder,
      stackGcNatFullReadBitmap config bitmaps descriptor = some bits ∧
      stackGcNatFilterBitmap bits stack = some (selected, remainder) ∧
      result.remainder = remainder := by
  unfold stackGcNatMoveBitmap at hresult
  cases hfull : stackGcNatFullReadBitmap config bitmaps descriptor with
  | none =>
      simp [hfull] at hresult
  | some bits =>
      cases hfilter : stackGcNatFilterBitmap bits stack with
      | none =>
          simp [hfull, hfilter] at hresult
      | some pair =>
          cases pair with
          | mk selected remainder =>
              let moved := stackGcNatMoveValueRoots config selected index destination
                oldBase memory domain
              cases hmap : stackGcNatMapBitmap bits moved.values stack with
              | none =>
                  simp [hfull, hfilter, moved, hmap] at hresult
              | some pair =>
                  cases pair with
                  | mk values restPair =>
                      cases restPair with
                      | mk restMoved restValues =>
                          have htuple :
                              { values := values
                                remainder := remainder
                                nextIndex := moved.nextIndex
                                nextAddress := moved.nextAddress
                                memory := moved.memory
                                condition := moved.condition } = result := by
                            simpa [hfull, hfilter, moved, hmap] using hresult
                          cases htuple
                          exact ⟨bits, selected, remainder, rfl, hfilter, rfl⟩

theorem stackGcNatDecodeStackFuel_length
    (config : StackGcConfig) (bitmaps : List Nat) (fuel : Nat)
    (encoded stack result : List StackGcNatValue)
    (hresult : stackGcNatDecodeStackFuel config bitmaps fuel encoded stack =
      some result) :
    result.length = stack.length := by
  induction fuel generalizing encoded stack result with
  | zero =>
      simp [stackGcNatDecodeStackFuel.eq_1] at hresult
  | succ fuel ih =>
      replace hresult :
          stackGcNatDecodeStackFuel config bitmaps (Nat.succ fuel) encoded stack =
            some result := by
        simpa only [Nat.add_one] using hresult
      cases stack with
      | nil =>
          simp [stackGcNatDecodeStackFuel.eq_2] at hresult
      | cons value values =>
          change stackGcNatDecodeStackFuel config bitmaps (Nat.succ fuel)
              encoded (value :: values) = some result at hresult
          cases value with
          | loc left right =>
              simp [stackGcNatDecodeStackFuel.eq_6,
                stackGcNatFullReadBitmap] at hresult
          | word value =>
              by_cases hzero : value = 0
              · subst value
                cases values with
                | nil =>
                    cases encoded with
                    | nil =>
                        rw [stackGcNatDecodeStackFuel.eq_3] at hresult
                        injection hresult with htuple
                        cases htuple
                        rfl
                    | cons encodedValue encodedRest =>
                        have hencoded :
                            (encodedValue :: encodedRest : List StackGcNatValue) ≠ [] := by
                          simp
                        rw [stackGcNatDecodeStackFuel.eq_4 config bitmaps
                          (encodedValue :: encodedRest) fuel hencoded] at hresult
                        simp at hresult
                | cons next rest =>
                    have htail :
                        (next :: rest : List StackGcNatValue) ≠ [] := by
                      simp
                    have hencoded :
                        encoded = [] →
                          (next :: rest : List StackGcNatValue) = [] → False := by
                      simp
                    rw [stackGcNatDecodeStackFuel.eq_5 config bitmaps encoded fuel
                      (next :: rest) htail hencoded] at hresult
                    simp at hresult
              · cases hfull : stackGcNatFullReadBitmap config bitmaps (.word value) with
                | none =>
                    have hsentinel : (.word value : StackGcNatValue) ≠ .word 0 := by
                      simp [hzero]
                    have hvalues :
                        (.word value : StackGcNatValue) = .word 0 →
                          values = [] → False := by
                      simp [hzero]
                    have hencoded :
                        encoded = [] →
                          (.word value : StackGcNatValue) = .word 0 →
                          values = [] → False := by
                      simp [hzero]
                    rw [stackGcNatDecodeStackFuel.eq_6 config bitmaps encoded fuel
                      (.word value) values hvalues hsentinel hencoded] at hresult
                    simp [hfull] at hresult
                | some bits =>
                    cases hmap : stackGcNatMapBitmap bits encoded values with
                    | none =>
                        have hsentinel : (.word value : StackGcNatValue) ≠ .word 0 := by
                          simp [hzero]
                        have hvalues :
                            (.word value : StackGcNatValue) = .word 0 →
                              values = [] → False := by
                          simp [hzero]
                        have hencoded :
                            encoded = [] →
                              (.word value : StackGcNatValue) = .word 0 →
                              values = [] → False := by
                          simp [hzero]
                        rw [stackGcNatDecodeStackFuel.eq_6 config bitmaps encoded fuel
                          (.word value) values hvalues hsentinel hencoded] at hresult
                        simp [hfull, hmap] at hresult
                    | some pair =>
                        cases pair with
                        | mk mapped restPair =>
                            cases restPair with
                            | mk restEncoded restValues =>
                                cases hdecode : stackGcNatDecodeStackFuel config bitmaps fuel
                                    restEncoded restValues with
                                | none =>
                                    have hsentinel : (.word value : StackGcNatValue) ≠ .word 0 := by
                                      simp [hzero]
                                    have hvalues :
                                        (.word value : StackGcNatValue) = .word 0 →
                                          values = [] → False := by
                                      simp [hzero]
                                    have hencoded :
                                        encoded = [] →
                                          (.word value : StackGcNatValue) = .word 0 →
                                          values = [] → False := by
                                      simp [hzero]
                                    rw [stackGcNatDecodeStackFuel.eq_6 config bitmaps encoded fuel
                                      (.word value) values hvalues hsentinel hencoded] at hresult
                                    simp [hfull, hmap, hdecode] at hresult
                                | some rest =>
                                    have hsentinel : (.word value : StackGcNatValue) ≠ .word 0 := by
                                      simp [hzero]
                                    have hvalues :
                                        (.word value : StackGcNatValue) = .word 0 →
                                          values = [] → False := by
                                      simp [hzero]
                                    have hencoded :
                                        encoded = [] →
                                          (.word value : StackGcNatValue) = .word 0 →
                                          values = [] → False := by
                                      simp [hzero]
                                    rw [stackGcNatDecodeStackFuel.eq_6 config bitmaps encoded fuel
                                      (.word value) values hvalues hsentinel hencoded] at hresult
                                    simp [hfull, hmap, hdecode] at hresult
                                    have htuple :
                                        (.word value :: mapped ++ rest) = result := by
                                      exact hresult
                                    have hpartition :=
                                      stackGcNatMapBitmap_length_partition bits encoded values
                                        mapped restEncoded restValues hmap
                                    have hlength := ih restEncoded restValues rest hdecode
                                    cases htuple
                                    simp only [List.length_cons, List.length_append]
                                    omega

theorem stackGcNatDecodeStack_length
    (config : StackGcConfig) (bitmaps : List Nat)
    (encoded stack result : List StackGcNatValue)
    (hresult : stackGcNatDecodeStack config bitmaps encoded stack = some result) :
    result.length = stack.length := by
  exact stackGcNatDecodeStackFuel_length config bitmaps (stack.length + 1)
    encoded stack result hresult

theorem stackGcNatMoveRootsBitmaps_length
    (config : StackGcConfig) (bitmaps : List Nat)
    (stack : List StackGcNatValue)
    (index destination oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool) (result : StackGcValueRootsResult)
    (hresult :
      stackGcNatMoveRootsBitmaps config bitmaps stack index destination oldBase
        memory domain = some result) :
    result.values.length = stack.length := by
  unfold stackGcNatMoveRootsBitmaps at hresult
  cases hencode :
      stackGcNatEncodeStack config bitmaps stack with
  | none =>
      simp [hencode] at hresult
  | some encoded =>
      let moved := stackGcNatMoveValueRoots config encoded index destination
        oldBase memory domain
      cases hdecode :
          stackGcNatDecodeStack config bitmaps moved.values stack with
      | none =>
          simp [hencode, hdecode, moved] at hresult
      | some values =>
          have hlength := stackGcNatDecodeStack_length config bitmaps
            moved.values stack values hdecode
          simp [hencode, hdecode, moved] at hresult
          cases hresult
          exact hlength

theorem stackGcNatFullBitmaps_length
    (config : StackGcConfig) (bitmaps : List Nat)
    (stack : List StackGcNatValue)
    (newBase oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool) (fuel : Nat) (result : StackGcValueRootsResult)
    (hresult :
      stackGcNatFullBitmaps config bitmaps stack newBase oldBase memory domain fuel =
        some result) :
    result.values.length = stack.length := by
  unfold stackGcNatFullBitmaps at hresult
  cases hmove :
      stackGcNatMoveRootsBitmaps config bitmaps stack 0 newBase oldBase
        memory domain with
  | none =>
      simp [hmove] at hresult
  | some moved =>
      have hlength := stackGcNatMoveRootsBitmaps_length config bitmaps stack
        0 newBase oldBase memory domain moved hmove
      simp [hmove] at hresult
      cases hresult
      exact hlength

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
