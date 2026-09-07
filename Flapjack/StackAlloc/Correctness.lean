import Flapjack.StackAlloc.Machine

/-
  The HOL source for this specification is
  cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml.  It describes
  the collector over machine words and a partial memory map.  This file ports
  the word-only word_gc_move layer first; the location-valued stack and
  bitmap wrappers remain a subsequent refinement.
-/

namespace Flapjack

structure StackGcNatCopyResult where
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

structure StackGcNatMoveResult where
  value : Nat
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

structure StackGcNatRootsResult where
  values : List Nat
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

structure StackGcNatMoveListResult where
  nextScan : Nat
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

structure StackGcNatMoveLoopResult where
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

structure StackGcNatFullResult where
  values : List Nat
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

inductive StackGcNatValue where
  | loc (left right : Nat)
  | word (value : Nat)
  deriving DecidableEq, Repr

structure StackGcValueMoveResult where
  value : StackGcNatValue
  nextIndex : Nat
  nextAddress : Nat
  memory : Nat → Nat
  condition : Bool

/-! Bitmap filtering and reconstruction are the list-level primitives used by
    the StackLang root collector.  They are partial because a bitmap must
    consume exactly the number of values it describes.  This mirrors the
    filter_bitmap and map_bitmap definitions in the CakeML stack semantics. -/

def stackGcNatFilterBitmap :
    List Bool → List StackGcNatValue →
      Option (List StackGcNatValue × List StackGcNatValue)
  | [], values => some ([], values)
  | false :: bits, _ :: values => stackGcNatFilterBitmap bits values
  | true :: bits, value :: values => do
      let (selected, rest) ← stackGcNatFilterBitmap bits values
      pure (value :: selected, rest)
  | _, _ => none

def stackGcNatMapBitmap :
    List Bool → List StackGcNatValue → List StackGcNatValue →
      Option (List StackGcNatValue × List StackGcNatValue × List StackGcNatValue)
  | [], moved, values => some ([], moved, values)
  | false :: bits, moved, value :: values => do
      let (mapped, restMoved, restValues) ←
        stackGcNatMapBitmap bits moved values
      pure (value :: mapped, restMoved, restValues)
  | true :: bits, movedValue :: moved, _ :: values => do
      let (mapped, restMoved, restValues) ←
        stackGcNatMapBitmap bits moved values
      pure (movedValue :: mapped, restMoved, restValues)
  | _, _, _ => none

theorem stackGcNatFilterBitmap_nil (values : List StackGcNatValue) :
    stackGcNatFilterBitmap [] values = some ([], values) := by
  rfl

@[simp] theorem stackGcNatFilterBitmap_false_cons
    (bits : List Bool) (value : StackGcNatValue)
    (values : List StackGcNatValue) :
    stackGcNatFilterBitmap (false :: bits) (value :: values) =
      stackGcNatFilterBitmap bits values := by
  rfl

@[simp] theorem stackGcNatFilterBitmap_true_cons
    (bits : List Bool) (value : StackGcNatValue)
    (values : List StackGcNatValue) :
    stackGcNatFilterBitmap (true :: bits) (value :: values) = (do
      let (selected, rest) ← stackGcNatFilterBitmap bits values
      pure (value :: selected, rest)) := by
  rfl

@[simp] theorem stackGcNatMapBitmap_false_cons
    (bits : List Bool) (moved : List StackGcNatValue)
    (value : StackGcNatValue) (values : List StackGcNatValue) :
    stackGcNatMapBitmap (false :: bits) moved (value :: values) = (do
      let (mapped, restMoved, restValues) ←
        stackGcNatMapBitmap bits moved values
      pure (value :: mapped, restMoved, restValues)) := by
  rfl

@[simp] theorem stackGcNatMapBitmap_true_cons
    (bits : List Bool) (movedValue : StackGcNatValue)
    (moved : List StackGcNatValue) (value : StackGcNatValue)
    (values : List StackGcNatValue) :
    stackGcNatMapBitmap (true :: bits) (movedValue :: moved)
        (value :: values) = (do
      let (mapped, restMoved, restValues) ←
        stackGcNatMapBitmap bits moved values
      pure (movedValue :: mapped, restMoved, restValues)) := by
  rfl

def stackGcNatPointerAddress (config : StackGcConfig)
    (base value : Nat) : Nat :=
  base + (value / 2 ^ config.shiftLength) * config.bytesInWord

def stackGcNatUpdateAddress (config : StackGcConfig)
    (forwardPointer oldAddress : Nat) : Nat :=
  forwardPointer * 2 ^ config.shiftLength +
    oldAddress % 2 ^ config.smallShiftLength

def stackGcNatIsForwardingPointer (value : Nat) : Bool :=
  value % 4 = 0

def stackGcNatDecodeLength (config : StackGcConfig) (header : Nat) : Nat :=
  header / 2 ^ (config.wordBits - config.lenSize)

def stackGcNatMemcpy (config : StackGcConfig) :
    Nat → Nat → Nat → (Nat → Nat) → (Nat → Bool) → StackGcNatCopyResult
  | 0, _, destination, memory, _ =>
      { nextAddress := destination, memory := memory, condition := true }
  | words + 1, source, destination, memory, domain =>
      let copied := stackGcNatMemcpy config words
        (source + config.bytesInWord) (destination + config.bytesInWord)
        (fun address => if address = destination then memory source
          else memory address) domain
      { nextAddress := copied.nextAddress
        memory := copied.memory
        condition := copied.condition && domain source && domain destination }

def stackGcNatMove (config : StackGcConfig)
    (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) : StackGcNatMoveResult :=
  if value % 2 = 0 then
    { value := value
      nextIndex := index
      nextAddress := destination
      memory := memory
      condition := true }
  else
    let headerAddress := stackGcNatPointerAddress config oldBase value
    let header := memory headerAddress
    if stackGcNatIsForwardingPointer header then
      { value := stackGcNatUpdateAddress config (header / 4) value
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := domain headerAddress }
    else
      let length := stackGcNatDecodeLength config header
      let copied := stackGcNatMemcpy config (length + 1) headerAddress
        destination memory domain
      { value := stackGcNatUpdateAddress config index value
        nextIndex := index + length + 1
        nextAddress := copied.nextAddress
        memory := fun address =>
          if address = headerAddress then index * 4
          else copied.memory address
        condition := domain headerAddress && copied.condition }

def stackGcValueMove (config : StackGcConfig)
    (value : StackGcNatValue) (index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) : StackGcValueMoveResult :=
  match value with
  | .loc left right =>
      { value := .loc left right
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := right == 0 }
  | .word value =>
      let moved := stackGcNatMove config value index destination oldBase
        memory domain
      { value := .word moved.value
        nextIndex := moved.nextIndex
        nextAddress := moved.nextAddress
        memory := moved.memory
        condition := moved.condition }

def stackGcNatMoveRoots (config : StackGcConfig) :
    List Nat → Nat → Nat → Nat → (Nat → Nat) → (Nat → Bool) →
      StackGcNatRootsResult
  | [], index, destination, _, memory, _ =>
      { values := []
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := true }
  | value :: values, index, destination, oldBase, memory, domain =>
      let moved := stackGcNatMove config value index destination oldBase
        memory domain
      let rest := stackGcNatMoveRoots config values moved.nextIndex
        moved.nextAddress oldBase moved.memory domain
      { values := moved.value :: rest.values
        nextIndex := rest.nextIndex
        nextAddress := rest.nextAddress
        memory := rest.memory
        condition := moved.condition && rest.condition }

def stackGcNatMoveList (config : StackGcConfig) :
    Nat → Nat → Nat → Nat → Nat → (Nat → Nat) → (Nat → Bool) →
      StackGcNatMoveListResult
  | 0, address, index, destination, _, memory, _ =>
      { nextScan := address
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := true }
  | length + 1, address, index, destination, oldBase, memory, domain =>
      let moved := stackGcNatMove config (memory address) index destination oldBase
        memory domain
      let memory1 := fun current =>
        if current = address then moved.value else moved.memory current
      let rest := stackGcNatMoveList config length
        (address + config.bytesInWord) moved.nextIndex moved.nextAddress
        oldBase memory1 domain
      { nextScan := rest.nextScan
        nextIndex := rest.nextIndex
        nextAddress := rest.nextAddress
        memory := rest.memory
        condition := domain address && moved.condition && rest.condition }

def stackGcNatHeaderHasCode (header : Nat) : Bool :=
  (header / 4) % 2 = 1

def stackGcNatMoveLoop (config : StackGcConfig) :
    Nat → Nat → Nat → Nat → Nat → (Nat → Nat) → (Nat → Bool) → Bool →
      StackGcNatMoveLoopResult
  | 0, _, index, destination, _, memory, _, _ =>
      { nextIndex := index
        nextAddress := destination
        memory := memory
        condition := false }
  | fuel + 1, scan, index, destination, oldBase, memory, domain, condition =>
      if scan = destination then
        { nextIndex := index
          nextAddress := destination
          memory := memory
          condition := condition }
      else
        let header := memory scan
        let condition := condition && domain scan
        let length := stackGcNatDecodeLength config header
        if stackGcNatHeaderHasCode header then
          stackGcNatMoveLoop config fuel
            (scan + (length + 1) * config.bytesInWord) index destination
            oldBase memory domain condition
        else
          let moved := stackGcNatMoveList config length
            (scan + config.bytesInWord) index destination oldBase memory domain
          let rest := stackGcNatMoveLoop config fuel moved.nextScan
            moved.nextIndex moved.nextAddress oldBase moved.memory domain
            (condition && moved.condition)
          rest

def stackGcNatFull (config : StackGcConfig)
    (values : List Nat) (newBase oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (fuel : Nat) :
    StackGcNatFullResult :=
  let moved := stackGcNatMoveRoots config values 0 newBase oldBase memory domain
  let scanned := stackGcNatMoveLoop config fuel newBase moved.nextIndex
    moved.nextAddress oldBase moved.memory domain moved.condition
  { values := moved.values
    nextIndex := scanned.nextIndex
    nextAddress := scanned.nextAddress
    memory := scanned.memory
    condition := scanned.condition }

theorem stackGcNatMove_immediate
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 = 0) :
    (stackGcNatMove config value index destination oldBase memory domain).value =
      value := by
  simp [stackGcNatMove, hvalue]

theorem stackGcValueMove_loc
    (config : StackGcConfig) (left right index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    stackGcValueMove config (.loc left right) index destination oldBase
      memory domain =
      { value := .loc left right
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := right == 0 } := by
  rfl

theorem stackGcNatMove_forwarding
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hforward : stackGcNatIsForwardingPointer
      (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).value =
      stackGcNatUpdateAddress config
        (memory (stackGcNatPointerAddress config oldBase value) / 4) value := by
  have hforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 = 0 := by
    simpa [stackGcNatIsForwardingPointer] using hforward
  simp [stackGcNatMove, hvalue, hforward', stackGcNatIsForwardingPointer]

theorem stackGcNatMove_copy
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).nextIndex =
      index + stackGcNatDecodeLength config
        (memory (stackGcNatPointerAddress config oldBase value)) + 1 := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  simp [stackGcNatMove, hvalue, hnonforward',
    stackGcNatIsForwardingPointer]

theorem stackGcNatMemcpy_nextAddress
    (config : StackGcConfig) (words source destination : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMemcpy config words source destination memory domain).nextAddress =
      destination + words * config.bytesInWord := by
  induction words generalizing source destination memory with
  | zero => simp [stackGcNatMemcpy]
  | succ words ih =>
      simp [stackGcNatMemcpy, ih, Nat.succ_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]

theorem stackGcNatMemcpy_memory_domain_irrel
    (config : StackGcConfig) (words source destination : Nat)
    (memory : Nat → Nat) (domain domain' : Nat → Bool) :
    (stackGcNatMemcpy config words source destination memory domain).memory =
      (stackGcNatMemcpy config words source destination memory domain').memory := by
  induction words generalizing source destination memory with
  | zero => rfl
  | succ words ih =>
      simp [stackGcNatMemcpy, ih]

theorem stackGcNatMemcpy_condition_of_domain
    (config : StackGcConfig) (words source destination : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hdomain : ∀ address, domain address = true) :
    (stackGcNatMemcpy config words source destination memory domain).condition =
      true := by
  induction words generalizing source destination memory with
  | zero => simp [stackGcNatMemcpy]
  | succ words ih =>
      simp [stackGcNatMemcpy, ih, hdomain]

theorem stackGcNatMemcpy_memory_unchanged
    (config : StackGcConfig) (words source destination : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (address : Nat)
    (haddress :
      ∀ index, index < words →
        address ≠ destination + index * config.bytesInWord) :
    (stackGcNatMemcpy config words source destination memory domain).memory
        address =
      memory address := by
  induction words generalizing source destination memory with
  | zero => rfl
  | succ words ih =>
      have hdestination : address ≠ destination := by
        intro heq
        apply haddress 0 (by omega)
        simpa using heq
      have hrest :
          ∀ index, index < words →
            address ≠ (destination + config.bytesInWord) +
              index * config.bytesInWord := by
        intro index hindex heq
        apply haddress (index + 1) (by omega)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using heq
      have hmemory := ih (source + config.bytesInWord)
        (destination + config.bytesInWord)
        (fun current =>
          if current = destination then memory source else memory current)
        hrest
      simp [stackGcNatMemcpy, hmemory, hdestination]

theorem stackGcNatMove_copy_value
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).value =
      stackGcNatUpdateAddress config index value := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  simp [stackGcNatMove, hvalue, hnonforward',
    stackGcNatIsForwardingPointer]

theorem stackGcNatMove_copy_nextAddress
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).nextAddress =
      destination +
        (stackGcNatDecodeLength config
          (memory (stackGcNatPointerAddress config oldBase value)) + 1) *
          config.bytesInWord := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  let headerAddress := stackGcNatPointerAddress config oldBase value
  let length := stackGcNatDecodeLength config (memory headerAddress)
  have hmemcpy := stackGcNatMemcpy_nextAddress config (length + 1) headerAddress
    destination memory domain
  simp [stackGcNatMove, hvalue, hnonforward',
    stackGcNatIsForwardingPointer, headerAddress, length, hmemcpy]

theorem stackGcNatMove_copy_memory_header
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).memory
        (stackGcNatPointerAddress config oldBase value) =
      index * 4 := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  simp [stackGcNatMove, hvalue, hnonforward',
    stackGcNatIsForwardingPointer]

theorem stackGcNatMove_copy_condition
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value))) :
    (stackGcNatMove config value index destination oldBase memory domain).condition =
      (domain (stackGcNatPointerAddress config oldBase value) &&
        (stackGcNatMemcpy config
          (stackGcNatDecodeLength config
            (memory (stackGcNatPointerAddress config oldBase value)) + 1)
          (stackGcNatPointerAddress config oldBase value) destination memory domain).condition) := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  simp [stackGcNatMove, hvalue, hnonforward',
    stackGcNatIsForwardingPointer]

theorem stackGcNatMove_condition_of_domain
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hdomain : ∀ address, domain address = true) :
    (stackGcNatMove config value index destination oldBase memory domain).condition =
      true := by
  by_cases hvalue : value % 2 = 0
  · simp [stackGcNatMove, hvalue]
  · let headerAddress := stackGcNatPointerAddress config oldBase value
    by_cases hforward : stackGcNatIsForwardingPointer (memory headerAddress)
    · simp [stackGcNatMove, hvalue, hforward, headerAddress, hdomain]
    · have hmem := stackGcNatMemcpy_condition_of_domain config
        (stackGcNatDecodeLength config (memory headerAddress) + 1)
        headerAddress destination memory domain hdomain
      simp [stackGcNatMove, hvalue, hforward, headerAddress, hdomain, hmem]

theorem stackGcNatMoveRoots_length
    (config : StackGcConfig) (values : List Nat) (index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveRoots config values index destination oldBase memory domain).values.length =
      values.length := by
  induction values generalizing index destination memory with
  | nil => rfl
  | cons value values ih =>
      simp [stackGcNatMoveRoots, ih]

theorem stackGcNatMoveRoots_condition_of_domain
    (config : StackGcConfig) (values : List Nat)
    (index destination oldBase : Nat) (memory : Nat → Nat)
    (domain : Nat → Bool)
    (hdomain : ∀ address, domain address = true) :
    (stackGcNatMoveRoots config values index destination oldBase memory domain).condition =
      true := by
  induction values generalizing index destination memory with
  | nil => simp [stackGcNatMoveRoots]
  | cons value values ih =>
      let moved := stackGcNatMove config value index destination oldBase
        memory domain
      have hmove := stackGcNatMove_condition_of_domain config value
        index destination oldBase memory domain hdomain
      have hrest := ih moved.nextIndex moved.nextAddress moved.memory
      simp [stackGcNatMoveRoots, moved, hmove, hrest]

theorem stackGcNatMoveList_zero
    (config : StackGcConfig) (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    stackGcNatMoveList config 0 address index destination oldBase memory domain =
      { nextScan := address
        nextIndex := index
        nextAddress := destination
        memory := memory
        condition := true } := by
  rfl

theorem stackGcNatMoveList_immediate_one
    (config : StackGcConfig) (address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : memory address % 2 = 0) :
    stackGcNatMoveList config 1 address index destination oldBase memory domain =
      { nextScan := address + config.bytesInWord
        nextIndex := index
        nextAddress := destination
        memory := fun current =>
          if current = address then memory address else memory current
        condition := domain address } := by
  simp [stackGcNatMoveList, stackGcNatMove, hvalue]

theorem stackGcNatMoveList_forwarding_one
    (config : StackGcConfig) (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hforward :
      stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hloaded : memory address = value) :
    stackGcNatMoveList config 1 address index destination oldBase memory domain =
      { nextScan := address + config.bytesInWord
        nextIndex := index
        nextAddress := destination
        memory := fun current =>
          if current = address then
            stackGcNatUpdateAddress config
              (memory (stackGcNatPointerAddress config oldBase value) / 4) value
          else memory current
        condition := domain address &&
          domain (stackGcNatPointerAddress config oldBase value) } := by
  have hforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 = 0 := by
    simpa [stackGcNatIsForwardingPointer] using hforward
  simp [stackGcNatMoveList, stackGcNatMove, stackGcNatIsForwardingPointer,
    hvalue, hforward', hloaded]

theorem stackGcNatMoveList_copy_one
    (config : StackGcConfig) (address value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hloaded : memory address = value) :
    let headerAddress := stackGcNatPointerAddress config oldBase value
    let length := stackGcNatDecodeLength config (memory headerAddress)
    let copied := stackGcNatMemcpy config (length + 1) headerAddress
      destination memory domain
    stackGcNatMoveList config 1 address index destination oldBase memory domain =
      { nextScan := address + config.bytesInWord
        nextIndex := index + length + 1
        nextAddress := copied.nextAddress
        memory := fun current =>
          if current = address then
            stackGcNatUpdateAddress config index value
          else if current = headerAddress then index * 4
          else copied.memory current
        condition := domain address &&
          (domain headerAddress && copied.condition) } := by
  let headerAddress := stackGcNatPointerAddress config oldBase value
  let length := stackGcNatDecodeLength config (memory headerAddress)
  let copied := stackGcNatMemcpy config (length + 1) headerAddress
    destination memory domain
  have hnonforward' :
      memory headerAddress % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, headerAddress, h]
  simp [stackGcNatMoveList, stackGcNatMove, stackGcNatIsForwardingPointer,
    hvalue, hnonforward', hloaded, headerAddress, length, copied]

theorem stackGcNatMoveList_append
    (config : StackGcConfig) (length length' address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    stackGcNatMoveList config (length + length') address index destination
        oldBase memory domain =
      let first := stackGcNatMoveList config length address index destination
        oldBase memory domain
      let second := stackGcNatMoveList config length' first.nextScan
        first.nextIndex first.nextAddress oldBase first.memory domain
      { nextScan := second.nextScan
        nextIndex := second.nextIndex
        nextAddress := second.nextAddress
        memory := second.memory
        condition := first.condition && second.condition } := by
  induction length generalizing address index destination memory with
  | zero =>
      simp [stackGcNatMoveList]
  | succ length ih =>
      rw [Nat.succ_add]
      simp [stackGcNatMoveList, ih, Bool.and_assoc]

theorem stackGcNatMoveList_nextScan
    (config : StackGcConfig) (length address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveList config length address index destination oldBase memory domain).nextScan =
      address + length * config.bytesInWord := by
  induction length generalizing address index destination memory with
  | zero =>
      simp [stackGcNatMoveList]
  | succ length ih =>
      simp [stackGcNatMoveList, ih, Nat.succ_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

theorem stackGcNatMoveList_condition_of_domain
    (config : StackGcConfig) (length address index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hdomain : ∀ address, domain address = true) :
    (stackGcNatMoveList config length address index destination oldBase memory domain).condition =
      true := by
  induction length generalizing address index destination memory with
  | zero => simp [stackGcNatMoveList]
  | succ length ih =>
      let moved := stackGcNatMove config (memory address) index destination oldBase
        memory domain
      let memory1 := fun current =>
        if current = address then moved.value else moved.memory current
      have hmove := stackGcNatMove_condition_of_domain config (memory address)
        index destination oldBase memory domain hdomain
      have hrest := ih (address + config.bytesInWord) moved.nextIndex
        moved.nextAddress memory1
      simp [stackGcNatMoveList, moved, memory1, hdomain, hmove, hrest]

theorem stackGcNatMoveLoop_code_step
    (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hscan : scan ≠ destination)
    (hcode : stackGcNatHeaderHasCode (memory scan) = true) :
    stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
        memory domain condition =
      stackGcNatMoveLoop config fuel
        (scan + (stackGcNatDecodeLength config (memory scan) + 1) *
          config.bytesInWord)
        index destination oldBase memory domain (condition && domain scan) := by
  simp [stackGcNatMoveLoop, hscan, hcode]

theorem stackGcNatMoveLoop_data_step
    (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hscan : scan ≠ destination)
    (hcode : stackGcNatHeaderHasCode (memory scan) ≠ true) :
    let moved := stackGcNatMoveList config
      (stackGcNatDecodeLength config (memory scan))
      (scan + config.bytesInWord) index destination oldBase memory domain
    stackGcNatMoveLoop config (fuel + 1) scan index destination oldBase
        memory domain condition =
      stackGcNatMoveLoop config fuel moved.nextScan moved.nextIndex
        moved.nextAddress oldBase moved.memory domain
        (condition && domain scan && moved.condition) := by
  simp [stackGcNatMoveLoop, hscan, hcode, Bool.and_assoc]

theorem stackGcNatMoveLoop_iterate_of_step
    (config : StackGcConfig) (fuel iterations oldBase : Nat)
    (domain : Nat → Bool)
    (scans indices destinations : Nat → Nat)
    (memories : Nat → Nat → Nat)
    (conditions : Nat → Bool)
    (hstep : ∀ current remaining, current < iterations →
      stackGcNatMoveLoop config (remaining + 1)
        (scans current) (indices current) (destinations current) oldBase
        (memories current) domain (conditions current) =
      stackGcNatMoveLoop config remaining
        (scans (current + 1)) (indices (current + 1))
        (destinations (current + 1)) oldBase
        (memories (current + 1)) domain (conditions (current + 1))) :
    stackGcNatMoveLoop config (fuel + iterations)
        (scans 0) (indices 0) (destinations 0) oldBase
        (memories 0) domain (conditions 0) =
      stackGcNatMoveLoop config fuel
        (scans iterations) (indices iterations) (destinations iterations)
        oldBase (memories iterations) domain (conditions iterations) := by
  induction iterations generalizing scans indices destinations memories conditions with
  | zero => rfl
  | succ iterations ih =>
      have hfirst := hstep 0 (fuel + iterations) (by omega)
      have hrest := ih
        (scans := fun current => scans (current + 1))
        (indices := fun current => indices (current + 1))
        (destinations := fun current => destinations (current + 1))
        (memories := fun current => memories (current + 1))
        (conditions := fun current => conditions (current + 1))
        (hstep := fun current remaining hcurrent =>
          hstep (current + 1) remaining (by omega))
      simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hfirst.trans hrest

theorem stackGcNatMoveLoop_zero
    (config : StackGcConfig) (scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveLoop config 0 scan index destination oldBase memory domain true).condition =
      false := by
  rfl

theorem stackGcNatMoveLoop_false
    (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveLoop config fuel scan index destination oldBase memory domain false).condition =
      false := by
  induction fuel generalizing scan index destination memory with
  | zero => rfl
  | succ fuel ih =>
      by_cases hscan : scan = destination
      · simp [stackGcNatMoveLoop, hscan]
      · by_cases hcode : stackGcNatHeaderHasCode (memory scan) = true
        · simpa [stackGcNatMoveLoop, hscan, hcode] using
            (ih (scan + (stackGcNatDecodeLength config (memory scan) + 1) * config.bytesInWord)
              index destination memory)
        · let moved := stackGcNatMoveList config
            (stackGcNatDecodeLength config (memory scan))
            (scan + config.bytesInWord) index destination oldBase memory domain
          simpa [stackGcNatMoveLoop, hscan, hcode, moved] using
            (ih moved.nextScan moved.nextIndex moved.nextAddress moved.memory)

theorem stackGcNatMoveLoop_ok
    (config : StackGcConfig) (fuel scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (condition : Bool)
    (hresult :
      (stackGcNatMoveLoop config fuel scan index destination oldBase memory domain condition).condition =
        true) :
    condition = true := by
  cases condition with
  | false =>
      have hfalse := stackGcNatMoveLoop_false config fuel scan index destination oldBase
        memory domain
      simp [hfalse] at hresult
  | true => rfl

/-! The post-`Memcpy` part of a non-forwarded move.  Keeping this as a
    separate Nat result mirrors `stackGcMoveCopySuffixAfterMemcpy` and makes
    the arbitrary-object copy proof compositional. -/

def stackGcNatMoveCopySuffix (config : StackGcConfig)
    (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) : StackGcNatMoveResult :=
  let copied := stackGcNatMemcpy config words source destination memory domain
  { value := stackGcNatUpdateAddress config index value
    nextIndex := index + words
    nextAddress := copied.nextAddress
    memory := fun current =>
      if current = source then index * 4 else copied.memory current
    condition := copied.condition }

@[simp] theorem stackGcNatMoveCopySuffix_value
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).value = stackGcNatUpdateAddress config index value := by
  rfl

@[simp] theorem stackGcNatMoveCopySuffix_nextIndex
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).nextIndex = index + words := by
  rfl

theorem stackGcNatMoveCopySuffix_nextAddress
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).nextAddress = destination + words * config.bytesInWord := by
  simp [stackGcNatMoveCopySuffix, stackGcNatMemcpy_nextAddress]

theorem stackGcNatMoveCopySuffix_condition
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).condition =
      (stackGcNatMemcpy config words source destination memory domain).condition := by
  rfl

theorem stackGcNatMoveCopySuffix_memory_source
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).memory source = index * 4 := by
  simp [stackGcNatMoveCopySuffix]

theorem stackGcNatMoveCopySuffix_memory_of_ne
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) (target : Nat)
    (htarget : target ≠ source) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).memory target =
      (stackGcNatMemcpy config words source destination memory domain).memory target := by
  simp [stackGcNatMoveCopySuffix, htarget]

theorem stackGcNatMoveCopySuffix_eq_move_copy
    (config : StackGcConfig) (value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hheaderDomain :
      domain (stackGcNatPointerAddress config oldBase value) = true) :
    stackGcNatMoveCopySuffix config
        (stackGcNatDecodeLength config
          (memory (stackGcNatPointerAddress config oldBase value)) + 1)
        (stackGcNatPointerAddress config oldBase value)
        destination index value memory domain =
      stackGcNatMove config value index destination oldBase memory domain := by
  have hnonforward' :
      memory (stackGcNatPointerAddress config oldBase value) % 4 ≠ 0 := by
    intro h
    apply hnonforward
    simp [stackGcNatIsForwardingPointer, h]
  simp [stackGcNatMoveCopySuffix, stackGcNatMove,
    stackGcNatIsForwardingPointer, hvalue, hnonforward',
    hheaderDomain, Nat.add_assoc]

theorem stackGcNatMoveCopySuffix_condition_of_domain
    (config : StackGcConfig) (words source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hdomain : ∀ address, domain address = true) :
    (stackGcNatMoveCopySuffix config words source destination index value
      memory domain).condition = true := by
  simp [stackGcNatMoveCopySuffix,
    stackGcNatMemcpy_condition_of_domain config words source destination
      memory domain hdomain]

def stackGcNatMoveListCopyBody (config : StackGcConfig)
    (words scan source destination index value : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) : StackGcNatMoveListResult :=
  let moved := stackGcNatMoveCopySuffix config words source destination index
    value memory domain
  { nextScan := scan + config.bytesInWord
    nextIndex := moved.nextIndex
    nextAddress := moved.nextAddress
    memory := fun current =>
      if current = scan then moved.value else moved.memory current
    condition := domain scan && moved.condition }

theorem stackGcNatMoveListCopyBody_eq_moveList_copy
    (config : StackGcConfig) (scan value index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool)
    (hloaded : memory scan = value)
    (hvalue : value % 2 ≠ 0)
    (hnonforward :
      ¬ stackGcNatIsForwardingPointer
        (memory (stackGcNatPointerAddress config oldBase value)))
    (hheaderDomain :
      domain (stackGcNatPointerAddress config oldBase value) = true) :
    stackGcNatMoveListCopyBody config
        (stackGcNatDecodeLength config
          (memory (stackGcNatPointerAddress config oldBase value)) + 1)
        scan (stackGcNatPointerAddress config oldBase value)
        destination index value memory domain =
      stackGcNatMoveList config 1 scan index destination oldBase memory domain := by
  have hsuffix := stackGcNatMoveCopySuffix_eq_move_copy config value index
    destination oldBase memory domain hvalue hnonforward hheaderDomain
  simp [stackGcNatMoveListCopyBody, stackGcNatMoveList, hloaded, hsuffix]

end Flapjack
