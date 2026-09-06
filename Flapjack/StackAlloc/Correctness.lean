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

theorem stackGcNatMoveRoots_length
    (config : StackGcConfig) (values : List Nat) (index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveRoots config values index destination oldBase memory domain).values.length =
      values.length := by
  induction values generalizing index destination memory with
  | nil => rfl
  | cons value values ih =>
      simp [stackGcNatMoveRoots, ih]

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

theorem stackGcNatMoveLoop_zero
    (config : StackGcConfig) (scan index destination oldBase : Nat)
    (memory : Nat → Nat) (domain : Nat → Bool) :
    (stackGcNatMoveLoop config 0 scan index destination oldBase memory domain true).condition =
      false := by
  rfl

end Flapjack
