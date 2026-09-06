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

end Flapjack
