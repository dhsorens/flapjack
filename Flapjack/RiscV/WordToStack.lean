import Flapjack.Stack
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.RegAlloc

/-!
# Word-to-Stack spill moves

This is the first executable consumer of the spill locations produced by the
Word allocator.  It ports the essential `wMoveSingle` cases from CakeML's
`word_to_stackScript.sml`: a virtual variable is either represented by a
physical register or by a slot in the current stack frame, and `x31` is used
as the temporary for moves involving stack locations.

The full CakeML pass also lowers every Word instruction and maintains GC
bitmaps.  Those later pieces will build on this total location lookup and its
explicit move cases.
-/

namespace Flapjack.RiscV

structure WordStackConfig where
  locations : NatInfoMap WordLocation
  scratch : Nat
  stackBase : Nat
  addressScratch : Nat := 29
  specialScratch : Nat := 28
  carryScratch : Nat := 27
  perf : Bool := false
  frameOffset : Nat := 0
  returnLabel : Nat := 0
  entryLabel : Nat := 0
  handlerLabel : Nat := 0
  deriving Repr

def wordStackLocation (config : WordStackConfig) (name : Nat) :
    Option WordLocation :=
  lookupNatInfo name config.locations

def wordStackOffset (config : WordStackConfig) (slot : Nat) : Nat :=
  config.stackBase + slot

def wordStackMove (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let source ← wordStackLocation config source
  match destination, source with
  | .register destination, .register source =>
      pure (.arith .or destination source source)
  | .register destination, .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))
  | .stack slot, .register source =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))
  | .stack destinationSlot, .stack sourceSlot =>
      pure (.seq (.stackLoad config.scratch
          (wordStackOffset config sourceSlot))
        (.stackStore config.scratch (wordStackOffset config destinationSlot)))

def wordToStackMove (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) :=
  wordStackMove config destination source

def wordStackLoadInst (config : WordStackConfig) (operator : WordMemOp)
    (destination address : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let address ← wordStackLocation config address
  match destination, address with
  | .register destination, .register address =>
      pure (.inst (.mem operator destination address))
  | .stack destination, .register address =>
      pure (.seq (.inst (.mem operator config.scratch address))
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .register destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.inst (.mem operator destination config.addressScratch)))
  | .stack destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.inst (.mem operator config.scratch config.addressScratch))
          (.stackStore config.scratch (wordStackOffset config destination))))

def wordStackStoreInst (config : WordStackConfig) (operator : WordMemOp)
    (source address : Nat) : Option (StackProg α) := do
  let source ← wordStackLocation config source
  let address ← wordStackLocation config address
  match source, address with
  | .register source, .register address =>
      pure (.inst (.mem operator source address))
  | .stack source, .register address =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config source))
        (.inst (.mem operator config.scratch address)))
  | .register source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.inst (.mem operator source config.addressScratch)))
  | .stack source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.stackLoad config.scratch (wordStackOffset config source))
          (.inst (.mem operator config.scratch config.addressScratch))))

def wordStackJoin (first second : StackProg α) : StackProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def wordMoveDestinations (moves : List (Nat × Nat)) : List Nat :=
  moves.map (fun move => move.1)

def wordMoveRemoveDestination (destination : Nat) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.filter (fun move => move.1 != destination)

def wordMoveReady (destinations : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | move :: moves =>
      if move.2 ∉ destinations then
        some move
      else
        wordMoveReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordStackMoveToScratch (config : WordStackConfig) (source : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or config.addressScratch register register)
  | .stack slot =>
      pure (.stackLoad config.addressScratch (wordStackOffset config slot))

def wordStackMoveFromScratch (config : WordStackConfig) (destination : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or register config.addressScratch config.addressScratch)
  | .stack slot =>
      pure (.stackStore config.addressScratch (wordStackOffset config slot))

/-! Compile a parallel move list.  A move whose source is not another pending
    destination can be emitted immediately.  If the remaining graph is a
    cycle, save one source in the reserved scratch register, solve the rest,
    and restore that saved value into the postponed destination.  CakeML's
    `parmove` uses the same temporary-register idea; the explicit `Nodup`
    check is its windmill invariant at this boundary.  Stack-to-stack moves
    use `scratch`, so cycle save/restore uses the independent address scratch.
    The allocator reserves both registers for this purpose. -/
def wordStackParallelMoveAux (config : WordStackConfig) :
    Nat → List (Nat × Nat) → Option (StackProg α)
  | 0, _ => none
  | fuel + 1, moves =>
      let destinations := wordMoveDestinations moves
      if !destinations.Nodup then
        none
      else if moves.isEmpty then
        some .skip
      else
        match wordMoveReady destinations moves with
        | some (destination, source) => do
            let first ← wordStackMove config destination source
            let rest ← wordStackParallelMoveAux config fuel
              (wordMoveRemoveDestination destination moves)
            pure (wordStackJoin first rest)
        | none =>
            match moves with
            | [] => some .skip
            | (destination, source) :: _ => do
                let save ← wordStackMoveToScratch config source
                let rest ← wordStackParallelMoveAux config fuel
                  (wordMoveRemoveDestination destination moves)
                let restore ← wordStackMoveFromScratch config destination
                pure (wordStackJoin save (wordStackJoin rest restore))

def wordStackParallelMove (config : WordStackConfig)
    (moves : List (Nat × Nat)) : Option (StackProg α) :=
  wordStackParallelMoveAux config (moves.length + 1) moves

def wordStackMoveList (config : WordStackConfig) :
    List (Nat × Nat) → Option (StackProg α) :=
  wordStackParallelMove config

def wordStackDivInst (config : WordStackConfig)
    (destination dividend divisor : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let dividend ← wordStackLocation config dividend
  let divisor ← wordStackLocation config divisor
  match destination, dividend, divisor with
  | .register destination, .register dividend, .register divisor =>
      pure (.inst (.arith (.div destination dividend divisor)))
  | .register destination, .stack dividend, .register divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (.inst (.arith (.div destination config.scratch divisor))))
  | .register destination, .register dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.addressScratch (wordStackOffset config divisor))
        (.inst (.arith (.div destination dividend config.addressScratch))))
  | .register destination, .stack dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config divisor))
          (.inst (.arith (.div destination config.scratch config.addressScratch)))))
  | .stack destination, .register dividend, .register divisor =>
      pure (wordStackJoin
        (.inst (.arith (.div config.scratch dividend divisor)))
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .stack destination, .stack dividend, .register divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.inst (.arith (.div config.scratch config.scratch divisor)))
          (.stackStore config.scratch (wordStackOffset config destination))))
  | .stack destination, .register dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.addressScratch (wordStackOffset config divisor))
        (wordStackJoin
          (.inst (.arith (.div config.scratch dividend config.addressScratch)))
          (.stackStore config.scratch (wordStackOffset config destination))))
  | .stack destination, .stack dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config divisor))
          (wordStackJoin
            (.inst (.arith (.div config.scratch config.scratch config.addressScratch)))
            (.stackStore config.scratch (wordStackOffset config destination)))))

def wordStackLongMulLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch &&
        register != config.specialScratch && register != config.carryScratch
  | .stack _ => true

def wordStackAddCarryLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch &&
        register != config.specialScratch && register != config.carryScratch
  | .stack _ => true

def wordStackLongMulLocationsSafe (config : WordStackConfig)
    (operation : WordArith) : Bool :=
  match operation with
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      match wordStackLocation config destinationLeft,
        wordStackLocation config destinationRight,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight with
      | some destinationLeft, some destinationRight,
          some sourceLeft, some sourceRight =>
          wordStackLongMulLocationSafe config destinationLeft &&
            wordStackLongMulLocationSafe config destinationRight &&
            wordStackLongMulLocationSafe config sourceLeft &&
            wordStackLongMulLocationSafe config sourceRight
      | _, _, _, _ => false
  | _ => false

def wordStackLongMulMoveToPhysical (config : WordStackConfig)
    (source destination : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))

def wordStackLongMulMoveFromPhysical (config : WordStackConfig)
    (destination source : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = source then pure .skip
      else pure (.arith .or register source source)
  | .stack slot =>
      pure (.stackStore source (wordStackOffset config slot))

def wordStackLongMulInst (config : WordStackConfig)
    (operation : WordArith) : Option (StackProg α) :=
  if wordStackLongMulLocationsSafe config operation then
    match operation with
    | .longMul destinationLeft destinationRight sourceLeft sourceRight => do
        match wordStackLocation config destinationLeft,
          wordStackLocation config destinationRight,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight with
        | some (.register destinationLeft), some (.register destinationRight),
            some (.register sourceLeft), some (.register sourceRight) =>
            pure (.inst (.arith (.longMul destinationLeft destinationRight
              sourceLeft sourceRight)))
        | _, _, _, _ =>
            let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft config.scratch
            let loadRight ← wordStackLongMulMoveToPhysical config sourceRight config.addressScratch
            let writeLeft ← wordStackLongMulMoveFromPhysical config destinationLeft
              config.specialScratch
            let writeRight ← wordStackLongMulMoveFromPhysical config destinationRight config.scratch
            pure (wordStackJoin loadLeft
              (wordStackJoin loadRight
                (wordStackJoin
                  (.inst (.arith (.longMul config.specialScratch config.scratch
                    config.scratch config.addressScratch)))
                  (wordStackJoin writeLeft writeRight))))
    | _ => none
  else
    none

def wordStackAddCarryInst (config : WordStackConfig)
    (operation : WordArith) : Option (StackProg α) :=
  match operation with
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      let safe name := match wordStackLocation config name with
        | some location => wordStackAddCarryLocationSafe config location
        | none => false
      if safe destination && safe resultCarry && safe sourceLeft &&
          safe sourceRight && safe carryIn then
        match wordStackLocation config destination,
          wordStackLocation config resultCarry,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight,
          wordStackLocation config carryIn with
        | some (.register destination), some (.register resultCarry),
            some (.register sourceLeft), some (.register sourceRight),
            some (.register carryIn) =>
            some (.inst (.arith (.addCarry destination resultCarry sourceLeft
              sourceRight carryIn)))
        | _, _, _, _, _ => do
            let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
              config.addressScratch
            let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
              config.specialScratch
            let loadCarry ← wordStackLongMulMoveToPhysical config carryIn
              config.carryScratch
            let writeDestination ← wordStackLongMulMoveFromPhysical config destination
              config.carryScratch
            let writeResultCarry ← wordStackLongMulMoveFromPhysical config resultCarry
              config.specialScratch
            pure (wordStackJoin loadLeft
              (wordStackJoin loadRight
                (wordStackJoin loadCarry
                  (wordStackJoin
                    (.inst (.arith (.addCarry config.carryScratch
                      config.specialScratch config.addressScratch
                      config.specialScratch config.carryScratch)))
                    (wordStackJoin writeDestination writeResultCarry)))))
      else
        none
  | _ => none

/-! CakeML's `LongDiv` uses a fixed four-register convention: the two-word
    dividend is in x3:x0, the quotient is written to x0, and the remainder to
    x3.  Only the divisor operand remains allocator-dependent.  Keep this
    normalized shape explicit so an unnormalized operation cannot silently
    acquire the special calling convention. -/
def wordStackLongDivInst (config : WordStackConfig)
    (operation : WordArith) : Option (StackProg α) :=
  match operation with
  | .longDiv 0 3 3 0 divisor => do
      let location ← wordStackLocation config divisor
      match location with
      | .register divisorRegister =>
          if divisorRegister = 0 || divisorRegister = 3 then
            none
          else
            pure (.inst (.arith (.longDiv 0 3 3 0 divisorRegister)))
      | .stack slot =>
          pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
            (.inst (.arith (.longDiv 0 3 3 0 config.scratch))))
  | _ => none

def wordStackArithInst (config : WordStackConfig) (operation : WordArith) :
    Option (StackProg α) :=
  if wordSpecialArithLocationsSafe operation config.locations = true then
    match operation with
    | .longMul _ _ _ _ =>
      wordStackLongMulInst config operation
    | .addCarry _ _ _ _ _ =>
      wordStackAddCarryInst config operation
    | .div destination dividend divisor =>
      wordStackDivInst config destination dividend divisor
    | .longDiv _ _ _ _ _ => wordStackLongDivInst config operation
  else
    none

def wordStackMemoryInst (config : WordStackConfig) (operator : WordMemOp)
    (sourceOrDestination address : Nat) : Option (StackProg α) :=
  match operator with
  | .load => wordStackLoadInst config operator sourceOrDestination address
  | .load8 => wordStackLoadInst config operator sourceOrDestination address
  | .load16 => wordStackLoadInst config operator sourceOrDestination address
  | .load32 => wordStackLoadInst config operator sourceOrDestination address
  | .store => wordStackStoreInst config operator sourceOrDestination address
  | .store8 => wordStackStoreInst config operator sourceOrDestination address
  | .store16 => wordStackStoreInst config operator sourceOrDestination address
  | .store32 => wordStackStoreInst config operator sourceOrDestination address

def wordStackStoreLocationsSafe (config : WordStackConfig) :
    WordLocation → WordLocation → Bool
  | .register _, .register _ => true
  | .stack _, .register address => address != config.scratch
  | .register source, .stack _ => source != config.addressScratch
  | .stack _, .stack _ => config.scratch != config.addressScratch

def wordStackDivLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch
  | .stack _ => true

def wordStackSharedLoadInst (config : WordStackConfig) (operator : WordMemOp)
    (destination address : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let address ← wordStackLocation config address
  match destination, address with
  | .register destination, .register address =>
      pure (.shMem operator destination address)
  | .stack destination, .register address =>
      pure (.seq (.shMem operator config.scratch address)
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .register destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.shMem operator destination config.addressScratch))
  | .stack destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.shMem operator config.scratch config.addressScratch)
          (.stackStore config.scratch (wordStackOffset config destination))))

def wordStackSharedStoreInst (config : WordStackConfig) (operator : WordMemOp)
    (source address : Nat) : Option (StackProg α) := do
  let source ← wordStackLocation config source
  let address ← wordStackLocation config address
  match source, address with
  | .register source, .register address =>
      pure (.shMem operator source address)
  | .stack source, .register address =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config source))
        (.shMem operator config.scratch address))
  | .register source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.shMem operator source config.addressScratch))
  | .stack source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.stackLoad config.scratch (wordStackOffset config source))
          (.shMem operator config.scratch config.addressScratch)))

def wordStackSharedMemoryInst (config : WordStackConfig) (operator : WordMemOp)
    (sourceOrDestination address : Nat) : Option (StackProg α) :=
  match operator with
  | .load => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load8 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load16 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load32 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .store => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store8 => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store16 => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store32 => wordStackSharedStoreInst config operator sourceOrDestination address

/-! The stack program has explicit control-flow and call carriers.  These
    helpers materialize spilled condition operands and implement the Word
    calling convention's even-numbered result registers.  The labels are
    supplied by the enclosing linker through `WordStackConfig`; keeping them
    in the configuration makes this boundary executable without baking in a
    particular code layout. -/

def wordStackReadRegister (config : WordStackConfig) (name temporary : Nat) :
    Option (StackProg α × Nat) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => pure (.skip, register)
  | .stack slot =>
      pure (.stackLoad temporary (wordStackOffset config slot), temporary)

def wordStackConditionOperands (config : WordStackConfig) (condition : Nat)
    (right : WordRegImm α) :
    Option (StackProg α × Nat × WordRegImm α) := do
  let (conditionPrelude, conditionRegister) ←
    wordStackReadRegister config condition config.scratch
  let (rightPrelude, rightOperand) ← match right with
    | .imm value => pure (.skip, .imm value)
    | .reg name => do
        let (prelude, register) ←
          wordStackReadRegister config name config.addressScratch
        pure (prelude, .reg register)
  pure (wordStackJoin conditionPrelude rightPrelude,
    conditionRegister, rightOperand)

/-! FFI arguments use the fixed RISC-V ABI registers x10--x13.  The source
    locations are checked before emitting the copies so a later argument cannot
    be destroyed by an earlier ABI move.  Allocator configurations that keep
    an argument in one of those destination registers are rejected here; a
    future parallel-move implementation can relax this contract. -/

def wordStackFfiRegisterSafe (register : Nat) : Bool :=
  register != 10 && register != 11 && register != 12 && register != 13

def wordStackFfiSourceSafe (config : WordStackConfig) (name : Nat) : Bool :=
  match wordStackLocation config name with
  | some (.register register) => wordStackFfiRegisterSafe register
  | some (.stack _) => true
  | none => false

def wordStackFfiSourcesSafe (config : WordStackConfig) : List Nat → Bool
  | [] => true
  | name :: names =>
      wordStackFfiSourceSafe config name && wordStackFfiSourcesSafe config names

def wordStackFfiMove (config : WordStackConfig) (source destination : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))

def wordStackFfi (config : WordStackConfig) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    Option (StackProg α) := do
  let sources := [configuration, configurationLength, array, arrayLength]
  if wordStackFfiSourcesSafe config sources then
    let configurationMove ← wordStackFfiMove config configuration 10
    let configurationLengthMove ← wordStackFfiMove config configurationLength 11
    let arrayMove ← wordStackFfiMove config array 12
    let arrayLengthMove ← wordStackFfiMove config arrayLength 13
    pure (wordStackJoin configurationMove
      (wordStackJoin configurationLengthMove
        (wordStackJoin arrayMove
          (wordStackJoin arrayLengthMove
            (.ffi function 10 11 12 13 0)))))
  else none

def wordStackStoreName : WordStore α → Option StackStore
  | .temp _ => none
  | .nextFree => some .nextFree
  | .endOfHeap => some .endOfHeap
  | .triggerGC => some .triggerGC
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength
  | .progStart => some .progStart
  | .bitmapBase => some .bitmapBase
  | .otherHeap => some .otherHeap
  | .allocSize => some .allocSize
  | .globals => some .globals
  | .globReal => some .globReal
  | .handler => some .handler
  | .genStart => some .genStart
  | .codeBuffer => some .codeBuffer
  | .codeBufferEnd => some .codeBufferEnd
  | .bitmapBuffer => some .bitmapBuffer
  | .bitmapBufferEnd => some .bitmapBufferEnd

/-! Concrete StackLang words use natural-number constants in this port.  The
    polymorphic Word syntax above is retained for pass composition, while
    these helpers provide the first executable expression compiler for the
    concrete representation.  Atom compilation deliberately uses separate
    value and address scratch registers; callers must keep those registers
    outside the locations assigned to simultaneously live virtual names. -/

def wordStackStoreNameNat : WordStore Nat → Option StackStore
  | .temp address => some (.temp address)
  | .nextFree => some .nextFree
  | .endOfHeap => some .endOfHeap
  | .triggerGC => some .triggerGC
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength
  | .progStart => some .progStart
  | .bitmapBase => some .bitmapBase
  | .otherHeap => some .otherHeap
  | .allocSize => some .allocSize
  | .globals => some .globals
  | .globReal => some .globReal
  | .handler => some .handler
  | .genStart => some .genStart
  | .codeBuffer => some .codeBuffer
  | .codeBufferEnd => some .codeBufferEnd
  | .bitmapBuffer => some .bitmapBuffer
  | .bitmapBufferEnd => some .bitmapBufferEnd

/-! Bitmap accumulation used by CakeML's `word_to_stack` pass.

    CakeML stores bitmaps as a flat append-only word list.  The first word of
    each bitmap chunk records which following constant words are pointers;
    liveness bitmaps have one additional terminating pointer bit.  Keeping
    the accumulator explicit makes the state change caused by `Alloc` and
    `StoreConsts` observable, rather than silently rejecting those Word
    constructors as the stateless compiler above must do. -/

structure WordStackBitmapState where
  data : List Nat
  length : Nat
  deriving Repr

def wordStackInitialBitmaps (perf : Bool) : WordStackBitmapState :=
  if perf then
    { data := [16], length := 1 }
  else
    { data := [4], length := 1 }

def wordStackBitsToNat : List Bool → Nat
  | [] => 1
  | bit :: bits =>
      wordStackBitsToNat bits * 2 + if bit then 1 else 0

def wordStackBitmapChunk (constants : List (Bool × Nat)) : List Nat :=
  wordStackBitsToNat (constants.map Prod.fst) :: constants.map Prod.snd

def wordStackBitmapWordsAux (chunkSize : Nat) :
    Nat → List Bool → List Nat
  | 0, _ => []
  | fuel + 1, bits =>
      if chunkSize = 0 || bits.length ≤ chunkSize then
        [wordStackBitsToNat bits]
      else
        wordStackBitsToNat (bits.take chunkSize ++ [true]) ::
          wordStackBitmapWordsAux chunkSize fuel (bits.drop chunkSize)

def wordStackBitmapWords (chunkSize : Nat) (bits : List Bool) : List Nat :=
  wordStackBitmapWordsAux chunkSize (bits.length + 1) bits

def wordStackConstBitmapWordsAux (wordBits : Nat) :
    Nat → List (Bool × Nat) → List Nat
  | 0, _ => []
  | fuel + 1, constants =>
      let chunkSize := wordBits - 1
      if chunkSize = 0 || constants.length < chunkSize then
        wordStackBitmapChunk constants
      else
        wordStackBitmapChunk (constants.take chunkSize) ++
          wordStackConstBitmapWordsAux wordBits fuel (constants.drop chunkSize)

def wordStackConstBitmapWords (wordBits : Nat)
    (constants : List (Bool × Nat)) : List Nat :=
  wordStackConstBitmapWordsAux wordBits (constants.length + 1) constants

def wordStackLiveBitmap (registerCount frameSlots wordBits : Nat)
    (live : List Nat) : List Nat :=
  let names := live.map (fun register =>
    frameSlots - 1 - (register / 2 - registerCount))
  let bits := (List.range frameSlots).map (fun slot => names.contains slot)
  wordStackBitmapWords (wordBits - 1) (bits ++ [true])

/- In the allocated Lean pipeline the location map is retained separately
   from the Word syntax.  Use its concrete spill slots when constructing a
   frame bitmap; register-resident live values do not occupy stack roots. -/
def wordStackLiveBitmapFromLocations (config : WordStackConfig)
    (frameSlots wordBits : Nat) (live : List Nat) : List Nat :=
  let slots := live.filterMap (fun name =>
    match wordStackLocation config name with
    | some (.stack slot) => some slot
    | some (.register _) | none => none)
  let bits := (List.range frameSlots).map (fun slot => slots.contains slot)
  wordStackBitmapWords (wordBits - 1) (bits ++ [true])

def wordStackInsertBitmap (state : WordStackBitmapState)
    (bitmap : List Nat) : WordStackBitmapState × Nat :=
  ({ data := state.data ++ bitmap,
      length := state.length + bitmap.length }, state.length)

def wordStackBitmapWriteWithBuilder (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (bitmapBuilder : List Nat → List Nat) :
    StackProg Nat × WordStackBitmapState :=
  if frameSlots = 0 then
    (.skip, state)
  else
    let bitmap := bitmapBuilder live
    let (newState, index) := wordStackInsertBitmap state bitmap
    (.seq (.const bitmapRegister (index + 1))
        (.stackStore bitmapRegister (wordStackOffset config 0)), newState)

def wordStackAllocWithBitmapBuilder (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (bitmapBuilder : List Nat → List Nat) :
    StackProg Nat × WordStackBitmapState :=
  let (write, state) := wordStackBitmapWriteWithBuilder config bitmapRegister
    frameSlots state live bitmapBuilder
  (wordStackJoin write (.alloc 1), state)

def wordStackBitmapWrite (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (registerCount wordBits : Nat) :
    StackProg Nat × WordStackBitmapState :=
  wordStackBitmapWriteWithBuilder config bitmapRegister frameSlots state live
    (wordStackLiveBitmap registerCount frameSlots wordBits)

def wordStackAllocWithBitmaps (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (registerCount wordBits : Nat) :
    StackProg Nat × WordStackBitmapState :=
  wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state live
    (wordStackLiveBitmap registerCount frameSlots wordBits)

def wordStackStoreConstsWithBitmaps (config : WordStackConfig)
    (registerCount specialScratch wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (constants : List (Bool × Nat)) :
    StackProg Nat × WordStackBitmapState :=
  let bitmap := wordStackConstBitmapWords wordBits constants
  let (newState, index) := wordStackInsertBitmap state bitmap
  (.seq (.const specialScratch index)
      (.storeConsts registerCount (registerCount + 1) storeConstsStub), newState)

def wordStackGet (config : WordStackConfig) (destination : Nat)
    (store : WordStore α) : Option (StackProg α) := do
  let store ← wordStackStoreName store
  let location ← wordStackLocation config destination
  match location with
  | .register register => pure (.get register store)
  | .stack slot =>
      pure (wordStackJoin (.get config.scratch store)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackOpCurrHeap (config : WordStackConfig) (operator : BinOp)
    (destination source : Nat) : Option (StackProg α) := do
  let (prelude, sourceRegister) ←
    wordStackReadRegister config source config.addressScratch
  let destination ← wordStackLocation config destination
  match destination with
  | .register destination =>
      pure (wordStackJoin prelude
        (.opCurrHeap operator destination sourceRegister))
  | .stack slot =>
      pure (wordStackJoin prelude
        (wordStackJoin
          (.opCurrHeap operator config.scratch sourceRegister)
          (.stackStore config.scratch (wordStackOffset config slot))))

def wordStackInstall (config : WordStackConfig)
    (codeBuffer codeLength dataBuffer dataLength : Nat) : Option (StackProg α) := do
  let codeBuffer ← wordStackLocation config codeBuffer
  let codeLength ← wordStackLocation config codeLength
  let dataBuffer ← wordStackLocation config dataBuffer
  let dataLength ← wordStackLocation config dataLength
  match codeBuffer, codeLength, dataBuffer, dataLength with
  | .register codeBuffer, .register codeLength,
      .register dataBuffer, .register dataLength =>
      pure (.install codeBuffer codeLength dataBuffer dataLength 0)
  | _, _, _, _ => none

def wordStackBufferWrite (config : WordStackConfig) (isCode : Bool)
    (address value : Nat) : Option (StackProg α) := do
  let address ← wordStackLocation config address
  let value ← wordStackLocation config value
  match address, value with
  | .register address, .register value =>
      pure (if isCode then .codeBufferWrite address value
        else .dataBufferWrite address value)
  | _, _ => none

def wordStackAtomNat (config : WordStackConfig) (temporary : Nat) :
    WordExp Nat → Option (StackProg Nat × Nat)
  | .const value => some (.const temporary value, temporary)
  | .var name => wordStackReadRegister config name temporary
  | .lookup store => do
      let store ← wordStackStoreNameNat store
      pure (.get temporary store, temporary)
  | _ => none

def wordStackWritePhysicalNat (config : WordStackConfig) (destination : Nat)
    (body : Nat → StackProg Nat) : Option (StackProg Nat) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register => pure (body register)
  | .stack slot =>
      pure (wordStackJoin (body config.scratch)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackCompileBinaryNat (config : WordStackConfig) (destination : Nat)
    (operator : BinOp) (left right : WordExp Nat) : Option (StackProg Nat) := do
  let (leftPrelude, leftRegister) ←
    wordStackAtomNat config config.scratch left
  let (rightPrelude, rightRegister) ←
    wordStackAtomNat config config.addressScratch right
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .arith operator register leftRegister rightRegister)
  pure (wordStackJoin leftPrelude (wordStackJoin rightPrelude body))

def wordStackCompileShiftNat (config : WordStackConfig) (destination : Nat)
    (operator : Shift) (left right : WordExp Nat) : Option (StackProg Nat) := do
  let (leftPrelude, leftRegister) ←
    wordStackAtomNat config config.scratch left
  let (rightPrelude, rightRegister) ←
    wordStackAtomNat config config.addressScratch right
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .shift operator register leftRegister rightRegister)
  pure (wordStackJoin leftPrelude (wordStackJoin rightPrelude body))

def wordStackCompileLoadNat (config : WordStackConfig) (destination : Nat)
    (address : WordExp Nat) : Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .inst (.mem .load register addressRegister))
  pure (wordStackJoin addressPrelude body)

def wordStackCompileStoreNat (config : WordStackConfig) (address : WordExp Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let (valuePrelude, valueRegister) ←
    wordStackAtomNat config config.scratch value
  pure (wordStackJoin addressPrelude
    (wordStackJoin valuePrelude (.inst (.mem .store valueRegister addressRegister))))

def wordStackCompileSharedNat (config : WordStackConfig)
    (operator : WordMemOp) (destination : Nat) (address : WordExp Nat) :
    Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .shMem operator register addressRegister)
  pure (wordStackJoin addressPrelude body)

def wordStackCompileExpNat (config : WordStackConfig) (destination : Nat) :
    WordExp Nat → Option (StackProg Nat)
  | .const value =>
      wordStackWritePhysicalNat config destination (.const · value)
  | .var source => wordStackMove config destination source
  | .lookup store => do
      let store ← wordStackStoreNameNat store
      let body ← wordStackWritePhysicalNat config destination
        (.get · store)
      pure body
  | .load address => wordStackCompileLoadNat config destination address
  | .op operator [left, right] =>
      wordStackCompileBinaryNat config destination operator left right
  | .op _ _ => none
  | .shift operator left right =>
      wordStackCompileShiftNat config destination operator left right

def wordStackSetNat (config : WordStackConfig) (store : WordStore Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let store ← wordStackStoreNameNat store
  let (prelude, register) ← wordStackAtomNat config config.scratch value
  pure (wordStackJoin prelude (.set store register))

def wordStackMoveFromPhysical (config : WordStackConfig)
    (destination source : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = source then pure .skip
      else pure (.arith .or register source source)
  | .stack slot =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackMoveToPhysical (config : WordStackConfig)
    (source destination : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))

def wordStackLocationMove (config : WordStackConfig)
    (destination source : WordLocation) : Option (StackProg α) :=
  match destination, source with
  | .register destination, .register source =>
      if destination = source then some .skip
      else some (.arith .or destination source source)
  | .register destination, .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))
  | .stack slot, .register source =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))
  | .stack destinationSlot, .stack sourceSlot =>
      if destinationSlot = sourceSlot then
        some .skip
      else
        pure (.seq (.stackLoad config.scratch
            (wordStackOffset config sourceSlot))
          (.stackStore config.scratch (wordStackOffset config destinationSlot)))

def wordStackLocationMoveToScratch (config : WordStackConfig)
    (source : WordLocation) : Option (StackProg α) :=
  match source with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or config.addressScratch register register)
  | .stack slot =>
      pure (.stackLoad config.addressScratch (wordStackOffset config slot))

def wordStackLocationMoveFromScratch (config : WordStackConfig)
    (destination : WordLocation) : Option (StackProg α) :=
  match destination with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or register config.addressScratch config.addressScratch)
  | .stack slot =>
      pure (.stackStore config.addressScratch (wordStackOffset config slot))

def wordStackLocationMoveDestinations
    (moves : List (WordLocation × WordLocation)) : List WordLocation :=
  moves.map (fun move => move.1)

def wordStackLocationMoveRemoveDestination (destination : WordLocation) :
    List (WordLocation × WordLocation) → List (WordLocation × WordLocation) :=
  List.filter (fun move => move.1 != destination)

def wordStackLocationMoveReady (destinations : List WordLocation) :
    List (WordLocation × WordLocation) → Option (WordLocation × WordLocation)
  | [] => none
  | move :: moves =>
      if move.1 = move.2 || move.2 ∉ destinations then
        some move
      else
        wordStackLocationMoveReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordStackParallelLocationMoveAux (config : WordStackConfig) :
    Nat → List (WordLocation × WordLocation) → Option (StackProg α)
  | 0, _ => none
  | fuel + 1, moves =>
      let destinations := wordStackLocationMoveDestinations moves
      let reserved location :=
        location = .register config.scratch ||
          location = .register config.addressScratch
      if moves.any (fun move => reserved move.1 || reserved move.2) then
        none
      else if !destinations.Nodup then
        none
      else if moves.isEmpty then
        some .skip
      else
        match wordStackLocationMoveReady destinations moves with
        | some (destination, source) => do
            let first ← wordStackLocationMove config destination source
            let rest ← wordStackParallelLocationMoveAux config fuel
              (wordStackLocationMoveRemoveDestination destination moves)
            pure (wordStackJoin first rest)
        | none =>
            match moves with
            | [] => some .skip
            | (destination, source) :: _ => do
                if config.scratch = config.addressScratch then none else
                  let save ← wordStackLocationMoveToScratch config source
                  let rest ← wordStackParallelLocationMoveAux config fuel
                    (wordStackLocationMoveRemoveDestination destination moves)
                  let restore ← wordStackLocationMoveFromScratch config destination
                  pure (wordStackJoin save (wordStackJoin rest restore))

def wordStackParallelLocationMove (config : WordStackConfig)
    (moves : List (WordLocation × WordLocation)) : Option (StackProg α) :=
  wordStackParallelLocationMoveAux config (moves.length + 1) moves

def wordStackPhysicalMovesFrom (config : WordStackConfig) :
    List Nat → Nat → Option (List (WordLocation × WordLocation))
  | [], _ => some []
  | destination :: destinations, source => do
      let destination ← wordStackLocation config destination
      let rest ← wordStackPhysicalMovesFrom config destinations (source + 2)
      pure ((destination, .register source) :: rest)
termination_by destinations => sizeOf destinations
decreasing_by all_goals decreasing_trivial

def wordStackPhysicalMovesTo (config : WordStackConfig) :
    List Nat → Nat → Option (List (WordLocation × WordLocation))
  | [], _ => some []
  | source :: sources, destination => do
      let source ← wordStackLocation config source
      let rest ← wordStackPhysicalMovesTo config sources (destination + 2)
      pure ((.register destination, source) :: rest)
termination_by sources => sizeOf sources
decreasing_by all_goals decreasing_trivial

def wordStackMovesFromPhysical (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | destinations, source => do
      let moves ← wordStackPhysicalMovesFrom config destinations source
      wordStackParallelLocationMove config moves

def wordStackMovesToPhysical (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | sources, destination => do
      let moves ← wordStackPhysicalMovesTo config sources destination
      wordStackParallelLocationMove config moves

def wordStackReturnCode (config : WordStackConfig) :
    Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat) →
      Option (StackProg α)
  | none => some .skip
  | some (destinations, _, _, _, _) =>
      wordStackMovesFromPhysical config destinations 2

def wordStackReturn (config : WordStackConfig) (values : List Nat) :
    Option (StackProg α) := do
  let moves ← wordStackMovesToPhysical config values 2
  match values with
  | [] => pure moves
  | _ => pure (wordStackJoin moves (.return 2))

def wordToStackInst (config : WordStackConfig) : WordInst → Option (StackProg α)
  | .mem operator sourceOrDestination address =>
      wordStackMemoryInst config operator sourceOrDestination address
  | .arith operation => wordStackArithInst config operation

/-! A compact executable semantics for the move fragment.  StackLang uses
natural-number register names, so this boundary deliberately models the
register file and frame slots independently of the later byte-addressed
RISC-V stack representation. -/
structure WordStackState (width : Nat) where
  registers : Nat → Word width
  stack : Nat → Word width

def wordStackWriteRegister [NeZero width] (state : WordStackState width)
    (register : Nat) (value : Word width) : WordStackState width :=
  { state with registers := fun current =>
      if current = register then value else state.registers current }

def wordStackWriteSlot [NeZero width] (state : WordStackState width)
    (slot : Nat) (value : Word width) : WordStackState width :=
  { state with stack := fun current =>
      if current = slot then value else state.stack current }

def evalWordStackBasic [NeZero width] (state : WordStackState width) :
    StackProg α → Option (WordStackState width)
  | .skip => some state
  | .arith .or destination left right =>
      some (wordStackWriteRegister state destination
        (state.registers left ||| state.registers right))
  | .stackLoad register offset =>
      some (wordStackWriteRegister state register (state.stack offset))
  | .stackStore register offset =>
      some (wordStackWriteSlot state offset (state.registers register))
  | .seq first second => do
      let state ← evalWordStackBasic state first
      evalWordStackBasic state second
  | _ => none

/-! A slightly richer executable StackLang semantics for the concrete Nat
    compiler.  It is intentionally an abstract word-memory model: byte
    layout and RISC-V instruction encoding remain below StackLang, while this
    state is sufficient to state expression-lowering preservation. -/

structure WordStackMachineState (width : Nat) where
  registers : Nat → Word width
  stack : Nat → Word width
  stores : StackStore → Word width
  memory : Word width → Word width
  sharedMemory : Word width → Word width

def wordStackMachineWriteRegister (state : WordStackMachineState width)
    (register : Nat) (value : Word width) : WordStackMachineState width :=
  { state with registers := fun current =>
      if current = register then value else state.registers current }

def wordStackMachineWriteSlot (state : WordStackMachineState width)
    (slot : Nat) (value : Word width) : WordStackMachineState width :=
  { state with stack := fun current =>
      if current = slot then value else state.stack current }

def wordStackMachineWriteStore (state : WordStackMachineState width)
    (store : StackStore) (value : Word width) : WordStackMachineState width :=
  { state with stores := fun current =>
      if current = store then value else state.stores current }

def wordStackMachineWriteMemory (state : WordStackMachineState width)
    (address value : Word width) : WordStackMachineState width :=
  { state with memory := fun current =>
      if current = address then value else state.memory current }

def wordStackMachineWriteSharedMemory (state : WordStackMachineState width)
    (address value : Word width) : WordStackMachineState width :=
  { state with sharedMemory := fun current =>
      if current = address then value else state.sharedMemory current }

def wordStackMachineBinOp : BinOp → Word width → Word width → Word width
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .and, left, right => left &&& right
  | .or, left, right => left ||| right
  | .xor, left, right => left ^^^ right

def wordStackMachineRotateRight (value : Word width) (amount : Word width) :
    Word width :=
  let amount := amount.toNat % width
  BitVec.ushiftRight value amount |||
    BitVec.shiftLeft value ((width - amount) % width)

def wordStackMachineShift : Shift → Word width → Word width → Word width
  | .lsl, left, right => BitVec.shiftLeft left (shiftAmount right)
  | .lsr, left, right => BitVec.ushiftRight left (shiftAmount right)
  | .asr, left, right => BitVec.sshiftRight left (shiftAmount right)
  | .ror, left, right => wordStackMachineRotateRight left right

def evalWordStackMachine [NeZero width]
    (state : WordStackMachineState width) :
    StackProg Nat → Option (WordStackMachineState width)
  | .skip => some state
  | .const destination value =>
      some (wordStackMachineWriteRegister state destination
        (BitVec.ofNat width value))
  | .arith operator destination left right =>
      some (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator
          (state.registers left) (state.registers right)))
  | .shift operator destination left right =>
      some (wordStackMachineWriteRegister state destination
        (wordStackMachineShift operator
          (state.registers left) (state.registers right)))
  | .inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) =>
      let left := state.registers sourceLeft
      let right := state.registers sourceRight
      let high := BitVec.ofNat width (left.toNat * right.toNat / 2 ^ width)
      let state := wordStackMachineWriteRegister state destinationLeft high
      some (wordStackMachineWriteRegister state destinationRight (left * right))
  | .inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)) =>
      let left := state.registers sourceLeft
      let right := state.registers sourceRight
      let carry := if state.registers carryIn == 0 then 0 else 1
      let total := left.toNat + right.toNat + carry
      let state := wordStackMachineWriteRegister state destination
        (BitVec.ofNat width total)
      some (wordStackMachineWriteRegister state resultCarry
        (BitVec.ofNat width (total / 2 ^ width)))
  | .inst (.arith (.div destination dividend divisor)) =>
      let divisorValue := state.registers divisor
      let value := if divisorValue == 0 then
        BitVec.ofNat width (2 ^ width - 1)
      else
        BitVec.ofNat width (state.registers dividend).toNat / divisorValue.toNat
      some (wordStackMachineWriteRegister state destination value)
  | .inst (.mem .load destination address) =>
      some (wordStackMachineWriteRegister state destination
        (state.memory (state.registers address)))
  | .inst (.mem .store source address) =>
      some (wordStackMachineWriteMemory state
        (state.registers address) (state.registers source))
  | .shMem .load destination address =>
      some (wordStackMachineWriteRegister state destination
        (state.sharedMemory (state.registers address)))
  | .shMem .store source address =>
      some (wordStackMachineWriteSharedMemory state
        (state.registers address) (state.registers source))
  | .get destination store =>
      some (wordStackMachineWriteRegister state destination (state.stores store))
  | .set store source =>
      some (wordStackMachineWriteStore state store (state.registers source))
  | .stackLoad register offset =>
      some (wordStackMachineWriteRegister state register (state.stack offset))
  | .stackStore register offset =>
      some (wordStackMachineWriteSlot state offset (state.registers register))
  | .seq first second => do
      let state ← evalWordStackMachine state first
      evalWordStackMachine state second
  | _ => none

def wordStackMachineValue [NeZero width] (config : WordStackConfig)
    (state : WordStackMachineState width) (name : Nat) : Option (Word width) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => some (state.registers register)
  | .stack slot => some (state.stack (wordStackOffset config slot))

def wordStackBinaryLocationsSafe (config : WordStackConfig) :
    WordLocation → WordLocation → Bool
  | .register _, .register _ => true
  | .register left, .stack _ => left != config.addressScratch
  | .stack _, .register right => right != config.scratch
  | .stack _, .stack _ => config.scratch != config.addressScratch

theorem evalWordStackMachine_const_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination value : Nat) (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (heval : (wordStackCompileExpNat config destination (.const value)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (BitVec.ofNat width value) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  simp [wordStackCompileExpNat, wordStackWritePhysicalNat] at heval
  cases destinationLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister, 
      hdestination] at heval ⊢
  all_goals
    cases heval
    simp [
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat) (destinationLocation sourceLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestinationScratch : destinationLocation ≠ .register config.scratch)
    (hsourceScratch : sourceLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        wordStackMachineValue config state source := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  simp [wordStackMove] at heval
  cases destinationLocation <;> cases sourceLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, hsource,
      ] at heval ⊢
  all_goals
    cases heval
    simp [
      
      wordStackMachineBinOp,
      ]

theorem evalWordStackMachine_lookup_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination : Nat) (store : WordStore Nat) (stackStore : StackStore)
    (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (heval : (wordStackCompileExpNat config destination (.lookup store)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.stores stackStore) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases destinationLocation <;>
      simp [wordStackCompileExpNat, wordStackStoreNameNat,
        wordStackWritePhysicalNat] at heval
  all_goals
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      hdestination] at heval ⊢
  all_goals
    cases heval
    simp [
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_set_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (stackStore : StackStore) (source : Nat)
    (sourceLocation : WordLocation) (sourceValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (heval : (wordStackSetNat config store (.var source)).bind
      (evalWordStackMachine state) = some final) :
      final.stores stackStore = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases sourceLocation <;>
    simp [wordStackSetNat, wordStackStoreNameNat, wordStackAtomNat,
      wordStackReadRegister, wordStackLocation, wordStackOffset,
      wordStackJoin, evalWordStackMachine, hsource] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource] at hsourceValue
    simp [wordStackMachineWriteRegister, wordStackMachineWriteStore,
      hsourceValue]

theorem evalWordStackMachine_binary_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : BinOp) (destination left right : Nat)
    (destinationLocation leftLocation rightLocation : WordLocation)
    (leftValue rightValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hleftValue : wordStackMachineValue config state left = some leftValue)
    (hrightValue : wordStackMachineValue config state right = some rightValue)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
    (heval : (wordStackCompileBinaryNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (wordStackMachineBinOp operator leftValue rightValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo left config.locations = some leftLocation at hleft
  change lookupNatInfo right config.locations = some rightLocation at hright
  cases destinationLocation <;> cases leftLocation <;> cases rightLocation <;>
    simp [wordStackCompileBinaryNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, hleft, hright, wordStackBinaryLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hleft, hright] at hleftValue hrightValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      wordStackMachineBinOp, hdestination, hleftValue, hrightValue, hsafe]

theorem evalWordStackMachine_shift_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : Shift) (destination left right : Nat)
    (destinationLocation leftLocation rightLocation : WordLocation)
    (leftValue rightValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hleftValue : wordStackMachineValue config state left = some leftValue)
    (hrightValue : wordStackMachineValue config state right = some rightValue)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
    (heval : (wordStackCompileShiftNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (wordStackMachineShift operator leftValue rightValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo left config.locations = some leftLocation at hleft
  change lookupNatInfo right config.locations = some rightLocation at hright
  cases destinationLocation <;> cases leftLocation <;> cases rightLocation <;>
    simp [wordStackCompileShiftNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, hleft, hright, wordStackBinaryLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hleft, hright] at hleftValue hrightValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      wordStackMachineShift, hdestination, hleftValue, hrightValue, hsafe]

theorem evalWordStackMachine_load_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (addressValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (heval : (wordStackCompileLoadNat config destination (.var address)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.memory addressValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackCompileLoadNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, haddress] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      haddress] at haddressValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      haddressValue, hdestination]

theorem evalWordStackMachine_load_const_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat) (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (heval : (wordStackCompileLoadNat config destination (.const address)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.memory (BitVec.ofNat width address)) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  cases destinationLocation <;>
    simp [wordStackCompileLoadNat, wordStackAtomNat, wordStackWritePhysicalNat,
      evalWordStackMachine, wordStackJoin, wordStackLocation,
      wordStackOffset, hdestination] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, hdestination]

theorem evalWordStackMachine_store_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackCompileStoreNat config (.var address) (.var source)).bind
      (evalWordStackMachine state) = some final) :
      final.memory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackCompileStoreNat, wordStackAtomNat, wordStackReadRegister,
      wordStackJoin, evalWordStackMachine, wordStackLocation, wordStackOffset,
      hsource, haddress, wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteMemory, hsourceValue,
      haddressValue, hsafe, hsafe']

def wordStackValue [NeZero width] (config : WordStackConfig)
    (state : WordStackState width) (name : Nat) : Option (Word width) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => some (state.registers register)
  | .stack slot => some (state.stack (wordStackOffset config slot))

theorem evalWordStackBasic_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackState width)
    (destination source : Nat) (destinationLocation sourceLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination_scratch : destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackBasic state) = some final) :
      wordStackValue config final destination =
      wordStackValue config state source := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  simp [wordStackMove] at heval
  cases destinationLocation <;> cases sourceLocation <;>
    simp [evalWordStackBasic, wordStackValue, wordStackLocation,
      wordStackOffset, wordStackWriteRegister, wordStackWriteSlot,
      hdestination, hsource] at heval ⊢
  all_goals
    cases heval
    simp [
      
      ]

theorem evalWordStackBasic_move_to_physical_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackState width)
    (source destination : Nat) (sourceLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (heval : (wordStackMoveToPhysical (α := Nat) config source destination).bind
      (evalWordStackBasic state) = some final) :
      final.registers destination = wordStackValue config state source := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      by_cases hsame : register = destination
      · simp [wordStackMoveToPhysical, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        simp [wordStackValue, wordStackLocation, 
          hsource, hsame]
      · simp [wordStackMoveToPhysical, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        simp [wordStackValue, wordStackLocation,
          wordStackWriteRegister, hsource]
  | stack slot =>
      simp [wordStackMoveToPhysical, wordStackLocation, 
        hsource] at heval
      cases heval
      simp [wordStackValue, wordStackLocation,
        wordStackOffset, wordStackWriteRegister, hsource]

theorem evalWordStackMachine_ffi_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination : Nat) (sourceLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination : sourceLocation ≠ .register destination)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
      final.registers destination = wordStackMachineValue config state source := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      have hregister : register ≠ destination := by
        intro heq
        apply hdestination
        simp [heq]
      simp [wordStackFfiMove, wordStackLocation, 
        hsource, hregister] at heval
      cases heval
      simp [wordStackMachineValue, wordStackLocation,
        wordStackMachineWriteRegister, wordStackMachineBinOp, hsource,
        ]
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at heval
      cases heval
      simp [wordStackMachineValue,
        wordStackLocation, wordStackOffset, wordStackMachineWriteRegister,
        hsource]

theorem evalWordStackMachine_ffi_move_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination other : Nat) (sourceLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hsource_destination : sourceLocation ≠ .register destination)
    (hother_destination : otherLocation ≠ .register destination)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final other =
        wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases sourceLocation with
  | register sourceRegister =>
      have hsourceRegister : sourceRegister ≠ destination := by
        intro heq
        apply hsource_destination
        simp [heq]
      simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
        hsource, hsourceRegister] at heval
      cases heval
      cases otherLocation with
      | register otherRegister =>
          have hotherRegister : otherRegister ≠ destination := by
            intro heq
            apply hother_destination
            simp [heq]
          simp [wordStackMachineValue, wordStackLocation,
            wordStackMachineWriteRegister, wordStackMachineBinOp, hother,
            hotherRegister]
      | stack otherSlot =>
          simp [wordStackMachineValue, wordStackLocation,
            wordStackMachineWriteRegister, wordStackMachineBinOp, hother]
  | stack sourceSlot =>
      simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
        hsource] at heval
      cases heval
      cases otherLocation with
      | register otherRegister =>
          have hotherRegister : otherRegister ≠ destination := by
            intro heq
            apply hother_destination
            simp [heq]
          simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
            wordStackMachineWriteRegister, hother, hotherRegister]
      | stack otherSlot =>
          simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
            wordStackMachineWriteRegister, hother]

theorem evalWordStackMachine_load_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hscratch : config.scratch ≠ config.addressScratch)
    (heval : (wordStackMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        (wordStackMachineValue config state address).map state.memory := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackMemoryInst, wordStackLoadInst, wordStackLocation,
      wordStackOffset, hdestination, haddress,
      ] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, haddress]

theorem evalWordStackMachine_store_preserves_memory [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
      final.memory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
      wordStackOffset, hsource, haddress,
      wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteMemory, hsourceValue,
      haddressValue, hsafe, hsafe']

theorem evalWordStackMachine_shared_load_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hscratch : config.scratch ≠ config.addressScratch)
    (heval : (wordStackSharedMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        (wordStackMachineValue config state address).map state.sharedMemory := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackSharedMemoryInst, wordStackSharedLoadInst,
      wordStackLocation, wordStackOffset, hdestination,
      haddress] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, 
      hdestination, haddress]

theorem evalWordStackMachine_shared_store_preserves_memory [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackSharedMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
      final.sharedMemory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackSharedMemoryInst, wordStackSharedStoreInst,
      wordStackLocation, wordStackOffset, hsource, haddress,
      wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteSharedMemory, 
      hsourceValue, haddressValue, hsafe, hsafe']

theorem evalWordStackMachine_div_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination dividend divisor : Nat)
    (destinationLocation dividendLocation divisorLocation : WordLocation)
    (dividendValue divisorValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hdividend : wordStackLocation config dividend = some dividendLocation)
    (hdivisor : wordStackLocation config divisor = some divisorLocation)
    (hdividendValue : wordStackMachineValue config state dividend =
      some dividendValue)
    (hdivisorValue : wordStackMachineValue config state divisor =
      some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hdestinationSafe : wordStackDivLocationSafe config destinationLocation = true)
    (hdividendSafe : wordStackDivLocationSafe config dividendLocation = true)
    (hdivisorSafe : wordStackDivLocationSafe config divisorLocation = true)
    (heval : (wordStackDivInst config destination dividend divisor).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo dividend config.locations = some dividendLocation at hdividend
  change lookupNatInfo divisor config.locations = some divisorLocation at hdivisor
  have hscratch' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases destinationLocation <;> cases dividendLocation <;> cases divisorLocation <;>
    simp [wordStackDivInst, wordStackJoin, wordStackLocation, wordStackOffset,
      hdestination, hdividend, hdivisor,
      wordStackDivLocationSafe] at hdestinationSafe hdividendSafe hdivisorSafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hdividend, hdivisor] at hdividendValue hdivisorValue
    have hdivisorNonzero' : ¬divisorValue = (0#width) := by
      intro hz
      apply hdivisorNonzero
      simpa using hz
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      hdestination, hdividendValue, hdivisorValue,
      hdivisorNonzero', hdividendSafe, hdivisorSafe,
      hscratch, BitVec.udiv_def]

def wordToStackProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α] [DecidableRel (fun left right : α => left < right)]
    (config : WordStackConfig) : WordProg α → Option (StackProg α)
  | .skip => some .skip
  | .move _ moves => wordStackMoveList config moves
  | .assign destination (.var source) =>
      wordStackMove config destination source
  | .locValue destination source =>
      wordStackMove config destination source
  | .inst instruction =>
      wordToStackInst config instruction
  | .get destination store =>
      wordStackGet config destination store
  | .store (.var address) value =>
      wordStackMemoryInst config .store value address
  | .set store (.var source) => do
      let store ← wordStackStoreName store
      let (prelude, register) ←
        wordStackReadRegister config source config.scratch
      pure (wordStackJoin prelude (.set store register))
  | .seq first second => do
      let first ← wordToStackProg config first
      let second ← wordToStackProg config second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let thenBranch ← wordToStackProg config thenBranch
      let elseBranch ← wordToStackProg config elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch))
  | .loop _ body _ => do
      let body ← wordToStackProg config body
      pure (.loop body)
  | .mustTerminate body => wordToStackProg config body
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return _ values => wordStackReturn config values
  | .call none (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      pure (wordStackJoin argumentMoves
        (.call none (.label target) none))
  | .tick => pure .tick
  | .call returns (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        config.returnLabel config.entryLabel
      pure (wordStackJoin argumentMoves callCode)
  | .call returns (some target) arguments
      (some (exception, body, handlerLabel, entryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let handlerCode ← wordToStackProg config body
      let callCode := wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception
      pure (wordStackJoin argumentMoves callCode)
  | .opCurrHeap operator destination source =>
      wordStackOpCurrHeap config operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      wordStackInstall config codeBuffer codeLength dataBuffer dataLength
  | .codeBufferWrite address value =>
      wordStackBufferWrite config true address value
  | .dataBufferWrite address value =>
      wordStackBufferWrite config false address value
  | .alloc _ _ | .storeConsts _ _ _ _ _ => none
  | .ffi function configuration configurationLength array arrayLength _ =>
      wordStackFfi config function configuration configurationLength array arrayLength
  | .shareInst operator name (.var address) =>
      wordStackSharedMemoryInst config operator name address
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! Concrete program compiler.  This specializes only the value representation
    (constants and temporary store names) to `Nat`; the generic compiler above
    remains available for syntax-only clients. -/

def wordToStackProgNat [BEq Nat] (config : WordStackConfig) :
    WordProg Nat → Option (StackProg Nat)
  | .skip => some .skip
  | .move _ moves => wordStackMoveList config moves
  | .assign destination value => wordStackCompileExpNat config destination value
  | .locValue destination source => wordStackMove config destination source
  | .inst instruction => wordToStackInst config instruction
  | .get destination store => wordStackGet config destination store
  | .store address value =>
      wordStackCompileStoreNat config address (.var value)
  | .set store value => wordStackSetNat config store value
  | .seq first second => do
      let first ← wordToStackProgNat config first
      let second ← wordToStackProgNat config second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let thenBranch ← wordToStackProgNat config thenBranch
      let elseBranch ← wordToStackProgNat config elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch))
  | .loop _ body _ => do
      let body ← wordToStackProgNat config body
      pure (.loop body)
  | .mustTerminate body => wordToStackProgNat config body
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return _ values => wordStackReturn config values
  | .call none (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      pure (wordStackJoin argumentMoves
        (.call none (.label target) none))
  | .tick => pure .tick
  | .call returns (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        config.returnLabel config.entryLabel
      pure (wordStackJoin argumentMoves callCode)
  | .call returns (some target) arguments
      (some (exception, body, handlerLabel, entryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      let returnCode ← wordStackReturnCode config returns
      let handlerCode ← wordToStackProgNat config body
      let callCode := wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception
      pure (wordStackJoin argumentMoves callCode)
  | .call _ none _ _ => none
  | .opCurrHeap operator destination source =>
      wordStackOpCurrHeap config operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      wordStackInstall config codeBuffer codeLength dataBuffer dataLength
  | .codeBufferWrite address value =>
      wordStackBufferWrite config true address value
  | .dataBufferWrite address value =>
      wordStackBufferWrite config false address value
  | .alloc _ _ | .storeConsts _ _ _ _ _ => none
  | .ffi function configuration configurationLength array arrayLength _ =>
      wordStackFfi config function configuration configurationLength array arrayLength
  | .shareInst operator name address =>
      wordStackCompileSharedNat config operator name address
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! Stateful variant of the Word-to-Stack compiler.

    The ordinary compiler above intentionally has no bitmap accumulator and
    therefore leaves Alloc and StoreConsts unavailable.  This variant
    follows CakeML's comp state threading for those constructors, structured
    sequencing, and handler bodies.  Other leaves use the existing lowering
    above. -/
def wordToStackProgNatWithBitmapBuilder [BEq Nat]
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState)
  | .seq first second => do
      let (first, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state first
      let (second, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state second
      pure (.seq first second, state)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let (thenBranch, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state thenBranch
      let (elseBranch, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch), state)
  | .loop liveIn body liveOut => do
      let (body, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state body
      pure (.loop body, state)
  | .mustTerminate body =>
      wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount bitmapRegister frameSlots
        wordBits storeConstsStub state body
  | .call returns (some target) arguments
      (some (exception, body, handlerLabel, entryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments 2
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let (handlerCode, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception
      pure (wordStackJoin argumentMoves callCode, state)
  | .alloc _ (_, live) =>
      let (program, state) := wordStackAllocWithBitmapBuilder config bitmapRegister
        frameSlots state live bitmapBuilder
      pure (program, state)
  | .storeConsts _ _ _ _ constants =>
      let (program, state) := wordStackStoreConstsWithBitmaps config registerCount
        config.specialScratch wordBits storeConstsStub state constants
      pure (program, state)
  | program =>
      (wordToStackProgNat config program).map (fun program => (program, state))
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordToStackProgNatWithBitmaps [BEq Nat]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithBitmapBuilder config
    (wordStackLiveBitmap registerCount frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state

theorem wordStackBitmapState_insert_length
    (state : WordStackBitmapState) (bitmap : List Nat)
    (hstate : state.length = state.data.length) :
    (wordStackInsertBitmap state bitmap).1.length =
      (wordStackInsertBitmap state bitmap).1.data.length := by
  simp [wordStackInsertBitmap, hstate]

theorem wordStackBitmapState_alloc_length
    (config : WordStackConfig) (bitmapRegister frameSlots : Nat)
    (state : WordStackBitmapState) (live : List Nat)
    (bitmapBuilder : List Nat → List Nat)
    (hstate : state.length = state.data.length) :
    (wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state
      live bitmapBuilder).2.length =
      (wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state
        live bitmapBuilder).2.data.length := by
  by_cases hframes : frameSlots = 0
  · simp [wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      hframes, hstate]
  · simp [wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      wordStackInsertBitmap, hframes, hstate]

theorem wordStackBitmapState_storeConsts_length
    (config : WordStackConfig) (registerCount specialScratch wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (constants : List (Bool × Nat))
    (hstate : state.length = state.data.length) :
    (wordStackStoreConstsWithBitmaps config registerCount specialScratch wordBits
      storeConstsStub state constants).2.length =
      (wordStackStoreConstsWithBitmaps config registerCount specialScratch wordBits
        storeConstsStub state constants).2.data.length := by
  simp [wordStackStoreConstsWithBitmaps, wordStackInsertBitmap, hstate]

theorem wordToStackProgNatWithBitmapBuilder_preserves_length
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg Nat)
    (hstate : state.length = state.data.length)
    (compiled : StackProg Nat) (finalState : WordStackBitmapState)
    (hresult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state program =
      some (compiled, finalState)) :
    finalState.length = finalState.data.length := by
  cases program <;> try simp [wordToStackProgNatWithBitmapBuilder, Option.bind] at hresult
  all_goals try
    (rcases hresult with ⟨_, _, rfl, rfl⟩
      <;> exact hstate)
  case seq first second =>
      generalize hfirstResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state first =
        firstResult at hresult
      cases firstResult with
      | none => simp_all
      | some firstPair =>
          cases firstPair with
          | mk firstCode firstState =>
              have hfirst : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                  registerCount bitmapRegister frameSlots wordBits storeConstsStub state first =
                  some (firstCode, firstState) := hfirstResult
              simp [] at hresult
              generalize hsecondResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                registerCount bitmapRegister frameSlots wordBits storeConstsStub firstState second =
                secondResult at hresult
              cases secondResult with
              | none => simp_all
              | some secondPair =>
                  cases secondPair with
                  | mk secondCode secondFinalState =>
                      have hsecond : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                          registerCount bitmapRegister frameSlots wordBits storeConstsStub firstState second =
                          some (secondCode, secondFinalState) := hsecondResult
                      simp [] at hresult
                      have hfirstState := wordToStackProgNatWithBitmapBuilder_preserves_length
                        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                        storeConstsStub state first hstate firstCode firstState hfirst
                      have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                        storeConstsStub firstState second hfirstState secondCode
                        secondFinalState hsecond
                      rcases hresult with ⟨_, rfl⟩
                      exact hfinal
  case ite operator condition right thenBranch elseBranch =>
      generalize hconditionResult : wordStackConditionOperands config condition right =
        conditionResult at hresult
      cases conditionResult with
      | none => simp_all
      | some conditionPair =>
          cases conditionPair with
          | mk conditionPrelude conditionRest =>
              cases conditionRest with
              | mk conditionRegister rightOperand =>
                  simp [] at hresult
                  generalize hthenResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                    registerCount bitmapRegister frameSlots wordBits storeConstsStub state thenBranch =
                    thenResult at hresult
                  cases thenResult with
                  | none => simp_all
                  | some thenPair =>
                      cases thenPair with
                      | mk thenCode thenState =>
                          simp [] at hresult
                          generalize helseResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                            registerCount bitmapRegister frameSlots wordBits storeConstsStub thenState elseBranch =
                            elseResult at hresult
                          cases elseResult with
                          | none => simp_all
                          | some elsePair =>
                              cases elsePair with
                              | mk elseCode finalResult =>
                                  have hthenState := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub state thenBranch hstate thenCode thenState hthenResult
                                  have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub thenState elseBranch hthenState elseCode finalResult
                                    helseResult
                                  rcases hresult with ⟨_, rfl⟩
                                  exact hfinal
  case loop liveIn body liveOut =>
      generalize hbodyResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
        bodyResult at hresult
      cases bodyResult with
      | none => simp_all
      | some bodyPair =>
          cases bodyPair with
          | mk bodyCode finalResult =>
              have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                storeConstsStub state body hstate bodyCode finalResult hbodyResult
              rcases hresult with ⟨_, rfl⟩
              exact hfinal
  case mustTerminate body =>
      exact wordToStackProgNatWithBitmapBuilder_preserves_length
        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state body hstate compiled finalState hresult
  case call returns target arguments handler =>
      cases target with
      | none =>
          simp [wordToStackProgNatWithBitmapBuilder] at hresult
          rcases hresult with ⟨_, _, rfl, rfl⟩
          exact hstate
      | some target =>
          cases handler with
          | none =>
              simp [wordToStackProgNatWithBitmapBuilder] at hresult
              rcases hresult with ⟨_, _, rfl, rfl⟩
              exact hstate
          | some handlerData =>
              rcases handlerData with ⟨exception, body, handlerLabel, entryLabel⟩
              generalize hhandlerResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
                handlerResult at hresult
              simp [wordToStackProgNatWithBitmapBuilder, hhandlerResult] at hresult
              generalize hargsResult : wordStackMovesToPhysical config arguments 2 =
                argsResult at hresult
              cases argsResult with
              | none => simp_all
              | some argumentMoves =>
                  generalize hreturnResult : wordStackReturnCode config returns =
                    returnResult at hresult
                  cases returnResult with
                  | none => simp_all
                  | some returnCode =>
                      cases handlerResult with
                      | none => simp_all
                      | some handlerPair =>
                          cases handlerPair with
                          | mk handlerCode finalResult =>
                              have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                                config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                storeConstsStub state body hstate handlerCode finalResult hhandlerResult
                              rcases hresult with ⟨_, rfl⟩
                              exact hfinal
  case alloc destination cutsets =>
      rw [wordToStackProgNatWithBitmapBuilder] at hresult
      generalize hallocResult : wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots
        state cutsets.2 bitmapBuilder = allocResult at hresult
      cases allocResult with
      | mk allocCode allocState =>
          rcases hresult with ⟨_, rfl⟩
          have hallocState := congrArg Prod.snd hallocResult
          have hallocState' : (wordStackAllocWithBitmapBuilder config bitmapRegister
              frameSlots state cutsets.2 bitmapBuilder).2 = finalState := by
            simpa using hallocState
          rw [← hallocState']
          exact wordStackBitmapState_alloc_length config bitmapRegister frameSlots state
            cutsets.2 bitmapBuilder hstate
  case storeConsts source bitmap codeLength dataLength constants =>
      rw [← hresult.2]
      exact wordStackBitmapState_storeConsts_length config registerCount
        config.specialScratch wordBits storeConstsStub state constants hstate
def wordToStackProgNatWithLocationBitmaps [BEq Nat]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithBitmapBuilder config
    (wordStackLiveBitmapFromLocations config frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state

/-! The real Word pipeline is indexed by a fixed-width bit-vector type, while
    StackProg keeps constants as natural numbers so that StackRemove can
    materialize them at the target width.  This adapter makes that boundary
    explicit: converting a Word constant to `toNat` is recovered by the
    subsequent `BitVec.ofNat` performed by the StackLang machine and LabLang
    backend. -/

def wordStoreToNat : WordStore (Word width) → WordStore Nat
  | .temp address => .temp address.toNat
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .currHeap => .currHeap
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd

def wordExpToNat : WordExp (Word width) → WordExp Nat
  | .const value => .const value.toNat
  | .var name => .var name
  | .lookup store => .lookup (wordStoreToNat store)
  | .load address => .load (wordExpToNat address)
  | .op operator arguments => .op operator (arguments.map wordExpToNat)
  | .shift operator left right =>
      .shift operator (wordExpToNat left) (wordExpToNat right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordRegImmToNat : WordRegImm (Word width) → WordRegImm Nat
  | .imm value => .imm value.toNat
  | .reg name => .reg name

def wordProgToNat : WordProg (Word width) → WordProg Nat
  | .skip => .skip
  | .move priority moves => .move priority moves
  | .assign name value => .assign name (wordExpToNat value)
  | .inst instruction => .inst instruction
  | .get destination store => .get destination (wordStoreToNat store)
  | .store address value => .store (wordExpToNat address) value
  | .set store value => .set (wordStoreToNat store) (wordExpToNat value)
  | .seq first second => .seq (wordProgToNat first) (wordProgToNat second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition (wordRegImmToNat right)
        (wordProgToNat thenBranch) (wordProgToNat elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordProgToNat body) liveOut
  | .mustTerminate body => .mustTerminate (wordProgToNat body)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return label values => .return label values
  | .tick => .tick
  | .locValue destination source => .locValue destination source
  | .call returns target arguments none =>
      .call (returns.map (fun (values, cutsets, returnCode, returnLabel, entryLabel) =>
        (values, cutsets, .skip, returnLabel, entryLabel))) target
        arguments none
  | .call returns target arguments
      (some (exception, body, handlerLabel, entryLabel)) =>
      .call (returns.map (fun (values, cutsets, returnCode, returnLabel, entryLabel) =>
        (values, cutsets, .skip, returnLabel, entryLabel))) target
        arguments (some (exception, wordProgToNat body, handlerLabel, entryLabel))
  | .alloc destination (nonGc, gc) =>
      .alloc destination (nonGc, gc)
  | .storeConsts source bitmap codeLength dataLength constants =>
      .storeConsts source bitmap codeLength dataLength
        (constants.map (fun (isByte, value) => (isByte, value.toNat)))
  | .opCurrHeap operator destination source =>
      .opCurrHeap operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc) =>
      .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc)
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function configuration configurationLength array arrayLength live
  | .shareInst operator name address =>
      .shareInst operator name (wordExpToNat address)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | (simp [sizeOf] <;> omega)

def wordToStackProgWord [NeZero width] (config : WordStackConfig)
    (program : WordProg (Word width)) : Option (StackProg Nat) :=
  wordToStackProgNat config (wordProgToNat program)

def wordToStackProgWordWithBitmaps [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithBitmaps config registerCount bitmapRegister frameSlots width
    storeConstsStub state (wordProgToNat program)

def wordToStackProgWordWithLocationBitmaps [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithLocationBitmaps config registerCount bitmapRegister frameSlots width
    storeConstsStub state (wordProgToNat program)

/-! Function-entry lowering for allocated Word programs.  Word calls place
    arguments in the even ABI registers beginning at x2; the allocator may
    place a formal parameter in a different register or in a spill slot.  The
    entry moves make that calling convention explicit before the lowered body
    starts executing. -/
def wordToStackFunctionWithParameters [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) : Option (StackProg Nat) := do
  let body ← wordToStackProgWord config program
  let parameterMoves ← wordStackMovesFromPhysical config parameters 2
  pure (wordStackJoin parameterMoves body)

def wordToStackFunctionWithParametersAndBitmaps [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithBitmaps config registerCount
    bitmapRegister frameSlots storeConstsStub state program
  let parameterMoves ← wordStackMovesFromPhysical config parameters 2
  pure (wordStackJoin parameterMoves body, state)

def wordToStackFunctionWithParametersAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmaps config registerCount
    bitmapRegister frameSlots storeConstsStub state program
  let parameterMoves ← wordStackMovesFromPhysical config parameters 2
  pure (wordStackJoin parameterMoves body, state)

/-! Public entry point for the spill-aware path.  The allocator's location
    map is authoritative for the renamed Word program; the remaining stack
    and bitmap configuration stays with the caller because it depends on the
    enclosing frame and linked runtime sections. -/
def wordToStackFunctionWithSpillStateAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordSpillState)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackFunctionWithParametersAndLocationBitmaps
    { config with locations := allocation.locations }
    parameters registerCount bitmapRegister frameSlots storeConstsStub state program

/-! Graph allocation produces the source-to-location map from the renamed
    program's graph colours.  This adapter keeps the renamed names intact and
    feeds that map directly to the location-aware StackLang lowering. -/
def wordToStackFunctionWithGraphAllocationAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordGraphAllocation) (colours stackStart : Nat)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackFunctionWithParametersAndLocationBitmaps
    { config with locations := wordGraphLocations allocation colours stackStart }
    parameters registerCount bitmapRegister frameSlots storeConstsStub state program

/-! Compose CakeML-shaped SSA/graph allocation with the actual location-aware
    StackLang entry point.  The allocation witness and renamed metadata are
    retained in the result so later linking and correctness layers can use
    the same graph proof that justified the locations. -/
def wordAllocateGraphFunctionWithStackOnlyToStack [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (fixedSources : List Nat)
    (colours stackStart : Nat) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    Option (WordSsaState × List Nat × WordGraphAllocation ×
      StackProg Nat × WordStackBitmapState) := do
  let (ssaState, renamedParameters, allocation, renamedProgram) ←
    wordAllocateGraphFunctionWithStackOnlyRenamed parameters program fixedSources
      colours stackStart
  let (stackProgram, state) ←
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps config
      renamedParameters allocation colours stackStart registerCount bitmapRegister
      frameSlots storeConstsStub state renamedProgram
  pure (ssaState, renamedParameters, allocation, stackProgram, state)

/-! Location map used by the currently register-coloured pipeline fragment.
    The spill-aware entry point above accepts the allocator-produced map
    directly; this identity helper remains useful for the register-only path.
-/
def wordStackIdentityConfig [NeZero width]
    (program : WordProg (Word width)) : WordStackConfig :=
  { locations := (wordProgVariables program).eraseDups.map
      (fun name => (name, .register name))
    scratch := 31
    stackBase := 0
    addressScratch := 29 }

theorem wordStackMove_registers :
    wordStackMove
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.arith .or 4 5 5 : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, lookupNatInfo]

theorem wordStackMove_register_to_spill :
    wordStackMove
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.arith .or 31 5 5) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMove_spill_to_register :
    wordStackMove
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.stackLoad 31 12) (.arith .or 4 31 31) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMove_spill_to_spill :
    wordStackMove
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.stackLoad 31 12) (.stackStore 31 13) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMemoryInst_load_spill_address :
    wordStackMemoryInst
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .load32 0 1 =
      some (.seq (.stackLoad 29 12) (.inst (.mem .load32 4 29)) : StackProg Nat) := by
  simp [wordStackMemoryInst, wordStackLoadInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

theorem wordStackMemoryInst_store_spill_value_and_address :
    wordStackMemoryInst
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .store32 0 1 =
      some (.seq (.stackLoad 29 12)
        (.seq (.stackLoad 31 13) (.inst (.mem .store32 31 29))) : StackProg Nat) := by
  simp [wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

theorem wordStackDivInst_spill_operands :
    wordStackDivInst
        { locations := [(0, .stack 3), (1, .stack 2), (2, .register 6)],
          scratch := 31, stackBase := 10 } 0 1 2 =
      some (.seq (.stackLoad 31 12)
        (.seq (.inst (.arith (.div 31 31 6)))
          (.stackStore 31 13)) : StackProg Nat) := by
  simp [wordStackDivInst, wordStackJoin, wordStackLocation,
    wordStackOffset, lookupNatInfo]




end Flapjack.RiscV
