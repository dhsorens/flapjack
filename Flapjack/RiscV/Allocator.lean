import Flapjack.Word

/-!
The first explicit register-allocation boundary for the Word backend.

CakeML's full `word_alloc` pass uses SSA renaming, clash colouring, and
spill-aware allocation.  Flapjack currently represents Word variables by
natural-number register names directly, so this module ports the part of the
target contract that must hold before that larger pass is introduced:

* x0 is the architectural zero register;
* x1 is the call link register;
* x27 is the third AddCarry scratch register used by spill lowering;
* x29 is the address scratch register used by stack lowering;
* x30 is the stack pointer used by ordinary calls; and
* x31 is the backend scratch register.

The allocator preserves the historical `name + 2` assignment whenever it is
safe.  Out-of-range names are assigned the first free register that is not a
preferred register of another slot.  x27 and x28 are reserved as temporaries
used by spill-aware `AddCarry` and `LongMul` lowering.  Exhaustion is reported as `none`; it
is never converted into an aliased or reserved register.
-/

namespace Flapjack

def wordAllocatableRegisters : List Nat :=
  (List.range 25).map (fun index => index + 2)

def wordPreferredRegister (name : Nat) : Option Nat :=
  let register := name + 2
  if register < 27 then some register else none

def wordPreferredRegisters : List Nat → List Nat
  | [] => []
  | name :: names =>
      match wordPreferredRegister name with
      | some register => register :: wordPreferredRegisters names
      | none => wordPreferredRegisters names

def wordRemoveRegisters (removed registers : List Nat) : List Nat :=
  match registers with
  | [] => []
  | register :: registers =>
      if register ∈ removed then
        wordRemoveRegisters removed registers
      else
        register :: wordRemoveRegisters removed registers

def wordAllocateVars : List Nat → List Nat → Option (NatInfoMap Nat)
  | [], _ => some []
  | name :: names, fallback =>
      match wordPreferredRegister name with
      | some register =>
          (wordAllocateVars names fallback).map
            (fun result => (name, register) :: result)
      | none =>
          match fallback with
          | [] => none
          | register :: fallback =>
              (wordAllocateVars names fallback).map
                (fun result => (name, register) :: result)

def wordAllocateVarsFromSlots (slots : List Nat) : Option (NatInfoMap Nat) :=
  wordAllocateVars slots
    (wordRemoveRegisters (wordPreferredRegisters slots)
      wordAllocatableRegisters)

def wordAllocateContext (slots : List Nat) : Option WordContext :=
  (wordAllocateVarsFromSlots slots).map (fun vars => { vars := vars })

def wordRegisterIsReserved (register : Nat) : Bool :=
  register == 0 || register == 1 || register == 27 || register == 28 ||
    register == 29 || register == 30 || register == 31

def wordRegisterIsAllocatable (register : Nat) : Bool :=
  register ≥ 2 && register < 27

/-! A compact executable clash-colouring interface.  CakeML builds a clash
tree from the SSA program and then colours its graph.  The current Word IR
does not yet carry the full spill metadata, but this layer already consumes
the resulting undirected clash edges instead of ignoring them. -/

def wordNeighbours (name : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (left, right) :: edges =>
      if left == name then right :: wordNeighbours name edges
      else if right == name then left :: wordNeighbours name edges
      else wordNeighbours name edges

def wordUsedRegisters (names : List Nat) (colouring : NatInfoMap Nat) : List Nat :=
  match names with
  | [] => []
  | name :: names =>
      match lookupNatInfo name colouring with
      | some register => register :: wordUsedRegisters names colouring
      | none => wordUsedRegisters names colouring

def wordFirstAvailable : List Nat → List Nat → Option Nat
  | [], _ => none
  | register :: registers, forbidden =>
      if register ∈ forbidden then
        wordFirstAvailable registers forbidden
      else some register

def wordColourCandidates (name : Nat) : List Nat :=
  match wordPreferredRegister name with
  | some register =>
      register :: wordRemoveRegisters [register] wordAllocatableRegisters
  | none => wordAllocatableRegisters

def wordGreedyColour (names : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : Option (NatInfoMap Nat) :=
  match names with
  | [] => some colouring
  | name :: names =>
      let neighbours := wordNeighbours name edges
      let forbidden := wordUsedRegisters neighbours colouring
      match wordFirstAvailable (wordColourCandidates name) forbidden with
      | none => none
      | some register =>
      wordGreedyColour names edges ((name, register) :: colouring)

/-! CakeML supplies preference edges from moves to the colouring algorithm so
    that a move can often be made register-to-register without an extra copy.
    A preference is only considered when its endpoint has already been
    coloured; the ordinary candidate list remains the fallback. -/

def wordPreferenceRegisters (name : Nat) (preferences : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : List Nat :=
  match preferences with
  | [] => []
  | (left, right) :: preferences =>
      if left == name then
        match lookupNatInfo right colouring with
        | some register => register :: wordPreferenceRegisters name preferences colouring
        | none => wordPreferenceRegisters name preferences colouring
      else if right == name then
        match lookupNatInfo left colouring with
        | some register => register :: wordPreferenceRegisters name preferences colouring
        | none => wordPreferenceRegisters name preferences colouring
      else
        wordPreferenceRegisters name preferences colouring

def wordColourCandidatesWithPreferences (name : Nat)
    (preferences : List (Nat × Nat)) (colouring : NatInfoMap Nat) : List Nat :=
  wordPreferenceRegisters name preferences colouring ++ wordColourCandidates name

def wordGreedyColourWithPreferences (names : List Nat)
    (edges preferences : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : Option (NatInfoMap Nat) :=
  match names with
  | [] => some colouring
  | name :: names =>
      let neighbours := wordNeighbours name edges
      let forbidden := wordUsedRegisters neighbours colouring
      match wordFirstAvailable
          (wordColourCandidatesWithPreferences name preferences colouring)
          forbidden with
      | none => none
      | some register =>
          wordGreedyColourWithPreferences names edges preferences
            ((name, register) :: colouring)

def wordColouringUsesAllocatable (names : List Nat)
    (colouring : NatInfoMap Nat) : Bool :=
  match names with
  | [] => true
  | name :: names =>
      match lookupNatInfo name colouring with
      | some register =>
          wordRegisterIsAllocatable register &&
            wordColouringUsesAllocatable names colouring
      | none => false

def wordColouringRespectsClashes (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : Bool :=
  match edges with
  | [] => true
  | (left, right) :: edges =>
      match lookupNatInfo left colouring, lookupNatInfo right colouring with
      | some leftRegister, some rightRegister =>
          leftRegister != rightRegister &&
            wordColouringRespectsClashes edges colouring
      | _, _ => false

def wordAllocateVarsWithClashes (slots : List Nat)
    (edges : List (Nat × Nat)) : Option (NatInfoMap Nat) :=
  let names := slots.eraseDups
  match wordGreedyColour names edges [] with
  | none => none
  | some colouring =>
      if wordColouringUsesAllocatable names colouring &&
          wordColouringRespectsClashes edges colouring then
        some colouring
      else none

def wordAllocateContextWithClashes (slots : List Nat)
    (edges : List (Nat × Nat)) : Option WordContext :=
  (wordAllocateVarsWithClashes slots edges).map (fun vars => { vars := vars })

def wordAllocateVarsWithClashesAndPreferences (slots : List Nat)
    (edges preferences : List (Nat × Nat)) : Option (NatInfoMap Nat) :=
  let names := slots.eraseDups
  match wordGreedyColourWithPreferences names edges preferences [] with
  | none => none
  | some colouring =>
      if wordColouringUsesAllocatable names colouring &&
          wordColouringRespectsClashes edges colouring then
        some colouring
      else none

def wordAllocateContextWithClashesAndPreferences (slots : List Nat)
    (edges preferences : List (Nat × Nat)) : Option WordContext :=
  (wordAllocateVarsWithClashesAndPreferences slots edges preferences).map
    (fun vars => { vars := vars })

/-! Straight-line liveness and clash construction for the current Word
instruction fragment.  The analysis walks backwards, keeping values live
after each instruction and adding an edge from every written variable to the
values that remain live. -/

def wordInstReadVars : WordInst → List Nat
  | .arith operation =>
      match operation with
      | .longMul _ _ sourceLeft sourceRight => [sourceLeft, sourceRight]
      | .longDiv _ _ sourceLeft sourceRight quotient =>
          [sourceLeft, sourceRight, quotient]
      | .addCarry _ _ sourceLeft sourceRight carryIn =>
          [sourceLeft, sourceRight, carryIn]
      | .div _ dividend divisor => [dividend, divisor]
  | .mem operator destination address =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [address]
      | .store | .store8 | .store16 | .store32 => [destination, address]

def wordInstWriteVars : WordInst → List Nat
  | .arith operation =>
      match operation with
      | .longMul destinationLeft destinationRight _ _ =>
          [destinationLeft, destinationRight]
      | .longDiv destinationLeft destinationRight _ _ _ =>
          [destinationLeft, destinationRight]
      | .addCarry destination resultCarry _ _ _ =>
          [destination, resultCarry]
      | .div destination _ _ => [destination]
  | .mem operator destination _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [destination]
      | .store | .store8 | .store16 | .store32 => []

def wordInstVars (instruction : WordInst) : List Nat :=
  wordInstReadVars instruction ++ wordInstWriteVars instruction

/-! RISC-V has additional forced clashes for multi-result arithmetic.  The
    high half of `LongMul` is written before the low half, so its first
    destination must not reuse either source.  The carry sequence similarly
    reads both addends after writing the sum destination; the two result
    destinations must also remain distinct.  These edges are part of the
    allocator contract, rather than an instruction-selection afterthought. -/

def wordInstForcedClashes : WordInst → List (Nat × Nat)
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      [(destinationLeft, destinationRight),
        (destinationLeft, sourceLeft), (destinationLeft, sourceRight)]
  | .arith (.addCarry destination resultCarry sourceLeft sourceRight _) =>
      [(destination, resultCarry),
        (destination, sourceLeft), (destination, sourceRight)]
  | _ => []

def wordClashPairs (writes live : List Nat) : List (Nat × Nat) :=
  writes.flatMap (fun write =>
    (live.filter (fun name => name != write)).map (fun name => (write, name)))

def wordPairwiseClashes : List Nat → List (Nat × Nat)
  | [] => []
  | name :: names =>
      (names.map (fun other => (name, other))) ++
        wordPairwiseClashes names

def wordInstLiveBefore (instruction : WordInst) (liveAfter : List Nat) : List Nat :=
  wordInstReadVars instruction ++
    liveAfter.filter (fun name => name ∉ wordInstWriteVars instruction)

def wordInstClashes (instruction : WordInst) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  wordInstForcedClashes instruction ++
    wordPairwiseClashes (wordInstWriteVars instruction) ++
    wordClashPairs (wordInstWriteVars instruction) liveAfter

def wordLinearClashAnalysis : List WordInst → List Nat →
    List Nat × List (Nat × Nat)
  | [], liveOut => (liveOut, [])
  | instruction :: instructions, liveOut =>
      let (liveAfter, edges) := wordLinearClashAnalysis instructions liveOut
      (wordInstLiveBefore instruction liveAfter,
        wordInstClashes instruction liveAfter ++ edges)

def wordLinearVariables (instructions : List WordInst) : List Nat :=
  instructions.flatMap wordInstVars

def wordAllocateLinearInstructions (instructions : List WordInst) :
    Option WordContext :=
  let (liveIn, edges) := wordLinearClashAnalysis instructions []
  wordAllocateContextWithClashes
    (wordLinearVariables instructions ++ liveIn) edges

/-! Word SSA renaming.  Each write receives a fresh virtual name; reads use the
latest name for their source variable.  As in CakeML's `next_var_rename`,
fresh names advance by four so the low two bits continue to identify physical,
allocatable-temporary, and stack-temporary names.  The implementation mirrors
the single-block part of `ssa_cc_trans_inst`, extends it with branch
reconciliation, and carries loop entry/exit frames for back-edge moves. -/

structure WordSsaState where
  current : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordSsaRead (state : WordSsaState) (name : Nat) : Nat :=
  match lookupNatInfo name state.current with
  | some value => value
  | none => name

def wordSsaReadCutsets (state : WordSsaState)
    (cutsets : List Nat × List Nat) : List Nat × List Nat :=
  (cutsets.1.map (wordSsaRead state), cutsets.2.map (wordSsaRead state))

def wordSsaFresh (state : WordSsaState) (name : Nat) : WordSsaState × Nat :=
  ({ current := (name, state.next) ::
        state.current.filter (fun entry => entry.1 != name),
      next := state.next + 4 },
    state.next)

theorem wordSsaFresh_next (state : WordSsaState) (name : Nat) :
    (wordSsaFresh state name).1.next = state.next + 4 := by
  rfl

theorem wordSsaFresh_preserves_residue (state : WordSsaState) (name : Nat)
    (residue : Nat) (hresidue : state.next % 4 = residue) :
    (wordSsaFresh state name).1.next % 4 = residue := by
  simp [wordSsaFresh, hresidue]

def wordSsaFreshList (state : WordSsaState) : List Nat →
    WordSsaState × List Nat
  | [] => (state, [])
  | name :: names =>
      let (state, freshName) := wordSsaFresh state name
      let (state, freshNames) := wordSsaFreshList state names
      (state, freshName :: freshNames)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaRenameReturns (state : WordSsaState) :
    Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat) →
      WordSsaState × Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat)
  | none => (state, none)
  | some (destinations, cutsets, returnCode, returnLabel, entryLabel) =>
      let cutsets := wordSsaReadCutsets state cutsets
      let (state, destinations) := wordSsaFreshList state destinations
      (state, some (destinations, cutsets, returnCode, returnLabel, entryLabel))

def wordSsaForceRename : List (Nat × Nat) → WordSsaState → WordSsaState
  | [], state => state
  | (source, destination) :: renamings, state =>
      wordSsaForceRename renamings
        { state with current := (source, destination) ::
            state.current.filter (fun entry => entry.1 != source) }
termination_by renamings => sizeOf renamings
decreasing_by all_goals decreasing_trivial

/-! Refresh a cut set while retaining the source-to-current mapping used by
    the surrounding SSA block.  CakeML uses this helper around ABI-sensitive
    operations such as FFI: every live name receives a fresh SSA version, and
    the generated Move makes that refresh explicit in the Word program. -/
def wordSsaListNextVarRenameMove (state : WordSsaState) (next : Nat)
    (names : List Nat) : WordSsaState × Nat × WordProg α :=
  let sources := names.map (wordSsaRead state)
  let (state, destinations) := wordSsaFreshList { state with next := next } names
  (state, state.next, .move 0 (destinations.zip sources))

def wordSsaRenameMove (state : WordSsaState) (priority : Nat)
    (moves : List (Nat × Nat)) : WordSsaState × WordProg α :=
  let destinations := moves.map (fun move => move.1)
  let sources := moves.map (fun move => wordSsaRead state move.2)
  let (state, destinations) := wordSsaFreshList state destinations
  let force := (moves.zip destinations).filter (fun move =>
    move.1.1 ∉ moves.map (fun candidate => candidate.1)) |>.map
      (fun move => (move.1.2, move.2))
  (wordSsaForceRename force state, .move priority (destinations.zip sources))


def wordSsaRenameInst (state : WordSsaState) : WordInst → WordSsaState × WordInst
  | .arith operation =>
      match operation with
      | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let (state, freshLeft) := wordSsaFresh state destinationLeft
          let (state, freshRight) := wordSsaFresh state destinationRight
          (state, .arith (.longMul freshLeft freshRight
            sourceLeft sourceRight))
      | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let quotient := wordSsaRead state quotient
          let (state, freshLeft) := wordSsaFresh state destinationLeft
          let (state, freshRight) := wordSsaFresh state destinationRight
          (state, .arith (.longDiv freshLeft freshRight
            sourceLeft sourceRight quotient))
      | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let carryIn := wordSsaRead state carryIn
          let (state, freshDestination) := wordSsaFresh state destination
          let (state, freshCarry) := wordSsaFresh state resultCarry
          (state, .arith (.addCarry freshDestination freshCarry
            sourceLeft sourceRight carryIn))
      | .div destination dividend divisor =>
          let dividend := wordSsaRead state dividend
          let divisor := wordSsaRead state divisor
          let (state, freshDestination) := wordSsaFresh state destination
          (state, .arith (.div freshDestination dividend divisor))
  | .mem operator destination address =>
      let address := wordSsaRead state address
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          let (state, freshDestination) := wordSsaFresh state destination
          (state, .mem operator freshDestination address)
      | .store | .store8 | .store16 | .store32 =>
          (state, .mem operator (wordSsaRead state destination) address)

def wordSsaRenameLinear (state : WordSsaState) : List WordInst →
    WordSsaState × List WordInst
  | [] => (state, [])
  | instruction :: instructions =>
      let (state, instruction) := wordSsaRenameInst state instruction
      let (state, instructions) := wordSsaRenameLinear state instructions
      (state, instruction :: instructions)

def wordAllocateSsaLinear (state : WordSsaState) (instructions : List WordInst) :
    Option (WordSsaState × List WordInst × WordContext) :=
  let (state, instructions) := wordSsaRenameLinear state instructions
  (wordAllocateLinearInstructions instructions).map
    (fun context => (state, instructions, context))

/-! Branch-aware SSA renaming for the Word program fragment.  A conditional
    starts both branches from the same incoming map, but gives the second
    branch the first branch's fresh-name counter.  Variables whose branch
    versions differ are reconciled with explicit copy assignments after each
    branch.  Those copies are ordinary Word assignments, so the result stays
    inside the existing IR and can be analysed by the allocator. -/

def wordSsaRenameExp (state : WordSsaState) : WordExp α → WordExp α
  | .const value => .const value
  | .var name => .var (wordSsaRead state name)
  | .lookup store => .lookup store
  | .load address => .load (wordSsaRenameExp state address)
  | .op operator arguments =>
      .op operator (arguments.map (wordSsaRenameExp state))
  | .shift operator left right =>
      .shift operator (wordSsaRenameExp state left) (wordSsaRenameExp state right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordSsaRenameRegImm (state : WordSsaState) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (wordSsaRead state name)

def wordSsaSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def wordSsaKeys (state : WordSsaState) : List Nat :=
  state.current.map (fun entry => entry.1)

def wordSsaBranchNames (base left right : WordSsaState) : List Nat :=
  (wordSsaKeys base ++ wordSsaKeys left ++ wordSsaKeys right).eraseDups

def wordSsaReconcile : List Nat → WordSsaState → WordSsaState → Nat →
    WordSsaState × WordProg α × WordProg α
  | [], _left, _right, next => ({ current := [], next := next }, .skip, .skip)
  | name :: names, left, right, next =>
      let leftName := wordSsaRead left name
      let rightName := wordSsaRead right name
      if leftName = rightName then
        let (merged, leftMoves, rightMoves) :=
          wordSsaReconcile names left right next
        ({ current := (name, leftName) :: merged.current, next := merged.next },
          leftMoves, rightMoves)
      else
        let leftMove := .assign next (.var leftName)
        let rightMove := .assign next (.var rightName)
        let (merged, leftMoves, rightMoves) :=
          wordSsaReconcile names left right (next + 4)
        ({ current := (name, next) :: merged.current, next := merged.next },
          wordSsaSeq leftMove leftMoves, wordSsaSeq rightMove rightMoves)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

structure WordSsaLoopFrame where
  entry : WordSsaState
  exit : WordSsaState
  entryNames : List Nat
  exitNames : List Nat

def wordSsaRestrict (state : WordSsaState) (names : List Nat) : WordSsaState :=
  { state with current := state.current.filter (fun entry => entry.1 ∈ names) }

def wordSsaReconcileTo (source target : WordSsaState) : List Nat →
    WordProg α
  | [] => .skip
  | name :: names =>
      let move := if wordSsaRead source name = wordSsaRead target name then
        (.skip : WordProg α)
      else
        .assign (wordSsaRead target name) (.var (wordSsaRead source name))
      wordSsaSeq move (wordSsaReconcileTo source target names)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaRefreshList (state : WordSsaState) : List Nat →
    WordSsaState × WordProg α
  | [] => (state, .skip)
  | name :: names =>
      let oldName := wordSsaRead state name
      let hadName := (lookupNatInfo name state.current).isSome
      let (state, freshName) := wordSsaFresh state name
      let (state, moves) := wordSsaRefreshList state names
      let move := if hadName then
        (.assign freshName (.var oldName) : WordProg α)
      else
        .skip
      (state, wordSsaSeq move moves)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaFindLoopFrame : Nat → List WordSsaLoopFrame →
    Option WordSsaLoopFrame
  | _, [] => none
  | 0, frame :: _ => some frame
  | label, _ :: frames => wordSsaFindLoopFrame (label - 1) frames

mutual
  def wordSsaRenameCallHandler (frames : List WordSsaLoopFrame)
      (incoming normalState : WordSsaState) (exception : Nat)
      : WordProg α → WordSsaState × Nat × WordProg α
    | body =>
        let handlerSeed := { incoming with next := normalState.next }
        let (handlerSeed, exceptionName) := wordSsaFresh handlerSeed exception
        let (handlerState, body) :=
          wordSsaRenameProgramWithLoops frames handlerSeed body
        let moves := wordSsaReconcileTo handlerState normalState
          (wordSsaKeys normalState)
        (handlerState, exceptionName, wordSsaSeq body moves)
  termination_by body => sizeOf body + 1
  decreasing_by all_goals decreasing_trivial

  def wordSsaRenameProgramWithLoops (frames : List WordSsaLoopFrame)
      (state : WordSsaState) : WordProg α → WordSsaState × WordProg α
    | .skip => (state, .skip)
    | .move priority moves =>
        wordSsaRenameMove state priority moves
    | .assign name value =>
        let value := wordSsaRenameExp state value
        let (state, freshName) := wordSsaFresh state name
        (state, .assign freshName value)
    | .inst instruction =>
        let (state, instruction) := wordSsaRenameInst state instruction
        (state, .inst instruction)
    | .get destination store =>
        let (state, destination) := wordSsaFresh state destination
        (state, .get destination store)
    | .seq first second =>
        let (state, first) := wordSsaRenameProgramWithLoops frames state first
        let (state, second) := wordSsaRenameProgramWithLoops frames state second
        (state, .seq first second)
    | .store address value =>
        (state, .store (wordSsaRenameExp state address) (wordSsaRead state value))
    | .set store value =>
        (state, .set store (wordSsaRenameExp state value))
    | .raise exception =>
        (state, .raise (wordSsaRead state exception))
    | .return label values =>
        (state, .return label (values.map (wordSsaRead state)))
    | .tick => (state, .tick)
    | .break label =>
        match wordSsaFindLoopFrame label frames with
        | none => (state, .break label)
        | some frame =>
            (state, wordSsaSeq
              (wordSsaReconcileTo state frame.exit frame.exitNames)
              (.break label))
    | .continue label =>
        match wordSsaFindLoopFrame label frames with
        | none => (state, .continue label)
        | some frame =>
            (state, wordSsaSeq
              (wordSsaReconcileTo state frame.entry frame.entryNames)
              (.continue label))
    | .locValue destination source =>
        let source := wordSsaRead state source
        let (state, destination) := wordSsaFresh state destination
        (state, .locValue destination source)
    | .ffi function configuration configurationLength array arrayLength live =>
        let names := (live.1 ++ live.2).eraseDups
        let (stackState, stackNext, stackMove) :=
          wordSsaListNextVarRenameMove state (state.next + 2) names
        let stackLive := wordSsaReadCutsets stackState live
        let configuration := wordSsaRead stackState configuration
        let configurationLength := wordSsaRead stackState configurationLength
        let array := wordSsaRead stackState array
        let arrayLength := wordSsaRead stackState arrayLength
        let cutState := wordSsaRestrict stackState names
        let (state, _, restoreMove) :=
          wordSsaListNextVarRenameMove cutState (stackNext + 2) names
        (state, wordSsaSeq stackMove
          (wordSsaSeq (.move 0
            [(2, configuration), (4, configurationLength),
             (6, array), (8, arrayLength)])
            (wordSsaSeq (.ffi function 2 4 6 8 stackLive) restoreMove)))
    | .shareInst operator name address =>
        let address := wordSsaRenameExp state address
        match operator with
        | .load | .load8 | .load16 | .load32 =>
            let (state, name) := wordSsaFresh state name
            (state, .shareInst operator name address)
        | .store | .store8 | .store16 | .store32 =>
            (state, .shareInst operator (wordSsaRead state name) address)
    | .call returns target arguments none =>
        let arguments := arguments.map (wordSsaRead state)
        let (state, returns) := wordSsaRenameReturns state returns
        (state, .call returns target arguments none)
    | .call returns target arguments (some (exception, body, handlerLabel, entryLabel)) =>
        let incoming := state
        let arguments := arguments.map (wordSsaRead state)
        let (normalState, returns) := wordSsaRenameReturns state returns
        let (handlerState, exception, body) :=
          wordSsaRenameCallHandler frames incoming normalState exception body
        ({ normalState with next := handlerState.next },
          .call returns target arguments (some (exception, body, handlerLabel, entryLabel)))
    | .alloc destination cutsets =>
        let cutsets := wordSsaReadCutsets state cutsets
        let (state, destination) := wordSsaFresh state destination
        (state, .alloc destination cutsets)
    | .storeConsts source bitmap codeLength dataLength constants =>
        (state, .storeConsts (wordSsaRead state source)
          (wordSsaRead state bitmap) (wordSsaRead state codeLength)
          (wordSsaRead state dataLength) constants)
    | .opCurrHeap operator destination source =>
        let source := wordSsaRead state source
        let (state, destination) := wordSsaFresh state destination
        (state, .opCurrHeap operator destination source)
    | .install codeBuffer codeLength dataBuffer dataLength cutsets =>
        let cutsets := wordSsaReadCutsets state cutsets
        let codeBuffer := wordSsaRead state codeBuffer
        let codeLength := wordSsaRead state codeLength
        let dataBuffer := wordSsaRead state dataBuffer
        let dataLength := wordSsaRead state dataLength
        (state, .install codeBuffer codeLength dataBuffer dataLength cutsets)
    | .codeBufferWrite address value =>
        (state, .codeBufferWrite (wordSsaRead state address)
          (wordSsaRead state value))
    | .dataBufferWrite address value =>
        (state, .dataBufferWrite (wordSsaRead state address)
          (wordSsaRead state value))
    | .loop liveIn body liveOut =>
        let names := (liveIn ++ liveOut).eraseDups
        let (setupState, setup) := wordSsaRefreshList state names
        let entryState := wordSsaRestrict setupState liveIn
        let exitState := wordSsaRestrict setupState liveOut
        let frame := WordSsaLoopFrame.mk entryState exitState
          liveIn.eraseDups liveOut.eraseDups
        let (bodyState, body) :=
          wordSsaRenameProgramWithLoops (frame :: frames) entryState body
        let backMoves := wordSsaReconcileTo bodyState setupState liveIn.eraseDups
        let body := wordSsaSeq body backMoves
        let program := .loop (liveIn.map (wordSsaRead setupState)) body
          (liveOut.map (wordSsaRead setupState))
        (exitState, wordSsaSeq setup program)
    | .mustTerminate body =>
        let (state, body) := wordSsaRenameProgramWithLoops frames state body
        (state, .mustTerminate body)
    | .ite operator condition right thenBranch elseBranch =>
        let right := wordSsaRenameRegImm state right
        let (thenState, thenBranch) :=
          wordSsaRenameProgramWithLoops frames state thenBranch
        let elseInput := { state with next := thenState.next }
        let (elseState, elseBranch) :=
          wordSsaRenameProgramWithLoops frames elseInput elseBranch
        let names := wordSsaBranchNames state thenState elseState
        let (merged, thenMoves, elseMoves) :=
          wordSsaReconcile names thenState elseState elseState.next
        ({ current := merged.current, next := merged.next },
          .ite operator (wordSsaRead state condition) right
            (wordSsaSeq thenBranch thenMoves)
            (wordSsaSeq elseBranch elseMoves))
  termination_by program => sizeOf program
  decreasing_by all_goals decreasing_trivial
end
def wordSsaRenameProgram (state : WordSsaState) (program : WordProg α) :
    WordSsaState × WordProg α :=
  wordSsaRenameProgramWithLoops [] state program

theorem wordSsaRenameProgram_ite :
    wordSsaRenameProgram ({ current := [], next := 10 } : WordSsaState)
        (.ite .equal 0 (.reg 0)
          (.assign 1 (.var 0)) (.assign 1 (.var 0)) : WordProg α) =
      ({ current := [(1, 18)], next := 22 },
        .ite .equal 0 (.reg 0)
          (.seq (.assign 10 (.var 0)) (.assign 18 (.var 10)))
          (.seq (.assign 14 (.var 0)) (.assign 18 (.var 14)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp, wordSsaRenameRegImm,
    wordSsaRead, wordSsaFresh, wordSsaBranchNames, wordSsaKeys,
    wordSsaReconcile, wordSsaSeq, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, lookupNatInfo]

/-! Program-level variable collection and liveness.  Sequencing and branch
    paths use backwards transfers; loop entry/exit sets remain conservative
    until the loop SSA reconciliation and spill contracts are ported. -/

def wordExpReadVars : WordExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => wordExpReadVars address
  | .op _ arguments => arguments.flatMap wordExpReadVars
  | .shift _ left right => wordExpReadVars left ++ wordExpReadVars right

def wordProgReadVars : WordProg α → List Nat
  | .skip => []
  | .move _ moves => moves.map (fun move => move.2)
  | .assign _ value => wordExpReadVars value
  | .inst instruction => wordInstReadVars instruction
  | .get _ _ => []
  | .store address value => wordExpReadVars address ++ [value]
  | .set _ value => wordExpReadVars value
  | .seq first second => wordProgReadVars first ++ wordProgReadVars second
  | .ite _ condition right thenBranch elseBranch =>
      [condition] ++ (match right with | .reg name => [name] | .imm _ => []) ++
        wordProgReadVars thenBranch ++ wordProgReadVars elseBranch
  | .loop liveIn body liveOut =>
      liveIn ++ wordProgReadVars body ++ liveOut
  | .mustTerminate body => wordProgReadVars body
  | .break _ | .continue _ => []
  | .raise exception => [exception]
  | .return _ values => values
  | .tick => []
  | .locValue _ source => [source]
  | .call returns _ arguments handler =>
      arguments ++ (match returns with
        | none => []
        | some (_, cutsets, returnCode, _, _) =>
            cutsets.1 ++ cutsets.2 ++ wordProgReadVars returnCode) ++
        (match handler with
        | none => []
        | some (_, body, _, _) => wordProgReadVars body)
  | .alloc destination (nonGc, gc) =>
      destination :: (nonGc ++ gc)
  | .storeConsts source bitmap codeLength dataLength _ =>
      [source, bitmap, codeLength, dataLength]
  | .opCurrHeap _ _ source => [source]
  | .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc) =>
      [codeBuffer, codeLength, dataBuffer, dataLength] ++ nonGc ++ gc
  | .codeBufferWrite address value => [address, value]
  | .dataBufferWrite address value => [address, value]
  | .ffi _ configuration configurationLength array arrayLength live =>
      [configuration, configurationLength, array, arrayLength] ++
        live.1 ++ live.2
  | .shareInst operator name address =>
      (match operator with
      | .load | .load8 | .load16 | .load32 => []
      | .store | .store8 | .store16 | .store32 => [name]) ++
        wordExpReadVars address

def wordProgWriteVars : WordProg α → List Nat
  | .skip | .get _ _ | .store _ _ | .set _ _ | .break _ | .continue _ | .raise _
  | .return _ _ | .tick => []
  | .move _ moves => moves.map (fun move => move.1)
  | .assign name _ => [name]
  | .inst instruction => wordInstWriteVars instruction
  | .seq first second => wordProgWriteVars first ++ wordProgWriteVars second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgWriteVars thenBranch ++ wordProgWriteVars elseBranch
  | .loop _ body _ => wordProgWriteVars body
  | .mustTerminate body => wordProgWriteVars body
  | .locValue destination _ => [destination]
  | .call returns _ _ handler =>
      (match returns with
      | none => []
      | some (values, _, returnCode, _, _) => values ++ wordProgWriteVars returnCode) ++
      (match handler with
      | none => []
        | some (exception, body, _, _) => exception :: wordProgWriteVars body)
  | .alloc destination _ => [destination]
  | .storeConsts source bitmap codeLength dataLength _ =>
      [source, bitmap, codeLength, dataLength]
  | .opCurrHeap _ destination _ => [destination]
  | .install codeBuffer _ _ _ _ => [codeBuffer]
  | .codeBufferWrite _ _ | .dataBufferWrite _ _ => []
  | .ffi _ _ _ _ _ _ => []
  | .shareInst operator name _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [name]
      | .store | .store8 | .store16 | .store32 => []

def wordProgVariables (program : WordProg α) : List Nat :=
  wordProgReadVars program ++ wordProgWriteVars program

/-! Physical Word names denote architectural registers directly.  They can
    occur in the body independently of the formal-parameter list, notably as
    the ABI operands of an FFI instruction, so the spill allocator must keep
    every such name fixed rather than recolouring it. -/

def wordPhysicalFixedSources (parameters : List Nat) (program : WordProg α) :
    List Nat :=
  parameters ++ (wordProgVariables program).filter (fun name => name % 2 == 0)

/-! Preference edges corresponding to CakeML's `get_prefs`.  Both explicit
    CakeML moves and the compact copy forms retained by the initial Word IR
    contribute preferences. -/

def wordProgPreferenceEdges : WordProg α → List (Nat × Nat)
  | .move _ moves => moves
  | .assign destination (.var source) => [(destination, source)]
  | .locValue destination source => [(destination, source)]
  | .seq first second =>
      wordProgPreferenceEdges first ++ wordProgPreferenceEdges second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgPreferenceEdges thenBranch ++ wordProgPreferenceEdges elseBranch
  | .loop _ body _ => wordProgPreferenceEdges body
  | .mustTerminate body => wordProgPreferenceEdges body
  | .call _ _ _ none => []
  | .call _ _ _ (some (_, body, _, _)) => wordProgPreferenceEdges body
  | _ => []

/-! CakeML's `full_ssa_cc_trans` starts a function by giving each formal
    parameter a fresh SSA name.  The fresh names are chosen above the source
    program's variable range; the corresponding ABI moves are materialised at
    the Word-to-Stack boundary.  Keeping this setup separate from the body
    renamer lets the function metadata retain its source-level parameter
    names. -/

def wordListMaximum : List Nat → Nat
  | [] => 0
  | value :: values => max value (wordListMaximum values)
termination_by values => sizeOf values
decreasing_by all_goals decreasing_trivial

def wordSsaLimitVar (parameters : List Nat) (program : WordProg α) : Nat :=
  let maximum := wordListMaximum (parameters ++ wordProgVariables program)
  maximum + (4 - maximum % 4) + 1

def wordSsaSetupParameters (parameters : List Nat) (program : WordProg α) :
    WordSsaState × List Nat :=
  wordSsaFreshList
    { current := [], next := wordSsaLimitVar parameters program } parameters

def wordSsaRenameFunction (parameters : List Nat) (program : WordProg α) :
    WordSsaState × List Nat × WordProg α :=
  let (state, renamedParameters) := wordSsaSetupParameters parameters program
  let (state, program) := wordSsaRenameProgram state program
  (state, renamedParameters, program)

/-! The CakeML `full_ssa_cc_trans` result starts with the moves which copy
    source formal parameters into their fresh SSA names.  The allocator needs
    these moves in its input: they are part of the function, not merely an
    implementation detail of the later Word-to-Stack entry lowering. -/

def wordSsaEntryMove (parameters renamedParameters : List Nat) :
    WordProg α :=
  .move 1 (renamedParameters.zip parameters)

def wordSsaRenameFunctionWithEntry (parameters : List Nat) (program : WordProg α) :
    WordSsaState × List Nat × WordProg α :=
  let (state, renamedParameters, program) :=
    wordSsaRenameFunction parameters program
  (state, renamedParameters, .seq (wordSsaEntryMove parameters renamedParameters) program)

def wordProgLiveBefore (program : WordProg α) (liveAfter : List Nat) : List Nat :=
  wordProgReadVars program ++
    liveAfter.filter (fun name => name ∉ wordProgWriteVars program)

def wordListUnion (left right : List Nat) : List Nat :=
  (left ++ right).eraseDups

def wordProgAtomicClashes (program : WordProg α) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  match program with
  | .inst instruction =>
      wordInstForcedClashes instruction ++
        wordClashPairs (wordProgWriteVars program) liveAfter
  | _ => wordClashPairs (wordProgWriteVars program) liveAfter

def wordProgClashAnalysis : WordProg α → List Nat →
    List Nat × List (Nat × Nat)
  | .seq first second, liveOut =>
      let (liveMiddle, secondEdges) := wordProgClashAnalysis second liveOut
      let (liveIn, firstEdges) := wordProgClashAnalysis first liveMiddle
      (liveIn, firstEdges ++ secondEdges)
  | .ite _ condition right thenBranch elseBranch, liveOut =>
      let (thenLive, thenEdges) := wordProgClashAnalysis thenBranch liveOut
      let (elseLive, elseEdges) := wordProgClashAnalysis elseBranch liveOut
      let conditionLive := condition :: match right with
        | .reg name => [name]
        | .imm _ => []
      (wordListUnion conditionLive (wordListUnion thenLive elseLive),
        thenEdges ++ elseEdges)
  | .loop liveIn body liveOut, liveAfter =>
      let (bodyLive, bodyEdges) :=
        wordProgClashAnalysis body (wordListUnion liveIn (liveOut ++ liveAfter))
      (wordListUnion liveIn bodyLive, bodyEdges)
  | .call returns target arguments (some (exception, body, _, _)), liveAfter =>
      let (handlerLive, handlerEdges) :=
        wordProgClashAnalysis body liveAfter
      let callProgram : WordProg α :=
        .call returns target arguments (some (exception, body, 0, 0))
      let handlerEntryEdges :=
        wordClashPairs [exception] (handlerLive ++ liveAfter)
      (wordListUnion (exception :: handlerLive)
          (wordProgLiveBefore callProgram liveAfter),
        handlerEntryEdges ++ handlerEdges ++
          wordProgAtomicClashes callProgram liveAfter)
  | program, liveOut =>
      (wordProgLiveBefore program liveOut, wordProgAtomicClashes program liveOut)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | simp_wf

/-! A CakeML-shaped clash-tree boundary for the RISC-V Word fragment.

    CakeML's `word_alloc` does not allocate from a flat list of pairwise
    clashes.  It first builds a tree whose `Delta` nodes describe writes and
    reads, whose `Branch` nodes preserve path-local live sets, and whose `Set`
    nodes model loop cut sets and call boundaries.  The earlier analysis above
    remains useful as a compact executable allocator input; this tree is the
    faithful structural interface that later colouring and spill proofs can
    consume.  The constructors absent from this RISC-V Word IR are naturally
    absent here as well. -/

inductive WordClashTree where
  | delta (writes reads : List Nat)
  | seq (first second : WordClashTree)
  | branch (live : Option (List Nat))
      (thenBranch elseBranch : WordClashTree)
  | set (names : List Nat)
  deriving Repr

def wordClashTreeFindLoopFrame : Nat → List (List Nat × List Nat) →
    Option (List Nat × List Nat)
  | _, [] => none
  | 0, frame :: _ => some frame
  | label, _ :: frames => wordClashTreeFindLoopFrame (label - 1) frames

def wordClashTreeDeltaInst : WordInst → WordClashTree
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      .delta [destinationLeft, destinationRight] [sourceRight, sourceLeft]
  | .arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient) =>
      .delta [destinationLeft, destinationRight] [quotient, sourceRight, sourceLeft]
  | .arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn) =>
      .delta [destination, resultCarry] [carryIn, sourceRight, sourceLeft]
  | .arith (.div destination dividend divisor) =>
      .delta [destination] [divisor, dividend]
  | .mem .load destination address
  | .mem .load8 destination address
  | .mem .load16 destination address
  | .mem .load32 destination address =>
      .delta [destination] [address]
  | .mem .store source address
  | .mem .store8 source address
  | .mem .store16 source address
  | .mem .store32 source address =>
      .delta [] [source, address]

def wordClashTreeCallReads (returns : Option
    (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat))
    (arguments : List Nat) : List Nat :=
  arguments ++ match returns with
    | none => []
    | some (values, cutsets, returnCode, _, _) =>
        values ++ cutsets.1 ++ cutsets.2 ++ wordProgReadVars returnCode

def wordClashTreeCallWrites (returns : Option
    (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat)) : List Nat :=
  match returns with
  | none => []
  | some (values, _, _, _, _) => values

def wordClashTreeCallCutSet (returns : Option
    (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat)) : List Nat :=
  match returns with
  | none => []
  | some (_, cutsets, _, _, _) => cutsets.1 ++ cutsets.2

def wordClashTreeCallSet (left right : List Nat) : List Nat :=
  (left ++ right).eraseDups

/-! The allocator models a call as a cut-set boundary.  The exact return
    continuation and exceptional handler are included in the recursive clash
    structure, while the two cut sets establish the caller boundary. -/

def wordClashTree : WordProg α → List (List Nat × List Nat) → WordClashTree
  | .skip, _ => .delta [] []
  | .move _ moves, _ =>
      .delta (moves.map (fun move => move.1))
        (moves.map (fun move => move.2))
  | .assign name value, _ => .delta [name] (wordExpReadVars value)
  | .inst instruction, _ => wordClashTreeDeltaInst instruction
  | .get destination _, _ => .delta [destination] []
  | .store address value, _ => .delta [] (value :: wordExpReadVars address)
  | .set _ value, _ => .delta [] (wordExpReadVars value)
  | .seq first second, frames =>
      .seq (wordClashTree first frames) (wordClashTree second frames)
  | .ite _ condition right thenBranch elseBranch, frames =>
      let conditionReads := condition :: match right with
        | .reg name => [name]
        | .imm _ => []
      .seq (.delta [] conditionReads)
        (.branch none (wordClashTree thenBranch frames)
          (wordClashTree elseBranch frames))
  | .loop liveIn body liveOut, frames =>
      .seq (.set liveIn)
        (.seq (.set liveOut)
          (.seq (wordClashTree body ((liveIn, liveOut) :: frames))
            (.set liveIn)))
  | .mustTerminate body, frames => wordClashTree body frames
  | .break label, frames =>
      match wordClashTreeFindLoopFrame label frames with
      | some (_, exitNames) => .set exitNames
      | none => .set []
  | .continue label, frames =>
      match wordClashTreeFindLoopFrame label frames with
      | some (entryNames, _) => .set entryNames
      | none => .set []
  | .raise exception, _ => .delta [] [exception]
  | .return _ values, _ => .delta [] values
  | .tick, _ => .delta [] []
  | .locValue destination source, _ => .delta [destination] [source]
  | .call returns _ arguments none, frames =>
      match returns with
      | none => .set arguments.eraseDups
      | some (values, _, _returnCode, _, _) =>
          let cutSet := wordClashTreeCallCutSet returns
          let liveSet := wordClashTreeCallSet cutSet arguments
          let returnTree :=
            .seq (.set (wordClashTreeCallSet values cutSet))
              (wordClashTree _returnCode frames)
          .seq (.set liveSet) returnTree
  | .call returns _ arguments (some (exception, body, _, _)), frames =>
      let cutSet := wordClashTreeCallCutSet returns
      let liveSet := wordClashTreeCallSet cutSet arguments
      .branch (some liveSet)
        (match returns with
        | none => .set liveSet
        | some (values, _, _returnCode, _, _) =>
            .seq (.set (wordClashTreeCallSet values cutSet))
              (wordClashTree _returnCode frames))
        (.seq (.set (wordClashTreeCallSet [exception] cutSet))
          (wordClashTree body frames))
  | .alloc destination (nonGc, gc), _ =>
      .seq (.delta [] [destination])
        (.set (wordClashTreeCallSet nonGc gc))
  | .storeConsts source bitmap codeLength dataLength _, _ =>
      .delta [source, bitmap, codeLength, dataLength]
        [codeLength, dataLength]
  | .opCurrHeap _ destination source, _ => .delta [destination] [source]
  | .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc), _ =>
      .seq (.delta [] [dataLength, dataBuffer, codeLength, codeBuffer])
        (.seq (.set (wordClashTreeCallSet nonGc gc))
          (.delta [codeBuffer] []))
  | .codeBufferWrite address value, _ => .delta [] [address, value]
  | .dataBufferWrite address value, _ => .delta [] [address, value]
  | .ffi _ configuration configurationLength array arrayLength (nonGc, gc), _ =>
      .seq (.delta [] [configuration, configurationLength, array, arrayLength])
        (.set (wordClashTreeCallSet nonGc gc))
  | .shareInst operator name address, _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          .delta [name] (wordExpReadVars address)
      | .store | .store8 | .store16 | .store32 =>
          .delta [] (name :: wordExpReadVars address)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem wordClashTree_skip (frames : List (List Nat × List Nat)) :
    wordClashTree (.skip : WordProg α) frames = .delta [] [] := by
  simp [wordClashTree]

theorem wordClashTree_loop_break_continue :
    wordClashTree
        (.loop [1, 2]
          (.seq (.continue 0) (.break 0)) [3] : WordProg α) [] =
      .seq (.set [1, 2])
        (.seq (.set [3])
          (.seq
            (.seq (.set [1, 2]) (.set [3]))
            (.set [1, 2]))) := by
  simp [wordClashTree, wordClashTreeFindLoopFrame]

/-! Backward interpretation of a clash tree.  `Delta` contributes clashes
    between its writes and the values live after it; `Seq` feeds the live set
    produced by its suffix into its prefix; and `Branch` joins the live sets
    computed for both paths.  `Set` is a cut-set boundary supplied by the
    source allocator. -/

def wordClashTreeAnalyze : WordClashTree → List Nat →
    List Nat × List (Nat × Nat)
  | .delta writes reads, liveAfter =>
      (wordListUnion reads (liveAfter.filter (fun name => name ∉ writes)),
        wordClashPairs writes liveAfter)
  | .seq first second, liveAfter =>
      let (liveMiddle, secondEdges) := wordClashTreeAnalyze second liveAfter
      let (liveIn, firstEdges) := wordClashTreeAnalyze first liveMiddle
      (liveIn, firstEdges ++ secondEdges)
  | .branch branchLive thenBranch elseBranch, liveAfter =>
      let branchOut := match branchLive with
        | some names => names
        | none => liveAfter
      let (thenLive, thenEdges) := wordClashTreeAnalyze thenBranch branchOut
      let (elseLive, elseEdges) := wordClashTreeAnalyze elseBranch branchOut
      (wordListUnion branchOut (wordListUnion thenLive elseLive),
        thenEdges ++ elseEdges)
  | .set names, _ => (names, [])

def wordNumSetDelete : List Nat → List Nat → List Nat
  | [], live => live
  | name :: names, live =>
      wordNumSetDelete names (live.filter (fun other => other != name))

def wordCheckPartialColour (colour : Nat → Nat) : List Nat → List Nat →
    List Nat → Option (List Nat × List Nat)
  | [], live, flive => some (live, flive)
  | name :: names, live, flive =>
      if name ∈ live then
        wordCheckPartialColour colour names live flive
      else if colour name ∈ flive then
        none
      else
        wordCheckPartialColour colour names (name :: live)
          (colour name :: flive)

def wordCheckColour (colour : Nat → Nat) (names : List Nat) :
    Option (List Nat × List Nat) :=
  let coloured := names.map colour
  if coloured.Nodup then some (names, coloured) else none

def wordClashTreeCheck (colour : Nat → Nat) : WordClashTree →
    List Nat → List Nat → Option (List Nat × List Nat)
  | .delta writes reads, live, flive =>
      match wordCheckPartialColour colour writes live flive with
      | none => none
      | some _ =>
          wordCheckPartialColour colour reads
            (wordNumSetDelete writes live)
            (wordNumSetDelete (writes.map colour) flive)
  | .set names, _, _ => wordCheckColour colour names
  | .branch branchLive thenBranch elseBranch, live, flive =>
      match wordClashTreeCheck colour thenBranch live flive with
      | none => none
      | some (thenOut, fThenOut) =>
          match wordClashTreeCheck colour elseBranch live flive with
          | none => none
          | some (elseOut, _fElseOut) =>
              match branchLive with
              | none =>
                  wordCheckPartialColour colour
                    (elseOut.filter (fun name => name ∉ thenOut))
                    thenOut fThenOut
              | some names => wordCheckColour colour names
  | .seq first second, live, flive =>
      match wordClashTreeCheck colour second live flive with
      | none => none
      | some (secondOut, fSecondOut) =>
          wordClashTreeCheck colour first secondOut fSecondOut
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

theorem wordCheckPartialColour_sound (colour : Nat → Nat)
    (names live flive live' flive' : List Nat)
    (hlive : live.Nodup)
    (hflive : flive.Nodup)
    (himage : flive = live.map colour)
    (hcheck : wordCheckPartialColour colour names live flive =
      some (live', flive')) :
    live'.Nodup ∧ flive'.Nodup ∧ flive' = live'.map colour := by
  induction names generalizing live flive live' flive' with
  | nil =>
      simp [wordCheckPartialColour] at hcheck
      rcases hcheck with ⟨rfl, rfl⟩
      exact ⟨hlive, hflive, himage⟩
  | cons name names ih =>
      by_cases hname : name ∈ live
      · have hcheck' : wordCheckPartialColour colour names live flive =
            some (live', flive') := by
          simpa [wordCheckPartialColour, hname] using hcheck
        exact ih live flive live' flive' hlive hflive himage hcheck'
      · by_cases hcolour : colour name ∈ flive
        · simp [wordCheckPartialColour, hname, hcolour] at hcheck
        · have hcheck' :
              wordCheckPartialColour colour names (name :: live)
                (colour name :: flive) = some (live', flive') := by
            simpa [wordCheckPartialColour, hname, hcolour] using hcheck
          have hlive' : (name :: live).Nodup := by
            simp [List.nodup_cons, hname, hlive]
          have hflive' : (colour name :: flive).Nodup := by
            simp [List.nodup_cons, hcolour, hflive]
          have himage' : colour name :: flive = (name :: live).map colour := by
            simp [himage]
          exact ih (name :: live) (colour name :: flive) live' flive'
            hlive' hflive' himage' hcheck'

theorem wordCheckColour_sound (colour : Nat → Nat)
    (names names' coloured' : List Nat)
    (hcheck : wordCheckColour colour names = some (names', coloured')) :
    names' = names ∧ coloured' = names.map colour ∧
      coloured'.Nodup := by
  simp [wordCheckColour] at hcheck
  rcases hcheck with ⟨hcoloured, hnames, hmap⟩
  exact ⟨hnames.symm, hmap.symm, by simpa [hmap] using hcoloured⟩

theorem wordMapFilterDelete (colour : Nat → Nat) (name : Nat)
    (live : List Nat) (hinjective : Function.Injective colour) :
    (live.filter (fun other => other != name)).map colour =
      (live.map colour).filter (fun other => other != colour name) := by
  induction live with
  | nil => simp
  | cons head tail ih =>
      by_cases hhead : head = name
      · subst head
        simpa using ih
      · have hcolour : colour head ≠ colour name := by
          intro heq
          apply hhead
          exact hinjective heq
        simp [hhead, hcolour, ih]

theorem wordNumSetDelete_map (colour : Nat → Nat)
    (names live : List Nat) (hinjective : Function.Injective colour) :
    wordNumSetDelete (names.map colour) (live.map colour) =
      (wordNumSetDelete names live).map colour := by
  induction names generalizing live with
  | nil => rfl
  | cons name names ih =>
      simp only [List.map_cons, wordNumSetDelete]
      rw [← wordMapFilterDelete colour name live hinjective]
      rw [ih]

theorem wordNumSetDelete_nodup (names live : List Nat)
    (hlive : live.Nodup) :
    (wordNumSetDelete names live).Nodup := by
  induction names generalizing live with
  | nil => exact hlive
  | cons name names ih =>
      apply ih
      exact hlive.filter (fun other => other != name)

theorem wordMap_nodup_source (colour : Nat → Nat)
    (names : List Nat) (hcoloured : (names.map colour).Nodup) :
    names.Nodup := by
  induction names with
  | nil => simp
  | cons name names ih =>
      have hcoloured' := List.nodup_cons.mp hcoloured
      apply List.nodup_cons.mpr
      constructor
      · intro hname
        apply hcoloured'.1
        exact List.mem_map.mpr ⟨name, hname, rfl⟩
      · exact ih hcoloured'.2

theorem wordClashTreeCheck_sound (colour : Nat → Nat)
    (tree : WordClashTree) (live flive live' flive' : List Nat)
    (hinjective : Function.Injective colour)
    (hlive : live.Nodup)
    (hflive : flive.Nodup)
    (himage : flive = live.map colour)
    (hcheck : wordClashTreeCheck colour tree live flive =
      some (live', flive')) :
    live'.Nodup ∧ flive'.Nodup ∧ flive' = live'.map colour := by
  induction tree generalizing live flive live' flive' with
  | delta writes reads =>
      simp only [wordClashTreeCheck] at hcheck
      split at hcheck
      · contradiction
      · rename_i hpartial
        have hdeletedLive :
            (wordNumSetDelete writes live).Nodup :=
          wordNumSetDelete_nodup writes live hlive
        have hdeletedFlive :
            (wordNumSetDelete (writes.map colour) flive).Nodup := by
          rw [himage]
          exact wordNumSetDelete_nodup (writes.map colour)
            (live.map colour) (by simpa [himage] using hflive)
        have hdeletedImage :
            wordNumSetDelete (writes.map colour) flive =
              (wordNumSetDelete writes live).map colour := by
          simpa [himage] using
            (wordNumSetDelete_map colour writes live hinjective)
        have hreads :
            wordCheckPartialColour colour reads
              (wordNumSetDelete writes live)
              (wordNumSetDelete (writes.map colour) flive) =
              some (live', flive') := by
            simpa [hpartial] using hcheck
        exact wordCheckPartialColour_sound colour reads
          (wordNumSetDelete writes live)
          (wordNumSetDelete (writes.map colour) flive)
          live' flive' hdeletedLive hdeletedFlive hdeletedImage hreads
  | set names =>
      have hcheck' : wordCheckColour colour names =
          some (live', flive') := by
        simpa [wordClashTreeCheck] using hcheck
      have hcolour := wordCheckColour_sound colour names live' flive' hcheck'
      rcases hcolour with ⟨hnames, hmap, hcoloured⟩
      subst live'
      subst flive'
      exact ⟨wordMap_nodup_source colour names hcoloured, hcoloured, rfl⟩
  | branch branchLive thenBranch elseBranch ihThen ihElse =>
      cases hthen : wordClashTreeCheck colour thenBranch live flive with
      | none =>
          simp [wordClashTreeCheck, hthen] at hcheck
      | some thenResult =>
          cases helse : wordClashTreeCheck colour elseBranch live flive with
          | none =>
              simp [wordClashTreeCheck, hthen, helse] at hcheck
          | some elseResult =>
              cases thenResult with
              | mk thenOut fThenOut =>
                  cases elseResult with
                  | mk elseOut fElseOut =>
                      have hthen' :
                          thenOut.Nodup ∧ fThenOut.Nodup ∧
                            fThenOut = thenOut.map colour :=
                        ihThen live flive thenOut fThenOut
                          hlive hflive himage hthen
                      have helse' :
                          elseOut.Nodup ∧ fElseOut.Nodup ∧
                            fElseOut = elseOut.map colour :=
                        ihElse live flive elseOut fElseOut
                          hlive hflive himage helse
                      cases branchLive with
                      | none =>
                          have hfinal :
                              wordCheckPartialColour colour
                                (elseOut.filter
                                  (fun name => name ∉ thenOut))
                                thenOut fThenOut =
                                some (live', flive') := by
                            simpa only [wordClashTreeCheck, hthen, helse] using
                              hcheck
                          exact wordCheckPartialColour_sound colour
                            (elseOut.filter
                              (fun name => name ∉ thenOut))
                            thenOut fThenOut live' flive'
                            hthen'.1 hthen'.2.1 hthen'.2.2 hfinal
                      | some names =>
                          have hfinal : wordCheckColour colour names =
                              some (live', flive') := by
                            simpa only [wordClashTreeCheck, hthen, helse] using
                              hcheck
                          have hcolour := wordCheckColour_sound colour
                            names live' flive' hfinal
                          rcases hcolour with ⟨hnames, hmap, hcoloured⟩
                          subst live'
                          subst flive'
                          exact ⟨wordMap_nodup_source colour names hcoloured,
                            hcoloured, rfl⟩
  | seq first second ihFirst ihSecond =>
      cases hsecond : wordClashTreeCheck colour second live flive with
      | none =>
          simp [wordClashTreeCheck, hsecond] at hcheck
      | some secondResult =>
          cases secondResult with
          | mk secondOut fSecondOut =>
              have hsecond' :
                  secondOut.Nodup ∧ fSecondOut.Nodup ∧
                    fSecondOut = secondOut.map colour :=
                ihSecond live flive secondOut fSecondOut
                  hlive hflive himage hsecond
              have hfirst : wordClashTreeCheck colour first
                  secondOut fSecondOut = some (live', flive') := by
                simpa [wordClashTreeCheck, hsecond] using hcheck
              exact ihFirst secondOut fSecondOut live' flive'
                hsecond'.1 hsecond'.2.1 hsecond'.2.2 hfirst

def wordAllocateProgramWithClashTree (slots : List Nat)
    (program : WordProg α) : Option WordContext :=
  let (liveIn, edges) :=
    wordClashTreeAnalyze (wordClashTree program []) []
  wordAllocateContextWithClashes
    (slots ++ liveIn ++ wordProgVariables program) edges

theorem wordClashTreeAnalyze_assign (name source : Nat)
    (hneq : name ≠ source) :
    wordClashTreeAnalyze
        (wordClashTree (.assign name (.var source) : WordProg α) []) [source] =
      ([source], [(name, source)]) := by
  have hneq' : source ≠ name := Ne.symm hneq
  simp [wordClashTree, wordClashTreeAnalyze, wordExpReadVars,
    wordClashPairs, wordListUnion, hneq', List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

theorem wordClashTreeAnalyze_seq (first second : WordProg α)
    (liveAfter : List Nat) :
    (wordClashTreeAnalyze
      (wordClashTree (.seq first second : WordProg α) []) liveAfter) =
      (let (liveMiddle, secondEdges) :=
          wordClashTreeAnalyze (wordClashTree second []) liveAfter
       let (liveIn, firstEdges) :=
          wordClashTreeAnalyze (wordClashTree first []) liveMiddle
       (liveIn, firstEdges ++ secondEdges)) := by
  simp [wordClashTree, wordClashTreeAnalyze]

def wordAllocateProgramWithSlots (slots : List Nat) (program : WordProg α) :
    Option WordContext :=
  let (liveIn, edges) := wordProgClashAnalysis program []
  wordAllocateContextWithClashes
    (slots ++ wordProgVariables program ++ liveIn) edges

def wordAllocateProgram (program : WordProg α) : Option WordContext :=
  wordAllocateProgramWithSlots [] program

def wordAllocateProgramWithPreferences (slots : List Nat)
    (program : WordProg α) : Option WordContext :=
  let (liveIn, edges) := wordProgClashAnalysis program []
  wordAllocateContextWithClashesAndPreferences
    (slots ++ wordProgVariables program ++ liveIn) edges
    (wordProgPreferenceEdges program)

def wordAllocateSsaProgram (state : WordSsaState) (program : WordProg α) :
    Option (WordSsaState × WordProg α × WordContext) :=
  let (state, program) := wordSsaRenameProgram state program
  let (liveIn, edges) := wordProgClashAnalysis program []
  (wordAllocateContextWithClashes
      (wordProgVariables program ++ liveIn) edges).map
    (fun context => (state, program, context))

/-! Apply a completed colouring to the full current Word syntax.  Control
    labels and function labels are not virtual registers; every data-register
    position, including nested handlers and loop live sets, is transformed. -/

def wordApplyColourExp (colour : Nat → Nat) : WordExp α → WordExp α
  | .const value => .const value
  | .var name => .var (colour name)
  | .lookup store => .lookup store
  | .load address => .load (wordApplyColourExp colour address)
  | .op operator arguments =>
      .op operator (arguments.map (wordApplyColourExp colour))
  | .shift operator left right =>
      .shift operator (wordApplyColourExp colour left)
        (wordApplyColourExp colour right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordApplyColourRegImm (colour : Nat → Nat) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (colour name)

def wordApplyColourArith (colour : Nat → Nat) : WordArith → WordArith
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul (colour destinationLeft) (colour destinationRight)
        (colour sourceLeft) (colour sourceRight)
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv (colour destinationLeft) (colour destinationRight)
        (colour sourceLeft) (colour sourceRight) (colour quotient)
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      .addCarry (colour destination) (colour resultCarry)
        (colour sourceLeft) (colour sourceRight) (colour carryIn)
  | .div destination dividend divisor =>
      .div (colour destination) (colour dividend) (colour divisor)

def wordApplyColourInst (colour : Nat → Nat) : WordInst → WordInst
  | .arith operation => .arith (wordApplyColourArith colour operation)
  | .mem operator destination address =>
      .mem operator (colour destination) (colour address)

def wordApplyColour (colour : Nat → Nat) : WordProg α → WordProg α
  | .skip => .skip
  | .move priority moves =>
      .move priority (moves.map (fun move => (colour move.1, colour move.2)))
  | .assign name value =>
      .assign (colour name) (wordApplyColourExp colour value)
  | .inst instruction => .inst (wordApplyColourInst colour instruction)
  | .get destination store => .get (colour destination) store
  | .store address value =>
      .store (wordApplyColourExp colour address) (colour value)
  | .set store value => .set store (wordApplyColourExp colour value)
  | .seq first second =>
      .seq (wordApplyColour colour first) (wordApplyColour colour second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator (colour condition) (wordApplyColourRegImm colour right)
        (wordApplyColour colour thenBranch) (wordApplyColour colour elseBranch)
  | .loop liveIn body liveOut =>
      .loop (liveIn.map colour) (wordApplyColour colour body) (liveOut.map colour)
  | .mustTerminate body => .mustTerminate (wordApplyColour colour body)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise (colour exception)
  | .return label values => .return label (values.map colour)
  | .tick => .tick
  | .locValue destination source =>
      .locValue (colour destination) (colour source)
  | .call returns target arguments none =>
      .call (returns.map (fun (values, cutsets, returnCode, returnLabel, entryLabel) =>
        (values.map colour,
          (cutsets.1.map colour, cutsets.2.map colour),
          returnCode, returnLabel, entryLabel)))
        target (arguments.map colour)
        none
  | .call returns target arguments (some (exception, body, handlerLabel, entryLabel)) =>
      .call (returns.map (fun (values, cutsets, returnCode, returnLabel, entryLabel) =>
        (values.map colour,
          (cutsets.1.map colour, cutsets.2.map colour),
          returnCode, returnLabel, entryLabel)))
        target (arguments.map colour)
        (some (colour exception, wordApplyColour colour body,
          handlerLabel, entryLabel))
  | .alloc destination (nonGc, gc) =>
      .alloc (colour destination) (nonGc.map colour, gc.map colour)
  | .storeConsts source bitmap codeLength dataLength constants =>
      .storeConsts (colour source) (colour bitmap) (colour codeLength)
        (colour dataLength) constants
  | .opCurrHeap operator destination source =>
      .opCurrHeap operator (colour destination) (colour source)
  | .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc) =>
      .install (colour codeBuffer) (colour codeLength) (colour dataBuffer)
        (colour dataLength) (nonGc.map colour, gc.map colour)
  | .codeBufferWrite address value =>
      .codeBufferWrite (colour address) (colour value)
  | .dataBufferWrite address value =>
      .dataBufferWrite (colour address) (colour value)
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function (colour configuration) (colour configurationLength)
        (colour array) (colour arrayLength)
        (live.1.map colour, live.2.map colour)
  | .shareInst operator name address =>
      .shareInst operator (colour name) (wordApplyColourExp colour address)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateProgramWithSlotsAndColour (slots : List Nat)
    (program : WordProg α) : Option (WordContext × WordProg α) :=
  let (liveIn, edges) := wordProgClashAnalysis program []
  (wordAllocateContextWithClashes
      (slots ++ wordProgVariables program ++ liveIn) edges).map
    (fun context => (context, wordApplyColour (wordFindVar context) program))

theorem wordApplyColour_assign (colour : Nat → Nat) (name source : Nat) :
    wordApplyColour colour (.assign name (.var source) : WordProg α) =
      .assign (colour name) (.var (colour source)) := by
  simp [wordApplyColour, wordApplyColourExp]

theorem wordApplyColour_preserves_control_labels (colour : Nat → Nat) (label : Nat) :
    wordApplyColour colour (.break label : WordProg α) = .break label := by
  simp [wordApplyColour]

def wordProgBranchLabels : WordProg α → List Nat
  | .break label => [label]
  | .continue label => [label]
  | .seq first second =>
      wordProgBranchLabels first ++ wordProgBranchLabels second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgBranchLabels thenBranch ++ wordProgBranchLabels elseBranch
  | .loop _ body _ => wordProgBranchLabels body
  | .mustTerminate body => wordProgBranchLabels body
  | _ => []

theorem wordApplyColourPreservesBranchLabelsAux
    (colour : Nat → Nat) : (program : WordProg α) →
    wordProgBranchLabels (wordApplyColour colour program) =
      wordProgBranchLabels program
  | .skip => by simp [wordApplyColour, wordProgBranchLabels]
  | .move _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .assign _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .inst _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .get _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .store _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .set _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .seq first second => by
      simp [wordApplyColour, wordProgBranchLabels,
        wordApplyColourPreservesBranchLabelsAux colour first,
        wordApplyColourPreservesBranchLabelsAux colour second]
  | .ite _ _ _ thenBranch elseBranch => by
      simp [wordApplyColour, wordProgBranchLabels,
        wordApplyColourPreservesBranchLabelsAux colour thenBranch,
        wordApplyColourPreservesBranchLabelsAux colour elseBranch]
  | .loop _ body _ => by
      simp [wordApplyColour, wordProgBranchLabels,
        wordApplyColourPreservesBranchLabelsAux colour body]
  | .mustTerminate body => by
      simp [wordApplyColour, wordProgBranchLabels,
        wordApplyColourPreservesBranchLabelsAux colour body]
  | .break _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .continue _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .raise _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .return _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .tick => by simp [wordApplyColour, wordProgBranchLabels]
  | .locValue _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .call _ _ _ handler => by
      cases handler with
      | none => simp [wordApplyColour, wordProgBranchLabels]
      | some value =>
          rcases value with ⟨exception, body, handlerLabel, entryLabel⟩
          simp [wordApplyColour, wordProgBranchLabels]
  | .alloc _ cutsets => by
      cases cutsets <;> simp [wordApplyColour, wordProgBranchLabels]
  | .storeConsts _ _ _ _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .opCurrHeap _ _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .install _ _ _ _ cutsets => by
      cases cutsets <;> simp [wordApplyColour, wordProgBranchLabels]
  | .codeBufferWrite _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .dataBufferWrite _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .ffi _ _ _ _ _ _ => by simp [wordApplyColour, wordProgBranchLabels]
  | .shareInst _ _ _ => by simp [wordApplyColour, wordProgBranchLabels]
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem wordApplyColour_preserves_branch_labels
    (colour : Nat → Nat) (program : WordProg α) :
    wordProgBranchLabels (wordApplyColour colour program) =
      wordProgBranchLabels program :=
  wordApplyColourPreservesBranchLabelsAux colour program

/- CakeML's `extract_labels`: collect the label pairs carried by calls and
   their return and exception handlers.  These labels are metadata rather
   than virtual registers, so colouring must preserve them exactly. -/
def wordProgLabels : WordProg α → List (Nat × Nat)
  | .call returns _ _ handler =>
      let returnLabels :=
        match returns with
        | none => []
        | some (_, _, returnProgram, returnLabel, entryLabel) =>
            (returnLabel, entryLabel) :: wordProgLabels returnProgram
      let handlerLabels :=
        match handler with
        | none => []
        | some (_, handlerProgram, handlerLabel, entryLabel) =>
            (handlerLabel, entryLabel) :: wordProgLabels handlerProgram
      returnLabels ++ handlerLabels
  | .seq first second => wordProgLabels first ++ wordProgLabels second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgLabels thenBranch ++ wordProgLabels elseBranch
  | .loop _ body _ => wordProgLabels body
  | .mustTerminate body => wordProgLabels body
  | _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem wordApplyColourPreservesLabelsAux
    (colour : Nat → Nat) : (program : WordProg α) →
    wordProgLabels (wordApplyColour colour program) = wordProgLabels program
  | .skip => by simp [wordApplyColour, wordProgLabels]
  | .move _ _ => by simp [wordApplyColour, wordProgLabels]
  | .assign _ _ => by simp [wordApplyColour, wordProgLabels]
  | .inst _ => by simp [wordApplyColour, wordProgLabels]
  | .get _ _ => by simp [wordApplyColour, wordProgLabels]
  | .store _ _ => by simp [wordApplyColour, wordProgLabels]
  | .set _ _ => by simp [wordApplyColour, wordProgLabels]
  | .seq first second => by
      simp [wordApplyColour, wordProgLabels,
        wordApplyColourPreservesLabelsAux colour first,
        wordApplyColourPreservesLabelsAux colour second]
  | .ite _ _ _ thenBranch elseBranch => by
      simp [wordApplyColour, wordProgLabels,
        wordApplyColourPreservesLabelsAux colour thenBranch,
        wordApplyColourPreservesLabelsAux colour elseBranch]
  | .loop _ body _ => by
      simp [wordApplyColour, wordProgLabels,
        wordApplyColourPreservesLabelsAux colour body]
  | .mustTerminate body => by
      simp [wordApplyColour, wordProgLabels,
        wordApplyColourPreservesLabelsAux colour body]
  | .break _ => by simp [wordApplyColour, wordProgLabels]
  | .continue _ => by simp [wordApplyColour, wordProgLabels]
  | .raise _ => by simp [wordApplyColour, wordProgLabels]
  | .return _ _ => by simp [wordApplyColour, wordProgLabels]
  | .tick => by simp [wordApplyColour, wordProgLabels]
  | .locValue _ _ => by simp [wordApplyColour, wordProgLabels]
  | .call returns _ _ handler => by
      cases returns with
      | none =>
          cases handler with
          | none => simp [wordApplyColour, wordProgLabels]
          | some value =>
              rcases value with ⟨exception, handlerProgram, handlerLabel,
                entryLabel⟩
              have hhandler :=
                wordApplyColourPreservesLabelsAux colour handlerProgram
              simp [wordApplyColour, wordProgLabels, hhandler]
      | some value =>
          rcases value with ⟨values, cutsets, returnProgram, returnLabel,
            entryLabel⟩
          have hreturn :=
            wordApplyColourPreservesLabelsAux colour returnProgram
          cases handler with
          | none => simp [wordApplyColour, wordProgLabels]
          | some handlerValue =>
              rcases handlerValue with ⟨exception, handlerProgram,
                handlerLabel, handlerEntryLabel⟩
              have hhandler :=
                wordApplyColourPreservesLabelsAux colour handlerProgram
              simp [wordApplyColour, wordProgLabels, hhandler]
  | .alloc _ cutsets => by
      cases cutsets <;> simp [wordApplyColour, wordProgLabels]
  | .storeConsts _ _ _ _ _ => by simp [wordApplyColour, wordProgLabels]
  | .opCurrHeap _ _ _ => by simp [wordApplyColour, wordProgLabels]
  | .install _ _ _ _ cutsets => by
      cases cutsets <;> simp [wordApplyColour, wordProgLabels]
  | .codeBufferWrite _ _ => by simp [wordApplyColour, wordProgLabels]
  | .dataBufferWrite _ _ => by simp [wordApplyColour, wordProgLabels]
  | .ffi _ _ _ _ _ _ => by simp [wordApplyColour, wordProgLabels]
  | .shareInst _ _ _ => by simp [wordApplyColour, wordProgLabels]
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem wordApplyColour_preserves_labels
    (colour : Nat → Nat) (program : WordProg α) :
    wordProgLabels (wordApplyColour colour program) = wordProgLabels program :=
  wordApplyColourPreservesLabelsAux colour program

/- A clash-tree-backed allocation boundary matching CakeML's allocator shape:
   analyze the program, allocate the resulting variables, and apply the
   successful context colouring to the complete Word program. -/
def wordAllocateProgramWithClashTreeAndColour (slots : List Nat)
    (program : WordProg α) : Option (WordContext × WordProg α) :=
  let (liveIn, edges) :=
    wordClashTreeAnalyze (wordClashTree program []) []
  (wordAllocateContextWithClashes
      (slots ++ liveIn ++ wordProgVariables program) edges).map
    (fun context => (context, wordApplyColour (wordFindVar context) program))

theorem wordAllocateContextWithClashes_sound (slots : List Nat)
    (edges : List (Nat × Nat)) (context : WordContext)
    (halloc : wordAllocateContextWithClashes slots edges = some context) :
    wordColouringUsesAllocatable slots.eraseDups context.vars = true ∧
      wordColouringRespectsClashes edges context.vars = true := by
  simp [wordAllocateContextWithClashes] at halloc
  rcases halloc with ⟨hcheck, hcontext⟩
  rcases hcontext with ⟨hvars, rfl⟩
  simp [wordAllocateVarsWithClashes] at hvars
  split at hvars <;> simp_all
  rcases hvars with ⟨hgood, rfl⟩
  exact hgood

theorem wordAllocateProgramWithClashTreeAndColour_success
    (slots : List Nat) (program : WordProg α)
    (context : WordContext) (coloured : WordProg α)
    (halloc : wordAllocateProgramWithClashTreeAndColour slots program =
      some (context, coloured)) :
    wordProgLabels coloured = wordProgLabels program ∧
      wordProgBranchLabels coloured = wordProgBranchLabels program := by
  simp [wordAllocateProgramWithClashTreeAndColour] at halloc
  rcases halloc with ⟨hcontext, hcontextEq, hcoloured⟩
  rcases hcoloured with ⟨hcontextEq', hcoloured⟩
  subst context
  subst coloured
  constructor
  · exact wordApplyColour_preserves_labels _ _
  · exact wordApplyColour_preserves_branch_labels _ _

theorem wordProgClashAnalysis_skip :
    wordProgClashAnalysis (.skip : WordProg α) [] = ([], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs]

theorem wordProgClashAnalysis_seq :
    wordProgClashAnalysis
        ((.seq (.assign 0 (.var 1)) (.assign 2 (.var 0))) : WordProg α) [] =
      ([1], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordExpReadVars]

theorem wordProgClashAnalysis_ite :
    wordProgClashAnalysis
        ((.ite .equal 0 (.reg 1)
          (.assign 2 (.var 0)) (.assign 3 (.var 0))) : WordProg α) [] =
      ([0, 1], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars, wordProgWriteVars,
    wordProgLiveBefore, wordProgAtomicClashes, wordClashPairs,
    wordListUnion, wordExpReadVars, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

theorem wordLinearClashAnalysis_empty (liveOut : List Nat) :
    wordLinearClashAnalysis [] liveOut = (liveOut, []) := by
  rfl

theorem wordInstVars_addCarry :
    wordInstVars (.arith (.addCarry 1 2 3 4 5)) = [3, 4, 5, 1, 2] := by
  rfl

theorem wordSsaRenameLinear_addCarry :
    wordSsaRenameLinear
        { current := [(2, 100), (3, 101), (4, 102)], next := 200 }
        [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      ({ current := [(6, 212), (5, 208), (1, 204), (0, 200),
          (2, 100), (3, 101), (4, 102)], next := 216 },
        [.arith (.addCarry 200 204 100 101 102),
          .arith (.addCarry 208 212 200 204 100)]) := by
  rfl

theorem wordAllocateLinearInstructions_example :
    wordAllocateLinearInstructions
      [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      some { vars := [(6, 8), (5, 7), (1, 3), (0, 2), (4, 6), (3, 5), (2, 4)] } := by
  rfl

theorem wordAllocateVarsWithClashes_sound (slots : List Nat)
    (edges : List (Nat × Nat)) (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  simp [wordAllocateVarsWithClashes] at hcolouring
  split at hcolouring <;> try simp_all
  all_goals
    rcases hcolouring with ⟨hcheck, heq⟩
    simpa [heq] using hcheck

theorem wordAllocateVarsWithClashesAndPreferences_sound (slots : List Nat)
    (edges preferences : List (Nat × Nat)) (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashesAndPreferences slots edges preferences =
      some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  simp [wordAllocateVarsWithClashesAndPreferences] at hcolouring
  split at hcolouring <;> try simp_all
  all_goals
    rcases hcolouring with ⟨hcheck, heq⟩
    simpa [heq] using hcheck

theorem wordColouringUsesAllocatable_witness (names : List Nat)
    (colouring : NatInfoMap Nat)
    (huses : wordColouringUsesAllocatable names colouring = true) :
    ∀ name, name ∈ names →
      ∃ register,
        lookupNatInfo name colouring = some register ∧
          wordRegisterIsAllocatable register = true := by
  induction names with
  | nil =>
      intro name hname
      simp at hname
  | cons head tail ih =>
      cases hlookup : lookupNatInfo head colouring with
      | none =>
          simp [wordColouringUsesAllocatable, hlookup] at huses
      | some register =>
          have huses' :
              wordRegisterIsAllocatable register = true ∧
                wordColouringUsesAllocatable tail colouring = true := by
            simpa [wordColouringUsesAllocatable, hlookup] using huses
          intro name hname
          simp only [List.mem_cons] at hname
          rcases hname with rfl | hname
          · exact ⟨register, hlookup, huses'.1⟩
          · exact ih huses'.2 name hname

theorem wordAllocateVarsWithClashes_maps_slots (slots : List Nat)
    (edges : List (Nat × Nat)) (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    ∀ name, name ∈ slots.eraseDups →
      ∃ register,
        lookupNatInfo name colouring = some register ∧
          wordRegisterIsAllocatable register = true := by
  have hsound := wordAllocateVarsWithClashes_sound slots edges colouring hcolouring
  exact wordColouringUsesAllocatable_witness slots.eraseDups colouring hsound.1

/-! Spill-aware allocation boundary.  CakeML's `word_to_stack` pass consumes
    the spill information produced by `word_alloc`; keeping that information
    explicit here prevents register exhaustion from being confused with a
    failed compilation.  Stack rewriting is intentionally a following pass:
    this result records a fresh stack slot for every value that cannot use a
    target register, while preserving the same clash check for values that do
    receive registers. -/

inductive WordLocation where
  | register (register : Nat)
  | stack (slot : Nat)
  deriving DecidableEq, Repr

/-! Give spilled values colours outside the physical-register range so the
    clash-tree oracle can validate register/register conflicts while treating
    distinct stack slots as distinct locations. -/

def wordSpillLocationColour (locations : NatInfoMap WordLocation)
    (name : Nat) : Nat :=
  match lookupNatInfo name locations with
  | some (.register register) => register
  | some (.stack slot) => 32 + slot
  | none => 32 + name

def wordSpillClashTreeChecked (tree : WordClashTree)
    (locations : NatInfoMap WordLocation) : Bool :=
  (wordClashTreeCheck (wordSpillLocationColour locations) tree [] []).isSome

/-! The Word-to-Stack special-instruction contract is checked at allocation.
    `LongMul` writes its high result before its low result and is normalized
    through the reserved scratch registers when locations spill. `AddCarry`
    likewise uses reserved scratch registers when one of its values spills;
    the register-resident path retains the x31 exclusion. Keep these contracts
    next to allocation so unsupported layouts cannot silently reach instruction
    selection. -/

def wordSpecialArithLocationsSafe (operation : WordArith)
    (locations : NatInfoMap WordLocation) : Bool :=
  match operation with
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      match lookupNatInfo destinationLeft locations,
        lookupNatInfo destinationRight locations,
        lookupNatInfo sourceLeft locations,
        lookupNatInfo sourceRight locations with
      | some destinationLeft, some destinationRight,
          some sourceLeft, some sourceRight =>
          destinationLeft != destinationRight &&
            destinationLeft != sourceLeft && destinationLeft != sourceRight
      | _, _, _, _ => false
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      match lookupNatInfo destination locations,
        lookupNatInfo resultCarry locations,
        lookupNatInfo sourceLeft locations,
        lookupNatInfo sourceRight locations,
        lookupNatInfo carryIn locations with
      | some destination, some resultCarry, some sourceLeft,
          some sourceRight, some carryIn =>
          destination != resultCarry &&
            match destination, resultCarry, sourceLeft, sourceRight, carryIn with
            | .register destination, .register resultCarry,
                .register sourceLeft, .register sourceRight, .register carryIn =>
                destination != sourceLeft && destination != sourceRight &&
                  destination != 31 && resultCarry != 31 &&
                  sourceLeft != 31 && sourceRight != 31 && carryIn != 31
            | _, _, _, _, _ => true
      | _, _, _, _, _ => false
  | .longDiv _ _ _ _ _ | .div _ _ _ => true

def wordProgSpecialLocationsSafe (locations : NatInfoMap WordLocation) :
    WordProg α → Bool
  | .skip => true
  | .move _ _ | .assign _ _ | .get _ _ | .store _ _ | .set _ _ | .break _ | .continue _ |
      .raise _ | .return _ _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ => true
  | .inst (.arith operation) => wordSpecialArithLocationsSafe operation locations
  | .inst (.mem _ _ _) => true
  | .seq first second =>
      wordProgSpecialLocationsSafe locations first &&
        wordProgSpecialLocationsSafe locations second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgSpecialLocationsSafe locations thenBranch &&
        wordProgSpecialLocationsSafe locations elseBranch
  | .loop _ body _ => wordProgSpecialLocationsSafe locations body
  | .mustTerminate body => wordProgSpecialLocationsSafe locations body
  | .call _ _ _ none => true
  | .call _ _ _ (some (_, body, _, _)) =>
      wordProgSpecialLocationsSafe locations body
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .opCurrHeap _ _ _ |
      .install _ _ _ _ _ | .codeBufferWrite _ _ | .dataBufferWrite _ _ => true
  | .shareInst _ _ _ => true
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

structure WordSpillState where
  locations : NatInfoMap WordLocation
  nextSpill : Nat
  deriving Repr

def wordUsedLocationRegisters (names : List Nat)
    (locations : NatInfoMap WordLocation) : List Nat :=
  match names with
  | [] => []
  | name :: names =>
      let registers := match lookupNatInfo name locations with
        | some (.register register) => [register]
        | some (.stack _) | none => []
      registers ++ wordUsedLocationRegisters names locations

def wordPreferenceLocationRegisters (name : Nat)
    (preferences : List (Nat × Nat))
    (locations : NatInfoMap WordLocation) : List Nat :=
  match preferences with
  | [] => []
  | (left, right) :: preferences =>
      if left == name then
        match lookupNatInfo right locations with
        | some (.register register) =>
            register :: wordPreferenceLocationRegisters name preferences locations
        | some (.stack _) | none =>
            wordPreferenceLocationRegisters name preferences locations
      else if right == name then
        match lookupNatInfo left locations with
        | some (.register register) =>
            register :: wordPreferenceLocationRegisters name preferences locations
        | some (.stack _) | none =>
            wordPreferenceLocationRegisters name preferences locations
      else
        wordPreferenceLocationRegisters name preferences locations

def wordColourCandidatesWithSpillPreferences (name : Nat)
    (preferences : List (Nat × Nat))
    (locations : NatInfoMap WordLocation) : List Nat :=
  wordPreferenceLocationRegisters name preferences locations ++
    wordColourCandidates name

def wordGreedyAllocateWithSpillsAndPreferences : List Nat →
    List (Nat × Nat) → List (Nat × Nat) → WordSpillState → WordSpillState
  | [], _, _, state => state
  | name :: names, edges, preferences, state =>
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours name edges) state.locations
      let candidates := wordColourCandidatesWithSpillPreferences name
        preferences state.locations
      let state := match wordFirstAvailable candidates forbidden with
        | some register =>
            { state with locations := (name, .register register) :: state.locations }
        | none =>
            { locations := (name, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      wordGreedyAllocateWithSpillsAndPreferences names edges preferences state

def wordGreedyAllocateWithSpills : List Nat → List (Nat × Nat) →
    WordSpillState → WordSpillState
  | [], _, state => state
  | name :: names, edges, state =>
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours name edges) state.locations
      let state := match wordFirstAvailable (wordColourCandidates name) forbidden with
        | some register =>
            { state with locations := (name, .register register) :: state.locations }
        | none =>
            { locations := (name, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      wordGreedyAllocateWithSpills names edges state

def wordSpillAllocationRespectsClashes (edges : List (Nat × Nat))
    (locations : NatInfoMap WordLocation) : Bool :=
  match edges with
  | [] => true
  | (left, right) :: edges =>
      match lookupNatInfo left locations, lookupNatInfo right locations with
      | some (.register leftRegister), some (.register rightRegister) =>
          leftRegister != rightRegister &&
            wordSpillAllocationRespectsClashes edges locations
      | some _, some _ => wordSpillAllocationRespectsClashes edges locations
      | _, _ => false

def wordAllocateVarsWithSpills (slots : List Nat)
    (edges : List (Nat × Nat)) : Option WordSpillState :=
  let state := wordGreedyAllocateWithSpills slots.eraseDups edges
    { locations := [], nextSpill := 0 }
  if wordSpillAllocationRespectsClashes edges state.locations then some state
  else none

def wordAllocateVarsWithSpillsAndPreferences (slots : List Nat)
    (edges preferences : List (Nat × Nat)) : Option WordSpillState :=
  let state := wordGreedyAllocateWithSpillsAndPreferences slots.eraseDups
    edges preferences { locations := [], nextSpill := 0 }
  if wordSpillAllocationRespectsClashes edges state.locations then some state
  else none

/-! Entry moves read architectural ABI sources.  Seed those names with their
    architectural registers and remove them from the greedy worklist, so the
    spill allocator cannot silently reassign an input before the entry move
    executes. -/

def wordFixedSourceLocations : List Nat → NatInfoMap WordLocation
  | [] => []
  | source :: sources =>
      (source, .register source) :: wordFixedSourceLocations sources

def wordAllocateVarsWithFixedSources (slots : List Nat)
    (edges preferences : List (Nat × Nat))
    (fixedSources : List Nat) : Option WordSpillState :=
  let initial : WordSpillState :=
    { locations := wordFixedSourceLocations fixedSources, nextSpill := 0 }
  let names := slots.eraseDups.filter (fun name => name ∉ fixedSources)
  let state := wordGreedyAllocateWithSpillsAndPreferences names
    edges preferences initial
  if wordSpillAllocationRespectsClashes edges state.locations then some state
  else none

theorem lookupNatInfo_wordFixedSourceLocations_mem
    (fixedSources : List Nat) (name : Nat) (hname : name ∈ fixedSources) :
    lookupNatInfo name (wordFixedSourceLocations fixedSources) =
      some (.register name) := by
  induction fixedSources with
  | nil => simp at hname
  | cons source sources ih =>
      simp only [wordFixedSourceLocations, List.mem_cons] at hname ⊢
      by_cases hsource : source = name
      · subst source
        simp [lookupNatInfo]
      · have hname' : name ∈ sources := by
          have hsource' : name ≠ source := Ne.symm hsource
          simpa [hsource'] using hname
        simp [lookupNatInfo, hsource, ih hname']

theorem wordGreedyAllocateWithSpills_preserves_lookup (names : List Nat)
    (edges : List (Nat × Nat)) (state : WordSpillState) :
    ∀ name, name ∉ names →
      lookupNatInfo name
          (wordGreedyAllocateWithSpills names edges state).locations =
        lookupNatInfo name state.locations := by
  induction names generalizing state with
  | nil =>
      intro name hname
      rfl
  | cons head tail ih =>
      intro name hname
      have hneq : name ≠ head := by
        intro heq
        apply hname
        simp [heq]
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours head edges) state.locations
      let allocated := match wordFirstAvailable
          (wordColourCandidates head) forbidden with
        | some register =>
            { state with locations := (head, .register register) :: state.locations }
        | none =>
            { locations := (head, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      have hneq' : ¬ head == name := by
        intro heq
        have heq' : head = name := by simpa using heq
        exact hneq heq'.symm
      cases havailable : wordFirstAvailable
          (wordColourCandidates head) forbidden with
      | none =>
          have htail := ih allocated name (by
            intro htail
            apply hname
            exact List.mem_cons_of_mem _ htail)
          calc
            lookupNatInfo name
                (wordGreedyAllocateWithSpills (head :: tail) edges state).locations =
                lookupNatInfo name
                  (wordGreedyAllocateWithSpills tail edges allocated).locations := by
                    simp [wordGreedyAllocateWithSpills, forbidden, allocated, havailable]
            _ = lookupNatInfo name allocated.locations := htail
            _ = lookupNatInfo name state.locations := by
              simp [allocated, havailable, lookupNatInfo, hneq']
      | some register =>
          have htail := ih allocated name (by
            intro htail
            apply hname
            exact List.mem_cons_of_mem _ htail)
          calc
            lookupNatInfo name
                (wordGreedyAllocateWithSpills (head :: tail) edges state).locations =
                lookupNatInfo name
                  (wordGreedyAllocateWithSpills tail edges allocated).locations := by
                    simp [wordGreedyAllocateWithSpills, forbidden, allocated, havailable]
            _ = lookupNatInfo name allocated.locations := htail
            _ = lookupNatInfo name state.locations := by
              simp [allocated, havailable, lookupNatInfo, hneq']

theorem wordGreedyAllocateWithSpills_maps_names (names : List Nat)
    (edges : List (Nat × Nat)) (state : WordSpillState)
    : ∀ name, name ∈ names →
      ∃ location,
        lookupNatInfo name
          (wordGreedyAllocateWithSpills names edges state).locations =
          some location := by
  induction names generalizing state with
  | nil =>
      intro name hname
      simp at hname
  | cons head tail ih =>
      intro name hname
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours head edges) state.locations
      let allocated := match wordFirstAvailable
          (wordColourCandidates head) forbidden with
        | some register =>
            { state with locations := (head, .register register) :: state.locations }
        | none =>
            { locations := (head, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      cases havailable : wordFirstAvailable
          (wordColourCandidates head) forbidden with
      | none =>
          have hname_cases : name = head ∨ name ∈ tail := by
            simpa [List.mem_cons] using hname
          rcases hname_cases with heq | htail
          · subst name
            by_cases hdup : head ∈ tail
            · simpa [wordGreedyAllocateWithSpills, forbidden, allocated,
                havailable] using ih allocated head hdup
            · have htail_lookup :=
                wordGreedyAllocateWithSpills_preserves_lookup tail edges allocated
                  head hdup
              have hself : head == head := by simp
              refine ⟨.stack state.nextSpill, ?_⟩
              calc
                lookupNatInfo head
                    (wordGreedyAllocateWithSpills (head :: tail) edges state).locations =
                    lookupNatInfo head
                      (wordGreedyAllocateWithSpills tail edges allocated).locations := by
                        simp [wordGreedyAllocateWithSpills, forbidden, allocated, havailable]
                _ = lookupNatInfo head allocated.locations := htail_lookup
                _ = some (.stack state.nextSpill) := by
                  simp [allocated, havailable, lookupNatInfo]
          · simpa [wordGreedyAllocateWithSpills, forbidden, allocated,
              havailable] using ih allocated name htail
      | some register =>
          have hname_cases : name = head ∨ name ∈ tail := by
            simpa [List.mem_cons] using hname
          rcases hname_cases with heq | htail
          · subst name
            by_cases hdup : head ∈ tail
            · simpa [wordGreedyAllocateWithSpills, forbidden, allocated,
                havailable] using ih allocated head hdup
            · have htail_lookup :=
                wordGreedyAllocateWithSpills_preserves_lookup tail edges allocated
                  head hdup
              have hself : head == head := by simp
              refine ⟨.register register, ?_⟩
              calc
                lookupNatInfo head
                    (wordGreedyAllocateWithSpills (head :: tail) edges state).locations =
                    lookupNatInfo head
                      (wordGreedyAllocateWithSpills tail edges allocated).locations := by
                        simp [wordGreedyAllocateWithSpills, forbidden, allocated, havailable]
                _ = lookupNatInfo head allocated.locations := htail_lookup
                _ = some (.register register) := by
                  simp [allocated, havailable, lookupNatInfo]
          · simpa [wordGreedyAllocateWithSpills, forbidden, allocated,
              havailable] using ih allocated name htail

theorem wordAllocateVarsWithSpills_maps_slots (slots : List Nat)
    (edges : List (Nat × Nat)) (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpills slots edges = some state) :
    ∀ name, name ∈ slots.eraseDups →
      ∃ location, lookupNatInfo name state.locations = some location := by
  let allocated : WordSpillState :=
    wordGreedyAllocateWithSpills slots.eraseDups edges
      { locations := [], nextSpill := 0 }
  have hstate' :
      (if wordSpillAllocationRespectsClashes edges allocated.locations = true then
          some allocated else none) = some state := by
    simpa [wordAllocateVarsWithSpills, allocated] using hstate
  split at hstate'
  · have heq : allocated = state := Option.some.inj hstate'
    subst state
    simpa [allocated] using
      (wordGreedyAllocateWithSpills_maps_names slots.eraseDups edges
        { locations := [], nextSpill := 0 })
  · contradiction

theorem wordGreedyAllocateWithSpillsAndPreferences_preserves_lookup
    (names : List Nat) (edges preferences : List (Nat × Nat))
    (state : WordSpillState) :
    ∀ name, name ∉ names →
      lookupNatInfo name
          (wordGreedyAllocateWithSpillsAndPreferences names edges preferences
            state).locations =
        lookupNatInfo name state.locations := by
  induction names generalizing state with
  | nil =>
      intro name hname
      rfl
  | cons head tail ih =>
      intro name hname
      have hneq : name ≠ head := by
        intro heq
        apply hname
        simp [heq]
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours head edges) state.locations
      let candidates := wordColourCandidatesWithSpillPreferences head
        preferences state.locations
      let allocated := match wordFirstAvailable candidates forbidden with
        | some register =>
            { state with locations := (head, .register register) :: state.locations }
        | none =>
            { locations := (head, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      have hneq' : ¬ head == name := by
        intro heq
        have heq' : head = name := by simpa using heq
        exact hneq heq'.symm
      cases havailable : wordFirstAvailable candidates forbidden with
      | none =>
          have htail := ih allocated name (by
            intro htail
            apply hname
            exact List.mem_cons_of_mem _ htail)
          calc
            lookupNatInfo name
                (wordGreedyAllocateWithSpillsAndPreferences (head :: tail)
                  edges preferences state).locations =
                lookupNatInfo name
                  (wordGreedyAllocateWithSpillsAndPreferences tail edges
                    preferences allocated).locations := by
                      simp [wordGreedyAllocateWithSpillsAndPreferences,
                        forbidden, candidates, allocated, havailable]
            _ = lookupNatInfo name allocated.locations := htail
            _ = lookupNatInfo name state.locations := by
              simp [allocated, havailable, lookupNatInfo, hneq']
      | some register =>
          have htail := ih allocated name (by
            intro htail
            apply hname
            exact List.mem_cons_of_mem _ htail)
          calc
            lookupNatInfo name
                (wordGreedyAllocateWithSpillsAndPreferences (head :: tail)
                  edges preferences state).locations =
                lookupNatInfo name
                  (wordGreedyAllocateWithSpillsAndPreferences tail edges
                    preferences allocated).locations := by
                      simp [wordGreedyAllocateWithSpillsAndPreferences,
                        forbidden, candidates, allocated, havailable]
            _ = lookupNatInfo name allocated.locations := htail
            _ = lookupNatInfo name state.locations := by
              simp [allocated, havailable, lookupNatInfo, hneq']

theorem wordAllocateVarsWithFixedSources_preserves_fixed_source
    (slots : List Nat) (edges preferences : List (Nat × Nat))
    (fixedSources : List Nat) (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources slots edges preferences
      fixedSources = some state) (name : Nat) (hname : name ∈ fixedSources) :
    lookupNatInfo name state.locations = some (.register name) := by
  let initial : WordSpillState :=
    { locations := wordFixedSourceLocations fixedSources, nextSpill := 0 }
  let names := slots.eraseDups.filter (fun candidate => candidate ∉ fixedSources)
  let allocated := wordGreedyAllocateWithSpillsAndPreferences names
    edges preferences initial
  have hstate' :
      (if wordSpillAllocationRespectsClashes edges allocated.locations = true then
          some allocated else none) = some state := by
    simpa [wordAllocateVarsWithFixedSources, initial, names, allocated] using hstate
  split at hstate'
  · have heq : allocated = state := Option.some.inj hstate'
    subst state
    have hnot : name ∉ names := by
      simp [names, hname]
    calc
      lookupNatInfo name allocated.locations =
          lookupNatInfo name initial.locations :=
        wordGreedyAllocateWithSpillsAndPreferences_preserves_lookup
          names edges preferences initial name hnot
      _ = some (.register name) := by
        exact lookupNatInfo_wordFixedSourceLocations_mem fixedSources name hname
  · contradiction

theorem wordGreedyAllocateWithSpillsAndPreferences_maps_names
    (names : List Nat) (edges preferences : List (Nat × Nat))
    (state : WordSpillState) :
    ∀ name, name ∈ names →
      ∃ location,
        lookupNatInfo name
          (wordGreedyAllocateWithSpillsAndPreferences names edges preferences
            state).locations = some location := by
  induction names generalizing state with
  | nil =>
      intro name hname
      simp at hname
  | cons head tail ih =>
      intro name hname
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours head edges) state.locations
      let candidates := wordColourCandidatesWithSpillPreferences head
        preferences state.locations
      let allocated := match wordFirstAvailable candidates forbidden with
        | some register =>
            { state with locations := (head, .register register) :: state.locations }
        | none =>
            { locations := (head, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      cases havailable : wordFirstAvailable candidates forbidden with
      | none =>
          have hname_cases : name = head ∨ name ∈ tail := by
            simpa [List.mem_cons] using hname
          rcases hname_cases with heq | htail
          · subst name
            by_cases hdup : head ∈ tail
            · simpa [wordGreedyAllocateWithSpillsAndPreferences, forbidden,
                candidates, allocated, havailable] using ih allocated head hdup
            · have htail_lookup :=
                wordGreedyAllocateWithSpillsAndPreferences_preserves_lookup tail
                  edges preferences allocated head hdup
              have hself : head == head := by simp
              refine ⟨.stack state.nextSpill, ?_⟩
              calc
                lookupNatInfo head
                    (wordGreedyAllocateWithSpillsAndPreferences (head :: tail)
                      edges preferences state).locations =
                    lookupNatInfo head
                      (wordGreedyAllocateWithSpillsAndPreferences tail edges
                        preferences allocated).locations := by
                          simp [wordGreedyAllocateWithSpillsAndPreferences,
                            forbidden, candidates, allocated, havailable]
                _ = lookupNatInfo head allocated.locations := htail_lookup
                _ = some (.stack state.nextSpill) := by
                  simp [allocated, havailable, lookupNatInfo]
          · simpa [wordGreedyAllocateWithSpillsAndPreferences, forbidden,
              candidates, allocated, havailable] using ih allocated name htail
      | some register =>
          have hname_cases : name = head ∨ name ∈ tail := by
            simpa [List.mem_cons] using hname
          rcases hname_cases with heq | htail
          · subst name
            by_cases hdup : head ∈ tail
            · simpa [wordGreedyAllocateWithSpillsAndPreferences, forbidden,
                candidates, allocated, havailable] using ih allocated head hdup
            · have htail_lookup :=
                wordGreedyAllocateWithSpillsAndPreferences_preserves_lookup tail
                  edges preferences allocated head hdup
              have hself : head == head := by simp
              refine ⟨.register register, ?_⟩
              calc
                lookupNatInfo head
                    (wordGreedyAllocateWithSpillsAndPreferences (head :: tail)
                      edges preferences state).locations =
                    lookupNatInfo head
                      (wordGreedyAllocateWithSpillsAndPreferences tail edges
                        preferences allocated).locations := by
                          simp [wordGreedyAllocateWithSpillsAndPreferences,
                            forbidden, candidates, allocated, havailable]
                _ = lookupNatInfo head allocated.locations := htail_lookup
                _ = some (.register register) := by
                  simp [allocated, havailable, lookupNatInfo]
          · simpa [wordGreedyAllocateWithSpillsAndPreferences, forbidden,
              candidates, allocated, havailable] using ih allocated name htail

theorem wordAllocateVarsWithFixedSources_maps_slots (slots : List Nat)
    (edges preferences : List (Nat × Nat)) (fixedSources : List Nat)
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources slots edges preferences
      fixedSources = some state) :
    ∀ name, name ∈ slots.eraseDups →
      ∃ location, lookupNatInfo name state.locations = some location := by
  let initial : WordSpillState :=
    { locations := wordFixedSourceLocations fixedSources, nextSpill := 0 }
  let names := slots.eraseDups.filter (fun candidate => candidate ∉ fixedSources)
  let allocated := wordGreedyAllocateWithSpillsAndPreferences names
    edges preferences initial
  have hstate' :
      (if wordSpillAllocationRespectsClashes edges allocated.locations = true then
          some allocated else none) = some state := by
    simpa [wordAllocateVarsWithFixedSources, initial, names, allocated] using hstate
  split at hstate'
  · have heq : allocated = state := Option.some.inj hstate'
    subst state
    intro name hslot
    by_cases hfixed : name ∈ fixedSources
    · have hnot : name ∉ names := by
        simp [names, hfixed]
      refine ⟨.register name, ?_⟩
      calc
        lookupNatInfo name allocated.locations = lookupNatInfo name initial.locations :=
          wordGreedyAllocateWithSpillsAndPreferences_preserves_lookup
            names edges preferences initial name hnot
        _ = some (.register name) :=
          lookupNatInfo_wordFixedSourceLocations_mem fixedSources name hfixed
    · have hname : name ∈ names := by
        simp [names, hslot, hfixed]
      exact wordGreedyAllocateWithSpillsAndPreferences_maps_names
        names edges preferences initial name hname
  · contradiction

theorem wordAllocateVarsWithSpillsAndPreferences_maps_slots (slots : List Nat)
    (edges preferences : List (Nat × Nat)) (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpillsAndPreferences slots edges preferences =
      some state) :
    ∀ name, name ∈ slots.eraseDups →
      ∃ location, lookupNatInfo name state.locations = some location := by
  let allocated : WordSpillState :=
    wordGreedyAllocateWithSpillsAndPreferences slots.eraseDups edges preferences
      { locations := [], nextSpill := 0 }
  have hstate' :
      (if wordSpillAllocationRespectsClashes edges allocated.locations = true then
          some allocated else none) = some state := by
    simpa [wordAllocateVarsWithSpillsAndPreferences, allocated] using hstate
  split at hstate'
  · have heq : allocated = state := Option.some.inj hstate'
    subst state
    simpa [allocated] using
      (wordGreedyAllocateWithSpillsAndPreferences_maps_names slots.eraseDups
        edges preferences { locations := [], nextSpill := 0 })
  · contradiction

def wordAllocateSsaProgramWithSpills (state : WordSsaState)
    (program : WordProg α) :
    Option (WordSsaState × WordProg α × WordSpillState) :=
  let (state, program) := wordSsaRenameProgram state program
  let (liveIn, edges) := wordProgClashAnalysis program []
  match wordAllocateVarsWithSpills (wordProgVariables program ++ liveIn) edges with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true then
        some (state, program, allocation)
      else
        none

/-! The same spill boundary using the CakeML-shaped clash tree.  Keeping this
    as a separate entry point makes it possible to compare the compact
    liveness analysis and the structural tree while the full colouring
    heuristic is being ported. -/

def wordAllocateSsaProgramWithClashTreeWithSpills (state : WordSsaState)
    (program : WordProg α) :
    Option (WordSsaState × WordProg α × WordSpillState) :=
  let (state, program) := wordSsaRenameProgram state program
  let (liveIn, edges) :=
    wordClashTreeAnalyze (wordClashTree program []) []
  match wordAllocateVarsWithSpills
      (wordProgVariables program ++ liveIn) edges with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true then
        some (state, program, allocation)
      else
        none

def wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences
    (state : WordSsaState) (program : WordProg α) :
    Option (WordSsaState × WordProg α × WordSpillState) :=
  let (state, program) := wordSsaRenameProgram state program
  let tree := wordClashTree program []
  let (liveIn, edges) := wordClashTreeAnalyze tree []
  let preferences := wordProgPreferenceEdges program
  match wordAllocateVarsWithSpillsAndPreferences
      (wordProgVariables program ++ liveIn) edges preferences with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true &&
          wordSpillClashTreeChecked tree allocation.locations then
        some (state, program, allocation)
      else
        none

theorem wordAllocateSsaProgramWithSpills_maps_variables
    (state : WordSsaState) (program : WordProg α)
    (renamedState : WordSsaState) (renamedProgram : WordProg α)
    (allocation : WordSpillState)
    (halloc : wordAllocateSsaProgramWithSpills state program =
      some (renamedState, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaProgramWithSpills] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpills_maps_slots
    (wordProgVariables (wordSsaRenameProgram state program).2 ++
      (wordProgClashAnalysis (wordSsaRenameProgram state program).2 []).fst)
    (wordProgClashAnalysis (wordSsaRenameProgram state program).2 []).snd
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

/-! Function-level spill allocation, including CakeML's fresh formal
    parameters in the allocation input.  A formal that is unused by the body
    still occurs in the generated entry move and therefore must receive a
    location. -/

def wordAllocateSsaFunctionWithSpills (parameters : List Nat)
    (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, program) :=
    wordSsaRenameFunction parameters program
  let (liveIn, edges) := wordProgClashAnalysis program []
  match wordAllocateVarsWithSpills
      (renamedParameters ++ wordProgVariables program ++ liveIn) edges with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true then
        some (state, renamedParameters, program, allocation)
      else
        none

/-! Function-level variant using the CakeML-shaped clash tree and move
    preferences.  The renamed formal parameters remain allocation slots so
    that the generated entry moves are valid even when a formal is otherwise
    unused. -/

def wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
    (parameters : List Nat) (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, program) :=
    wordSsaRenameFunction parameters program
  let tree := wordClashTree program []
  let (liveIn, edges) := wordClashTreeAnalyze tree []
  let preferences := wordProgPreferenceEdges program
  match wordAllocateVarsWithSpillsAndPreferences
      (renamedParameters ++ wordProgVariables program ++ liveIn)
      edges preferences with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true &&
          wordSpillClashTreeChecked tree allocation.locations then
        some (state, renamedParameters, program, allocation)
      else
        none

/-! ABI-correct variant of the entry-aware spill allocator.  The source
    parameter names are fixed to their architectural registers before the
    remaining SSA names are assigned registers or spill slots. -/

def wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
    (parameters : List Nat) (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, program) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := wordClashTree program []
  let (liveIn, edges) := wordClashTreeAnalyze tree []
  let preferences := wordProgPreferenceEdges program
  match wordAllocateVarsWithFixedSources
      (renamedParameters ++ wordProgVariables program ++ liveIn)
      edges preferences (wordPhysicalFixedSources parameters program) with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true &&
          wordSpillClashTreeChecked tree allocation.locations then
        some (state, renamedParameters, program, allocation)
      else
        none

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_preserves_parameters
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ parameters →
      lookupNatInfo name allocation.locations = some (.register name) := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  intro name hname
  apply wordAllocateVarsWithFixedSources_preserves_fixed_source _ _ _ _ alloc
    hallocation name
  exact List.mem_append_left _ hname

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithFixedSources_maps_slots
    ((wordSsaRenameFunctionWithEntry parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunctionWithEntry parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []) []).snd
    (wordProgPreferenceEdges
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (wordPhysicalFixedSources parameters
      (wordSsaRenameFunctionWithEntry parameters program).2.snd) alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateVarsWithFixedSources_sound (slots : List Nat)
    (edges preferences : List (Nat × Nat)) (fixedSources : List Nat)
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources slots edges preferences
      fixedSources = some state) :
    wordSpillAllocationRespectsClashes edges state.locations = true := by
  simp [wordAllocateVarsWithFixedSources] at hstate
  rcases hstate with ⟨hcheck, heq⟩
  simpa [heq] using hcheck

/-! Spill allocation over the complete CakeML-shaped SSA function.  In
    contrast with the historical entry point above, the explicit formal
    parameter moves are present in the clash tree, preferences, and returned
    program. -/

def wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences
    (parameters : List Nat) (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, program) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := wordClashTree program []
  let (liveIn, edges) := wordClashTreeAnalyze tree []
  let preferences := wordProgPreferenceEdges program
  match wordAllocateVarsWithSpillsAndPreferences
      (renamedParameters ++ wordProgVariables program ++ liveIn)
      edges preferences with
  | none => none
  | some allocation =>
      if wordProgSpecialLocationsSafe allocation.locations program = true &&
          wordSpillClashTreeChecked tree allocation.locations then
        some (state, renamedParameters, program, allocation)
      else
        none

theorem wordAllocateSsaFunctionWithSpills_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc : wordAllocateSsaFunctionWithSpills parameters program =
      some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithSpills] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpills_maps_slots
    ((wordSsaRenameFunction parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunction parameters program).2.snd ++
        (wordProgClashAnalysis (wordSsaRenameFunction parameters program).2.snd
          []).fst))
    (wordProgClashAnalysis (wordSsaRenameFunction parameters program).2.snd
    []).snd alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpillsAndPreferences_maps_slots
    ((wordSsaRenameFunction parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunction parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []) []).snd
    (wordProgPreferenceEdges (wordSsaRenameFunction parameters program).2.snd)
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences_maps_variables
    (state : WordSsaState) (program : WordProg α)
    (renamedState : WordSsaState) (renamedProgram : WordProg α)
    (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences state
        program = some (renamedState, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpillsAndPreferences_maps_slots
    (wordProgVariables (wordSsaRenameProgram state program).2 ++
      (wordClashTreeAnalyze
        (wordClashTree (wordSsaRenameProgram state program).2 []) []).fst)
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameProgram state program).2 []) []).snd
    (wordProgPreferenceEdges (wordSsaRenameProgram state program).2)
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_safe
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordProgSpecialLocationsSafe allocation.locations renamedProgram = true ∧
    wordSpillClashTreeChecked (wordClashTree renamedProgram [])
        allocation.locations := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨⟨hsafe, htree⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst renamedProgram
  subst allocation
  exact ⟨hsafe, htree⟩

theorem wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences_safe
    (state : WordSsaState) (program : WordProg α)
    (renamedState : WordSsaState) (renamedProgram : WordProg α)
    (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences state
        program = some (renamedState, renamedProgram, allocation)) :
    wordProgSpecialLocationsSafe allocation.locations renamedProgram = true ∧
      wordSpillClashTreeChecked (wordClashTree renamedProgram [])
        allocation.locations := by
  simp [wordAllocateSsaProgramWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨⟨hsafe, htree⟩, hstate, hprogram, hallocation⟩
  subst renamedProgram
  subst allocation
  exact ⟨hsafe, htree⟩

theorem wordAllocateVarsWithSpills_sound (slots : List Nat)
    (edges : List (Nat × Nat)) (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpills slots edges = some state) :
    wordSpillAllocationRespectsClashes edges state.locations = true := by
  simp [wordAllocateVarsWithSpills] at hstate
  rcases hstate with ⟨hcheck, heq⟩
  simpa [heq] using hcheck

theorem wordAllocateVarsWithSpillsAndPreferences_sound (slots : List Nat)
    (edges preferences : List (Nat × Nat)) (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpillsAndPreferences slots edges preferences =
      some state) :
    wordSpillAllocationRespectsClashes edges state.locations = true := by
  simp [wordAllocateVarsWithSpillsAndPreferences] at hstate
  rcases hstate with ⟨hcheck, heq⟩
  simpa [heq] using hcheck

theorem wordAllocateSsaProgramWithSpills_respects_clashes
    (state : WordSsaState) (program : WordProg α)
    (renamedState : WordSsaState) (renamedProgram : WordProg α)
    (allocation : WordSpillState)
    (halloc : wordAllocateSsaProgramWithSpills state program =
      some (renamedState, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
      (wordProgClashAnalysis renamedProgram []).snd allocation.locations = true := by
  simp [wordAllocateSsaProgramWithSpills] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  exact wordAllocateVarsWithSpills_sound _ _ alloc hallocation

theorem wordAllocateVarsWithSpills_example :
    wordAllocateVarsWithSpills [0, 1] [(0, 1)] =
      some { locations := [(1, .register 3), (0, .register 2)], nextSpill := 0 } := by
  rfl

theorem wordAllocateVarsWithSpills_spills_example :
    (wordAllocateVarsWithSpills (List.range 29)
      (wordPairwiseClashes (List.range 29))).map
        (fun state => state.nextSpill != 0) = some true := by
  decide +kernel

theorem wordAllocatableRegisters_safe :
    ∀ register ∈ wordAllocatableRegisters,
      wordRegisterIsAllocatable register = true := by
  intro register hregister
  simp [wordAllocatableRegisters, wordRegisterIsAllocatable] at hregister ⊢
  omega

theorem wordAllocatableRegisters_not_reserved :
    ∀ register ∈ wordAllocatableRegisters,
      wordRegisterIsReserved register = false := by
  intro register hregister
  simp [wordAllocatableRegisters, wordRegisterIsReserved] at hregister ⊢
  omega

theorem wordPreferredRegister_safe (name register : Nat)
    (hregister : wordPreferredRegister name = some register) :
    wordRegisterIsAllocatable register = true := by
  simp [wordPreferredRegister] at hregister
  rcases hregister with ⟨hbound, rfl⟩
  simp [wordRegisterIsAllocatable]
  omega

theorem wordAllocateContext_examples :
    wordAllocateContext [0, 1, 29, 30] =
      some { vars := [(0, 2), (1, 3), (29, 4), (30, 5)] } := by
  rfl

theorem wordAllocateContext_preserves_small_names :
    wordAllocateContext [0, 1, 2, 3] =
      some { vars := [(0, 2), (1, 3), (2, 4), (3, 5)] } := by
  rfl

theorem wordAllocateContext_add_slots :
    wordAllocateContext [2, 0, 1] =
      some { vars := [(2, 4), (0, 2), (1, 3)] } := by
  rfl

theorem wordAllocateContextWithClashes_examples :
    wordAllocateContextWithClashes [0, 1, 28]
        [(0, 1), (1, 28)] =
      some { vars := [(28, 2), (1, 3), (0, 2)] } := by
  rfl

theorem wordAllocateVarsWithClashes_safe_example :
    wordAllocateVarsWithClashes [0, 1]
        [(0, 1)] = some [(1, 3), (0, 2)] := by
  rfl

end Flapjack
