import Flapjack.RiscV.LinearScan

/-!
# Source-faithful linear-scan checks

This file contains the small executable checks that surround CakeML's
linear-scan allocator.  They are kept separate from the allocator state
machine: the latter can be used independently, while these predicates are
also useful when checking interval constructions and future two-pass proofs.
-/

namespace Flapjack

/-! CakeML's `fix_domination` makes values live at the beginning of a tree when
the backwards scan finds a non-empty incoming live set. -/
def wordFixDomination (tree : WordLiveTree) : WordLiveTree :=
  let live := wordGetLiveBackward tree []
  if live.isEmpty then tree else .seq (.writes live) tree

/-! The source allocator renumbers variables before putting them in its
linear-scan arrays.  Physical variables keep their names, stack variables
start at 3 and advance by four, and allocatable variables start at 1 and also
advance by four. -/
structure WordLinearScanBijectionState where
  toNode : NatInfoMap Nat
  fromNode : NatInfoMap Nat
  maxName : Nat
  nextStack : Nat
  nextAlloc : Nat
  deriving DecidableEq, Repr

def wordLinearScanBijectionInitial : WordLinearScanBijectionState :=
  { toNode := []
    fromNode := []
    maxName := 0
    nextStack := 3
    nextAlloc := 1 }

def wordLinearScanBijectionStep (state : WordLinearScanBijectionState)
    (register : Nat) : WordLinearScanBijectionState :=
  if (lookupNatInfo register state.toNode).isSome then
    state
  else if register % 2 == 0 then
    { state with
      toNode := (register, register) :: state.toNode
      fromNode := (register, register) :: state.fromNode
      maxName := max register state.maxName }
  else if register % 4 == 3 then
    { state with
      toNode := (register, state.nextStack) :: state.toNode
      fromNode := (state.nextStack, register) :: state.fromNode
      maxName := max state.nextStack state.maxName
      nextStack := state.nextStack + 4 }
  else
    { state with
      toNode := (register, state.nextAlloc) :: state.toNode
      fromNode := (state.nextAlloc, register) :: state.fromNode
      maxName := max state.nextAlloc state.maxName
      nextAlloc := state.nextAlloc + 4 }

def wordLinearScanBijectionList (state : WordLinearScanBijectionState)
    (registers : List Nat) : WordLinearScanBijectionState :=
  registers.foldl wordLinearScanBijectionStep state

def wordLinearScanBijectionTree : WordClashTree →
    WordLinearScanBijectionState → WordLinearScanBijectionState
  | .delta writes reads, state =>
      wordLinearScanBijectionList
        (wordLinearScanBijectionList state reads) writes
  | .set names, state => wordLinearScanBijectionList state names
  | .branch branchLive thenBranch elseBranch, state =>
      let state := wordLinearScanBijectionTree thenBranch state
      let state := wordLinearScanBijectionTree elseBranch state
      match branchLive with
      | none => state
      | some names => wordLinearScanBijectionList state names
  | .seq first second, state =>
      wordLinearScanBijectionTree second
        (wordLinearScanBijectionTree first state)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLinearScanBijection (tree : WordClashTree) :
    WordLinearScanBijectionState :=
  wordLinearScanBijectionTree tree wordLinearScanBijectionInitial

def wordLinearScanBijectionLookup
    (bijection : WordLinearScanBijectionState) (register : Nat) : Nat :=
  match lookupNatInfo register bijection.toNode with
  | some node => node
  | none => 0

def wordLinearScanApplyBijectionTree : WordClashTree →
    WordLinearScanBijectionState → WordClashTree
  | .delta writes reads, bijection =>
      .delta (writes.map (wordLinearScanBijectionLookup bijection))
        (reads.map (wordLinearScanBijectionLookup bijection))
  | .set names, bijection =>
      .set (names.map (wordLinearScanBijectionLookup bijection))
  | .branch branchLive thenBranch elseBranch, bijection =>
      .branch (branchLive.map
        (List.map (wordLinearScanBijectionLookup bijection)))
        (wordLinearScanApplyBijectionTree thenBranch bijection)
        (wordLinearScanApplyBijectionTree elseBranch bijection)
  | .seq first second, bijection =>
      .seq (wordLinearScanApplyBijectionTree first bijection)
        (wordLinearScanApplyBijectionTree second bijection)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLinearScanApplyBijectionForced
    (bijection : WordLinearScanBijectionState) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (left, right) :: edges =>
      (wordLinearScanBijectionLookup bijection left,
        wordLinearScanBijectionLookup bijection right) ::
        wordLinearScanApplyBijectionForced bijection edges

def wordLinearScanApplyBijectionMoves
    (bijection : WordLinearScanBijectionState) : List WordMove → List WordMove
  | [] => []
  | move :: moves =>
      { move with
        left := wordLinearScanBijectionLookup bijection move.left
        right := wordLinearScanBijectionLookup bijection move.right } ::
        wordLinearScanApplyBijectionMoves bijection moves

def wordLinearScanBijectionSources
    (bijection : WordLinearScanBijectionState) : List Nat :=
  bijection.toNode.map Prod.fst

def wordLinearScanStepWithRules (spillStack physicalLimit : Bool)
    (forbidden preferred : List Nat) (register : Nat)
    (beginning ending : Int) (force : Bool)
    (state : WordLinearScanState) : WordLinearScanState :=
  let state := wordLinearScanReleaseInactive beginning state
  if spillStack && register % 4 == 3 then
    wordLinearScanSpill register state
  else if physicalLimit && register % 2 == 0 &&
      register ≥ 2 * state.maxColours then
    wordLinearScanSpill register state
  else
    let forbidden :=
      if register % 2 == 0 then
        wordListUnion state.physicalColours forbidden
      else
        forbidden
    let (state, colour) := wordLinearScanFindColour state forbidden preferred
    match colour with
    | some colour => wordLinearScanColourRegister register colour ending state
    | none => wordLinearScanFindSpill forbidden register ending force state

def wordLinearScanAdjacencyUpdate (register : Nat) (neighbours : List Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  (register, neighbours) :: adjacency.filter (fun entry => entry.1 != register)

def wordLinearScanAdjacencyAdd (left right : Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  let leftNeighbours :=
    match lookupNatInfo left adjacency with
    | some neighbours => neighbours
    | none => []
  let rightNeighbours :=
    match lookupNatInfo right adjacency with
    | some neighbours => neighbours
    | none => []
  wordLinearScanAdjacencyUpdate right
    (wordListUnion [left] rightNeighbours)
    (wordLinearScanAdjacencyUpdate left
      (wordListUnion [right] leftNeighbours) adjacency)

def wordLinearScanAdjacency : List (Nat × Nat) → NatInfoMap (List Nat)
  | [] => []
  | (left, right) :: edges =>
      wordLinearScanAdjacencyAdd left right
        (wordLinearScanAdjacency edges)

def wordLinearScanAdjacencyColours (adjacency : NatInfoMap (List Nat))
    (state : WordLinearScanState) (register : Nat) : List Nat :=
  match lookupNatInfo register adjacency with
  | some neighbours => wordLinearScanColoursOf state neighbours
  | none => []

def wordLinearScanPass1Step (forced moves : NatInfoMap (List Nat))
    (register : Nat) (beginnings endings : NatInfoMap Int)
    (state : WordLinearScanState) : Option WordLinearScanState :=
  match lookupNatInfo register beginnings, lookupNatInfo register endings with
  | some beginning, some ending =>
      let forcedColours := wordLinearScanAdjacencyColours forced state register
      let preferredColours := wordLinearScanAdjacencyColours moves state register
      some (if register % 2 == 0 then
        wordLinearScanStepWithRules true true forcedColours [] register
          beginning ending true state
      else
        wordLinearScanStepWithRules true true forcedColours preferredColours register
          beginning ending false state)
  | _, _ => none

def wordLinearScanPass2Step (forced moves : NatInfoMap (List Nat))
    (register : Nat) (beginnings endings : NatInfoMap Int)
    (state : WordLinearScanState) : Option WordLinearScanState :=
  match lookupNatInfo register beginnings, lookupNatInfo register endings with
  | some beginning, some ending =>
      let forcedColours := wordLinearScanAdjacencyColours forced state register
      let preferredColours := wordLinearScanAdjacencyColours moves state register
      some (if register % 2 == 0 then
        wordLinearScanStepWithRules false false forcedColours [] register
          beginning ending false state
      else
        wordLinearScanStepWithRules false false forcedColours preferredColours register
          beginning ending false state)
  | _, _ => none

def wordLinearScanPass1 : NatInfoMap (List Nat) → NatInfoMap (List Nat) →
    List Nat → NatInfoMap Int → NatInfoMap Int →
    WordLinearScanState → Option WordLinearScanState
  | _, _, [], _, _, state => some state
  | forced, moves, register :: registers, beginnings, endings, state => do
      let state ← wordLinearScanPass1Step forced moves register beginnings endings state
      wordLinearScanPass1 forced moves registers beginnings endings state

def wordLinearScanStackRegisters (colours : Nat) :
    List Nat → WordLinearScanState → Option (List Nat)
  | [], _ => some []
  | register :: registers, state => do
      let colour ← lookupNatInfo register state.colours
      let rest ← wordLinearScanStackRegisters colours registers state
      if register % 4 == 3 || colours ≤ colour then
        some (register :: rest)
      else
        some rest

def wordLinearScanFilterAdjacency (registers : List Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  adjacency.map (fun entry =>
    (entry.1, entry.2.filter (fun register => register ∈ registers)))

def wordLinearScanPass2 : NatInfoMap (List Nat) → NatInfoMap (List Nat) →
    List Nat → NatInfoMap Int → NatInfoMap Int →
    WordLinearScanState → Option WordLinearScanState
  | _, _, [], _, _, state => some state
  | forced, moves, register :: registers, beginnings, endings, state => do
      let state ← wordLinearScanPass2Step forced moves register beginnings endings state
      wordLinearScanPass2 forced moves registers beginnings endings state

def wordLinearScanExchangeUpdate (colour replacement : Nat)
    (exchange : NatInfoMap Nat) : NatInfoMap Nat :=
  (colour, replacement) :: exchange.filter (fun entry => entry.1 != colour)

def wordLinearScanExchangeLookup (exchange : NatInfoMap Nat)
    (colour : Nat) : Nat :=
  match lookupNatInfo colour exchange with
  | some replacement => replacement
  | none => colour

def wordLinearScanFindRegExchangeAux
    (state : WordLinearScanState) : List Nat → NatInfoMap Nat →
    NatInfoMap Nat → NatInfoMap Nat × NatInfoMap Nat
  | [], exchange, inverse => (exchange, inverse)
  | register :: registers, exchange, inverse =>
      let colour :=
        match lookupNatInfo register state.colours with
        | some colour => colour
        | none => 0
      let fixedColour := register / 2
      let exchangedColour := wordLinearScanExchangeLookup inverse fixedColour
      let fixedExchangedColour := wordLinearScanExchangeLookup exchange colour
      let exchange := wordLinearScanExchangeUpdate colour fixedColour
        (wordLinearScanExchangeUpdate exchangedColour fixedExchangedColour exchange)
      let inverse := wordLinearScanExchangeUpdate fixedColour colour
        (wordLinearScanExchangeUpdate fixedExchangedColour exchangedColour inverse)
      wordLinearScanFindRegExchangeAux state registers exchange inverse

def wordLinearScanFindRegExchange (registers : List Nat)
    (state : WordLinearScanState) : NatInfoMap Nat × NatInfoMap Nat :=
  wordLinearScanFindRegExchangeAux state registers [] []

def wordLinearScanApplyColourExchange (exchange : NatInfoMap Nat)
    (state : WordLinearScanState) : WordLinearScanState :=
  { state with colours := state.colours.map (fun entry =>
      (entry.1, wordLinearScanExchangeLookup exchange entry.2)) }

def wordLinearScanApplyRegisterExchange (registers : List Nat)
    (state : WordLinearScanState) : WordLinearScanState :=
  let (exchange, _) := wordLinearScanFindRegExchange registers state
  wordLinearScanApplyColourExchange exchange state

/-! Source-shaped two-pass entry point.  The register list is expected to be
in interval-start order, as it is after CakeML's sorting pass. -/
def wordLinearScanTwoPass (colours : Nat)
    (forced moves : List (Nat × Nat)) (registers : List Nat)
    (beginnings endings : NatInfoMap Int) :
    Option (WordLinearScanState × List Nat × WordLinearScanState) := do
  let forcedAdjacency := wordLinearScanAdjacency forced
  let moveAdjacency := wordLinearScanAdjacency moves
  let firstRaw ← wordLinearScanPass1 forcedAdjacency moveAdjacency registers
    beginnings endings
    { (wordLinearScanInitialState colours colours) with
      nextSpill := colours }
  let firstPhysical := registers.filter (fun register =>
    register % 2 == 0 && register < 2 * colours)
  let first := wordLinearScanApplyRegisterExchange firstPhysical firstRaw
  let stackRegisters ← wordLinearScanStackRegisters colours registers first
  let secondRaw ← wordLinearScanPass2
    (wordLinearScanFilterAdjacency stackRegisters forcedAdjacency)
    (wordLinearScanFilterAdjacency stackRegisters moveAdjacency)
    stackRegisters beginnings endings
    { (wordLinearScanInitialState (colours + stackRegisters.length) (colours + stackRegisters.length)) with
      nextColour := colours
      nextSpill := colours + stackRegisters.length }
  let secondPhysical := stackRegisters.filter (fun register =>
    register % 2 == 0 && 2 * colours ≤ register)
  let second := wordLinearScanApplyRegisterExchange secondPhysical secondRaw
  pure (first, stackRegisters, second)

def wordLinearScanRegisterPrecedes (beginnings : NatInfoMap Int)
    (register head : Nat) : Bool :=
  match lookupNatInfo register beginnings, lookupNatInfo head beginnings with
  | some registerBeginning, some headBeginning =>
      registerBeginning < headBeginning ||
        (registerBeginning == headBeginning && register ≤ head)
  | some _, none => true
  | none, _ => false

def wordLinearScanInsertRegisterSource (beginnings : NatInfoMap Int)
    (register : Nat) : List Nat → List Nat
  | [] => [register]
  | head :: tail =>
      if wordLinearScanRegisterPrecedes beginnings register head then
        register :: head :: tail
      else
        head :: wordLinearScanInsertRegisterSource beginnings register tail
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanSortRegistersSource (beginnings : NatInfoMap Int) :
    List Nat → List Nat
  | [] => []
  | register :: registers =>
      wordLinearScanInsertRegisterSource beginnings register
        (wordLinearScanSortRegistersSource beginnings registers)
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanInsertMoveSource (move : WordMove) : List WordMove → List WordMove
  | [] => [move]
  | head :: moves =>
      if move.priority < head.priority then
        move :: head :: moves
      else
        head :: wordLinearScanInsertMoveSource move moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordLinearScanSortMovesSource : List WordMove → List WordMove
  | [] => []
  | move :: moves =>
      wordLinearScanInsertMoveSource move
        (wordLinearScanSortMovesSource moves)
  termination_by moves => sizeOf moves
  decreasing_by all_goals decreasing_trivial

def wordLinearScanBijectionNodes
    (bijection : WordLinearScanBijectionState) : List Nat :=
  bijection.toNode.map Prod.snd

def wordLinearScanExtractColouring
    (fromNode : NatInfoMap Nat) (registers : List Nat)
    (colours : NatInfoMap Nat) : NatInfoMap Nat → NatInfoMap Nat
  | colouring =>
      match registers with
      | [] => colouring
      | register :: registers =>
          let source :=
            match lookupNatInfo register fromNode with
            | some source => source
            | none => 0
          let colour :=
            match lookupNatInfo register colours with
            | some colour => colour
            | none => 0
          wordLinearScanExtractColouring fromNode registers colours
            ((source, colour) :: colouring.filter (fun entry => entry.1 != source))

def wordGetIntervalsCtAux : WordClashTree → Int → NatInfoMap Int →
    NatInfoMap Int → List Nat →
    Int × NatInfoMap Int × NatInfoMap Int × List Nat
  | .delta writes reads, number, beginnings, endings, live =>
      (number - 2,
        wordIntervalAddIfLt writes number beginnings,
        wordIntervalAddIfGt reads (number - 1)
          (wordIntervalAddIfGt writes number endings),
        wordListUnion reads (wordNumSetDelete writes live))
  | .set names, number, beginnings, endings, live =>
      (number - 1, beginnings,
        wordIntervalAddIfGt names number endings,
        wordListUnion names live)
  | .branch branchLive thenBranch elseBranch, number, beginnings, endings, live =>
      let (elseNumber, elseBeginnings, elseEndings, elseLive) :=
        wordGetIntervalsCtAux elseBranch number beginnings endings live
      let (thenNumber, thenBeginnings, thenEndings, thenLive) :=
        wordGetIntervalsCtAux thenBranch elseNumber elseBeginnings elseEndings elseLive
      match branchLive with
      | none =>
          (thenNumber, thenBeginnings, thenEndings,
            wordListUnion thenLive elseLive)
      | some names =>
          (thenNumber - 1, thenBeginnings,
            wordIntervalAddIfGt names thenNumber thenEndings,
            wordListUnion names (wordListUnion thenLive elseLive))
  | .seq first second, number, beginnings, endings, live =>
      let (secondNumber, secondBeginnings, secondEndings, secondLive) :=
        wordGetIntervalsCtAux second number beginnings endings live
      wordGetIntervalsCtAux first secondNumber secondBeginnings secondEndings secondLive
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordGetIntervalsCt (tree : WordClashTree) :
    Int × NatInfoMap Int × NatInfoMap Int :=
  let (number, beginnings, endings, live) :=
    wordGetIntervalsCtAux tree 0 [] [] []
  (number - 1,
    wordIntervalAddIfLt live number beginnings,
    wordIntervalAddIfGt live number endings)

structure WordLinearScanSourceAllocation where
  bijection : WordLinearScanBijectionState
  normalizedTree : WordClashTree
  normalizedRegisters : List Nat
  stackRegisters : List Nat
  firstPass : WordLinearScanState
  secondPass : WordLinearScanState
  colouring : NatInfoMap Nat
  deriving Repr

/-! Composition of the source preprocessing and both linear-scan passes.  The
result retains intermediate witnesses so later correctness layers can state
their invariants without reconstructing the allocator run. -/
def wordLinearScanAllocateSource (colours : Nat)
    (forced : List (Nat × Nat)) (moves : List WordMove)
    (tree : WordClashTree) :
    Option WordLinearScanSourceAllocation := do
  let bijection := wordLinearScanBijection tree
  let normalizedTree := wordLinearScanApplyBijectionTree tree bijection
  let normalizedForced :=
    wordLinearScanApplyBijectionForced bijection forced
  let normalizedMoves :=
    wordLinearScanApplyBijectionMoves bijection moves
  let (_, beginnings, endings) := wordGetIntervalsCt normalizedTree
  let normalizedRegisters := wordLinearScanSortRegistersSource beginnings
    (wordLinearScanBijectionNodes bijection)
  let normalizedMoves := wordLinearScanSortMovesSource normalizedMoves
  let normalizedMovePairs := normalizedMoves.map (fun move => (move.left, move.right))
  let (firstPass, stackRegisters, secondPass) ← wordLinearScanTwoPass colours
    normalizedForced normalizedMovePairs normalizedRegisters beginnings endings
  let colouring := wordLinearScanExtractColouring bijection.fromNode
    normalizedRegisters secondPass.colours []
  pure
    { bijection := bijection
      normalizedTree := normalizedTree
      normalizedRegisters := normalizedRegisters
      stackRegisters := stackRegisters
      firstPass := firstPass
      secondPass := secondPass
      colouring := colouring }

/-! A direct executable port of `check_number_property`.  The property is
passed as a Boolean predicate so this remains suitable for native evaluation
in the same way as the source allocator's checks. -/
def wordCheckNumberProperty (property : Int → List Nat → Bool) :
    WordLiveTree → Int → List Nat → Bool
  | .writes names, number, live =>
      property (number - 1) (wordNumSetDelete names live)
  | .reads names, number, live =>
      property (number - 1) (wordListUnion names live)
  | .branch thenBranch elseBranch, number, live =>
      wordCheckNumberProperty property elseBranch number live &&
        wordCheckNumberProperty property thenBranch
          (number - Int.ofNat (wordLiveTreeSize elseBranch)) live
  | .seq first second, number, live =>
      wordCheckNumberProperty property second number live &&
        wordCheckNumberProperty property first
          (number - Int.ofNat (wordLiveTreeSize second))
          (wordGetLiveBackward second live)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

/-! The stronger source check additionally tests the live set at a branch's
entry. -/
def wordCheckNumberPropertyStrong (property : Int → List Nat → Bool) :
    WordLiveTree → Int → List Nat → Bool
  | .writes names, number, live =>
      property (number - 1) (wordNumSetDelete names live)
  | .reads names, number, live =>
      property (number - 1) (wordListUnion names live)
  | .branch thenBranch elseBranch, number, live =>
      let thenResult := wordCheckNumberPropertyStrong property thenBranch
        (number - Int.ofNat (wordLiveTreeSize elseBranch)) live
      let elseResult := wordCheckNumberPropertyStrong property elseBranch number live
      thenResult && elseResult &&
        property
          (number - Int.ofNat (wordLiveTreeSize (.branch thenBranch elseBranch)))
          (wordGetLiveBackward (.branch thenBranch elseBranch) live)
  | .seq first second, number, live =>
      wordCheckNumberPropertyStrong property second number live &&
        wordCheckNumberPropertyStrong property first
          (number - Int.ofNat (wordLiveTreeSize second))
          (wordGetLiveBackward second live)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordCheckStartLiveNames (names : List Nat) (number : Int)
    (beginnings endings : NatInfoMap Int) (defaultBeginning : Int) : Bool :=
  match names with
  | [] => true
  | name :: names =>
      let beginning :=
        match lookupNatInfo name beginnings with
        | some value => value
        | none => defaultBeginning
      let hasEnd := (lookupNatInfo name endings).isSome
      let endCondition :=
        match lookupNatInfo name endings with
        | some value => number ≤ value
        | none => false
      defaultBeginning ≤ beginning && beginning ≤ number &&
        hasEnd && endCondition &&
        wordCheckStartLiveNames names number beginnings endings defaultBeginning

/-! Executable port of CakeML's `check_startlive_prop`. -/
def wordCheckStartLive : WordLiveTree → Int → NatInfoMap Int → NatInfoMap Int →
    Int → Bool
  | .writes names, number, beginnings, endings, defaultBeginning =>
      wordCheckStartLiveNames names number beginnings endings defaultBeginning
  | .reads _, _, _, _, _ => true
  | .branch thenBranch elseBranch, number, beginnings, endings, defaultBeginning =>
      wordCheckStartLive elseBranch number beginnings endings defaultBeginning &&
        wordCheckStartLive thenBranch
          (number - Int.ofNat (wordLiveTreeSize elseBranch))
          beginnings endings defaultBeginning
  | .seq first second, number, beginnings, endings, defaultBeginning =>
      wordCheckStartLive second number beginnings endings defaultBeginning &&
        wordCheckStartLive first
          (number - Int.ofNat (wordLiveTreeSize second))
          beginnings endings defaultBeginning
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordPointInsideInterval (interval : Int × Int) (number : Int) : Bool :=
  interval.1 ≤ number && number ≤ interval.2

def wordCheckIntervalPair (colour : Nat → Nat)
    (beginnings endings : NatInfoMap Int) (left right : Nat) : Bool :=
  match lookupNatInfo left beginnings, lookupNatInfo left endings,
      lookupNatInfo right beginnings, lookupNatInfo right endings with
  | some leftBeginning, some leftEnding, some rightBeginning, some rightEnding =>
      if wordIntervalIntersect (leftBeginning, leftEnding) (rightBeginning, rightEnding) &&
          colour left == colour right then
        left == right
      else
        true
  | _, _, _, _ => true

def wordCheckIntervalPairs (colour : Nat → Nat)
    (beginnings endings : NatInfoMap Int) (left : Nat) : List Nat → Bool
  | [] => true
  | right :: rights =>
      wordCheckIntervalPair colour beginnings endings left right &&
        wordCheckIntervalPairs colour beginnings endings left rights

/-! Executable port of `check_intervals`: overlapping intervals with equal
colours must belong to the same source register. -/
def wordCheckIntervals (colour : Nat → Nat)
    (beginnings endings : NatInfoMap Int) : Bool :=
  match beginnings with
  | [] => true
  | (left, _) :: rest =>
      wordCheckIntervalPairs colour beginnings endings left
        (beginnings.map Prod.fst) &&
        wordCheckIntervals colour rest endings

end Flapjack
