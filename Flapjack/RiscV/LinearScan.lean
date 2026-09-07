import Flapjack.RiscV.RegAlloc

/-!
# Linear-scan live trees

CakeML's linear-scan allocator consumes a second view of the clash tree.  The
ordinary graph allocator works with writes and reads at each `Delta`, while
linear scan records the points at which values become live and dead.  This
module ports that structural boundary and its executable checks; interval
construction and register assignment build on it in a later slice.
-/

namespace Flapjack

inductive WordLiveTree where
  | writes (names : List Nat)
  | reads (names : List Nat)
  | branch (thenBranch elseBranch : WordLiveTree)
  | seq (first second : WordLiveTree)
  deriving DecidableEq, Repr

/-! Translate the source clash-tree constructors to the live-tree view used by
CakeML's `linear_scan$check_live_tree` and interval analysis. -/
def wordGetLiveTree : WordClashTree → WordLiveTree
  | .delta writes reads =>
      .seq (.reads reads) (.writes writes)
  | .set names =>
      .reads names
  | .branch branchLive thenBranch elseBranch =>
      let branches := .branch (wordGetLiveTree thenBranch)
        (wordGetLiveTree elseBranch)
      match branchLive with
      | none => branches
      | some names => .seq (.reads names) branches
  | .seq first second =>
      .seq (wordGetLiveTree first) (wordGetLiveTree second)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLiveDifference (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∉ right)

def wordGetLiveBackward : WordLiveTree → List Nat → List Nat
  | .writes names, live => wordNumSetDelete names live
  | .reads names, live => wordListUnion names live
  | .branch thenBranch elseBranch, live =>
      let thenLive := wordGetLiveBackward thenBranch live
      let elseLive := wordGetLiveBackward elseBranch live
      wordListUnion (wordLiveDifference elseLive thenLive) thenLive
  | .seq first second, live =>
      wordGetLiveBackward first (wordGetLiveBackward second live)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLiveTreeRegisters : WordLiveTree → List Nat
  | .writes names | .reads names => names.eraseDups
  | .branch thenBranch elseBranch =>
      wordListUnion (wordLiveTreeRegisters thenBranch)
        (wordLiveTreeRegisters elseBranch)
  | .seq first second =>
      wordListUnion (wordLiveTreeRegisters first)
        (wordLiveTreeRegisters second)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLiveTreeSize : WordLiveTree → Nat
  | .writes _ | .reads _ => 1
  | .branch thenBranch elseBranch =>
      wordLiveTreeSize thenBranch + wordLiveTreeSize elseBranch
  | .seq first second => wordLiveTreeSize first + wordLiveTreeSize second
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

/-! Interval maps use the same update discipline as CakeML's
`numset_list_add_if`: starts retain the smallest position seen, while ends
retain the largest.  The position counter is an `Int`, matching the source
development's backwards scan and avoiding an artificial lower bound. -/
def wordIntervalUpdate (name : Nat) (value : Int)
    (intervals : NatInfoMap Int) : NatInfoMap Int :=
  (name, value) :: intervals.filter (fun entry => entry.1 != name)

def wordIntervalAddIf (names : List Nat) (value : Int)
    (intervals : NatInfoMap Int) (predicate : Int → Int → Bool) :
    NatInfoMap Int :=
  match names with
  | [] => intervals
  | name :: names =>
      match lookupNatInfo name intervals with
      | some previous =>
          if predicate value previous then
            wordIntervalAddIf names value
              (wordIntervalUpdate name value intervals) predicate
          else
            wordIntervalAddIf names value intervals predicate
      | none =>
          wordIntervalAddIf names value
            (wordIntervalUpdate name value intervals) predicate

def wordIntervalAddIfLt (names : List Nat) (value : Int)
    (intervals : NatInfoMap Int) : NatInfoMap Int :=
  wordIntervalAddIf names value intervals (fun current previous =>
    current < previous)

def wordIntervalAddIfGt (names : List Nat) (value : Int)
    (intervals : NatInfoMap Int) : NatInfoMap Int :=
  wordIntervalAddIf names value intervals (fun current previous =>
    previous ≤ current)

def wordGetIntervals : WordLiveTree → Int → NatInfoMap Int →
    NatInfoMap Int → Int × NatInfoMap Int × NatInfoMap Int
  | .writes names, position, beginnings, endings =>
      (position - 1,
        wordIntervalAddIfLt names position beginnings,
        wordIntervalAddIfGt names position endings)
  | .reads names, position, beginnings, endings =>
      (position - 1, beginnings,
        wordIntervalAddIfGt names position endings)
  | .branch thenBranch elseBranch, position, beginnings, endings =>
      let (position, beginnings, endings) :=
        wordGetIntervals elseBranch position beginnings endings
      wordGetIntervals thenBranch position beginnings endings
  | .seq first second, position, beginnings, endings =>
      let (position, beginnings, endings) :=
        wordGetIntervals second position beginnings endings
      wordGetIntervals first position beginnings endings
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordIntervalIntersect (left right : Int × Int) : Bool :=
  left.1 ≤ right.2 && right.1 ≤ left.2

/-! The executable state used by CakeML's two-pass linear allocator.  Colours
are compressed allocator colours; `wordLinearScanLocations` turns them into
the even RISC-V registers used by the Word backend. -/
structure WordLinearScanState where
  active : List (Int × Nat)
  colorPool : List Nat
  physicalColours : List Nat
  nextColour : Nat
  maxColours : Nat
  nextSpill : Nat
  colours : NatInfoMap Nat
  locations : NatInfoMap WordLocation
  deriving DecidableEq, Repr

def wordLinearScanUpdateColour (register colour : Nat)
    (colours : NatInfoMap Nat) : NatInfoMap Nat :=
  (register, colour) :: colours.filter (fun entry => entry.1 != register)

def wordLinearScanInsertActive (interval : Int × Nat) :
    List (Int × Nat) → List (Int × Nat)
  | [] => [interval]
  | head :: tail =>
      if interval.1 ≤ head.1 then
        interval :: head :: tail
      else
        head :: wordLinearScanInsertActive interval tail
termination_by active => sizeOf active
decreasing_by all_goals decreasing_trivial

def wordLinearScanReleaseInactiveAux (beginning : Int)
    (colours : NatInfoMap Nat) :
    List (Int × Nat) → List Nat → List (Int × Nat) × List Nat
  | [], pool => ([], pool)
  | (ending, register) :: active, pool =>
      if ending < beginning then
        let pool := match lookupNatInfo register colours with
          | some colour => colour :: pool
          | none => pool
        wordLinearScanReleaseInactiveAux beginning colours active pool
      else
        ((ending, register) :: active, pool)
termination_by active => sizeOf active
decreasing_by all_goals decreasing_trivial

def wordLinearScanReleaseInactive (beginning : Int)
    (state : WordLinearScanState) : WordLinearScanState :=
  let (active, pool) := wordLinearScanReleaseInactiveAux beginning
    state.colours state.active state.colorPool
  { state with active := active, colorPool := pool }

def wordLinearScanTakeAvailable : List Nat → List Nat →
    Option (Nat × List Nat)
  | [], _ => none
  | colour :: colours, forbidden =>
      if colour ∈ forbidden then
        wordLinearScanTakeAvailable colours forbidden |>.map
          (fun result => (result.1, colour :: result.2))
      else
        some (colour, colours)

def wordLinearScanFreshColour (state : WordLinearScanState) :
    WordLinearScanState × Option Nat :=
  if state.nextColour < state.maxColours then
    ({ state with nextColour := state.nextColour + 1 }, some state.nextColour)
  else
    (state, none)

def wordLinearScanFindColour (state : WordLinearScanState)
    (forbidden preferred : List Nat) :
    WordLinearScanState × Option Nat :=
  let preferred := preferred.filter (fun colour => colour ∈ state.colorPool)
  match wordLinearScanTakeAvailable preferred forbidden with
  | some (colour, _) =>
      let pool := state.colorPool.filter (fun candidate => candidate != colour)
      ({ state with colorPool := pool }, some colour)
  | none =>
      match wordLinearScanTakeAvailable state.colorPool forbidden with
      | some (colour, pool) =>
          ({ state with colorPool := pool }, some colour)
      | none => wordLinearScanFreshColour state

def wordLinearScanSpill (register : Nat) (state : WordLinearScanState) :
    WordLinearScanState :=
  { state with
    nextSpill := state.nextSpill + 1
    colours := wordLinearScanUpdateColour register state.nextSpill state.colours
    locations := (register, .stack state.nextSpill) ::
      state.locations.filter (fun entry => entry.1 != register) }

def wordLinearScanColourRegister (register colour : Nat) (ending : Int)
    (state : WordLinearScanState) : WordLinearScanState :=
  let physical := register % 2 = 0
  let active := wordLinearScanInsertActive (ending, register) state.active
  let physicalColours :=
    if physical then wordListUnion [colour] state.physicalColours
    else state.physicalColours
  { state with
    active := active
    physicalColours := physicalColours
    colours := wordLinearScanUpdateColour register colour state.colours
    locations := (register, .register (2 * (colour + 1))) ::
      state.locations.filter (fun entry => entry.1 != register) }

def wordLinearScanFindLastStealableAux (forbidden : List Nat)
    (colours : NatInfoMap Nat) :
    List (Int × Nat) →
    Option ((Int × Nat) × List (Int × Nat))
  | [] => none
  | head :: tail =>
      match wordLinearScanFindLastStealableAux forbidden colours tail with
      | some (candidate, rest) => some (candidate, head :: rest)
      | none =>
          let register := head.2
          match lookupNatInfo register colours with
          | some colour =>
              if register % 2 != 0 && colour ∉ forbidden then
                some (head, tail)
              else
                none
          | none => none
termination_by active => sizeOf active
decreasing_by all_goals decreasing_trivial

def wordLinearScanFindLastStealable (forbidden : List Nat)
    (state : WordLinearScanState) :
    Option ((Int × Nat) × List (Int × Nat)) :=
  wordLinearScanFindLastStealableAux forbidden state.colours state.active

def wordLinearScanFindSpill (forbidden : List Nat) (register : Nat)
    (ending : Int) (force : Bool) (state : WordLinearScanState) :
    WordLinearScanState :=
  match wordLinearScanFindLastStealable forbidden state with
  | some ((stealEnding, stealRegister), active) =>
      if force || ending < stealEnding then
        match lookupNatInfo stealRegister state.colours with
        | some colour =>
            let state := wordLinearScanSpill stealRegister
              { state with active := active }
            wordLinearScanColourRegister register colour ending state
        | none => wordLinearScanSpill register state
      else
        wordLinearScanSpill register state
  | none => wordLinearScanSpill register state

def wordLinearScanStep (forbidden preferred : List Nat)
    (register : Nat) (beginning ending : Int) (force : Bool)
    (state : WordLinearScanState) : WordLinearScanState :=
  let state := wordLinearScanReleaseInactive beginning state
  if register % 4 = 3 then
    wordLinearScanSpill register state
  else if register % 2 = 0 && register ≥ 2 * state.maxColours then
    wordLinearScanSpill register state
  else
    let forbidden :=
      if register % 2 = 0 then
        wordListUnion state.physicalColours forbidden
      else
        forbidden
    let (state, colour) := wordLinearScanFindColour state forbidden preferred
    match colour with
    | some colour => wordLinearScanColourRegister register colour ending state
    | none => wordLinearScanFindSpill forbidden register ending force state

def wordLinearScanInsertByBeginning (beginnings : NatInfoMap Int)
    (register : Nat) : List Nat → List Nat
  | [] => [register]
  | head :: tail =>
      match lookupNatInfo register beginnings,
        lookupNatInfo head beginnings with
      | some registerBeginning, some headBeginning =>
          if registerBeginning ≤ headBeginning then
            register :: head :: tail
          else
            head :: wordLinearScanInsertByBeginning beginnings register tail
      | some _, none => register :: head :: tail
      | none, _ =>
          head :: wordLinearScanInsertByBeginning beginnings register tail
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanSortRegisters (beginnings : NatInfoMap Int) :
    List Nat → List Nat
  | [] => []
  | register :: registers =>
      wordLinearScanInsertByBeginning beginnings register
        (wordLinearScanSortRegisters beginnings registers)
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanAllocateRegisters
    (forbidden : Nat → List Nat) (preferred : Nat → List Nat)
    : List Nat → (NatInfoMap Int) → (NatInfoMap Int) →
    WordLinearScanState → Option WordLinearScanState
  | [], _, _, state => some state
  | register :: registers, beginnings, endings, state =>
      match lookupNatInfo register beginnings,
        lookupNatInfo register endings with
      | some beginning, some ending =>
          let state := wordLinearScanStep
            (forbidden register) (preferred register)
            register beginning ending false state
          wordLinearScanAllocateRegisters forbidden preferred registers
            beginnings endings state
      | _, _ => none
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanEdgeNames (register : Nat) :
    List (Nat × Nat) → List Nat
  | [] => []
  | (left, right) :: edges =>
      if left == register then
        right :: wordLinearScanEdgeNames register edges
      else if right == register then
        left :: wordLinearScanEdgeNames register edges
      else
        wordLinearScanEdgeNames register edges

def wordLinearScanColoursOf (state : WordLinearScanState) :
    List Nat → List Nat
  | [] => []
  | register :: registers =>
      match lookupNatInfo register state.colours with
      | some colour => colour :: wordLinearScanColoursOf state registers
      | none => wordLinearScanColoursOf state registers

def wordLinearScanForcedColours (forced : List (Nat × Nat))
    (register : Nat) (state : WordLinearScanState) : List Nat :=
  wordLinearScanColoursOf state
    (wordLinearScanEdgeNames register forced)

def wordLinearScanPreferredColours (moves : List WordMove)
    (register : Nat) (state : WordLinearScanState) : List Nat :=
  wordLinearScanColoursOf state
    ((moves.flatMap (fun move =>
      if move.left == register then
        [move.right]
      else if move.right == register then
        [move.left]
      else
        [])))

def wordLinearScanAllocateClashTreeRegisters
    (forced : List (Nat × Nat)) (moves : List WordMove)
    : List Nat → (NatInfoMap Int) → (NatInfoMap Int) →
      WordLinearScanState → Option WordLinearScanState
  | [], _, _, state => some state
  | register :: registers, beginnings, endings, state =>
      match lookupNatInfo register beginnings,
        lookupNatInfo register endings with
      | some beginning, some ending =>
          let state := wordLinearScanStep
            (wordLinearScanForcedColours forced register state)
            (wordLinearScanPreferredColours moves register state)
            register beginning ending (register % 2 == 0) state
          wordLinearScanAllocateClashTreeRegisters forced moves registers
            beginnings endings state
      | _, _ => none
termination_by registers => sizeOf registers
decreasing_by all_goals decreasing_trivial

def wordLinearScanInitialState (colours : Nat) (stackStart : Nat) :
    WordLinearScanState :=
  { active := []
    colorPool := []
    physicalColours := []
    nextColour := 0
    maxColours := colours
    nextSpill := stackStart
    colours := []
    locations := [] }

def wordLinearScanAllocateClashTree (colours stackStart : Nat)
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (moves : List WordMove) : Option WordLinearScanState :=
  let liveTree := wordGetLiveTree tree
  let (_, beginnings, endings) := wordGetIntervals liveTree 0 [] []
  let registers := wordLinearScanSortRegisters beginnings
    (wordLiveTreeRegisters liveTree)
  wordLinearScanAllocateClashTreeRegisters forced moves registers
    beginnings endings (wordLinearScanInitialState colours stackStart)

def wordLinearScanLocations (state : WordLinearScanState) :
    NatInfoMap WordLocation :=
  state.locations

/-! Check a partial colouring while walking a live tree.  The two live lists
are kept in lockstep, with the second one carrying the corresponding colours.
This is the direct executable analogue of CakeML's `check_live_tree`. -/
def wordCheckLiveTree (colour : Nat → Nat) : WordLiveTree →
    List Nat → List Nat → Option (List Nat × List Nat)
  | .writes names, live, flive =>
      match wordCheckPartialColour colour names live flive with
      | none => none
      | some _ =>
          some (wordNumSetDelete names live,
            wordNumSetDelete (names.map colour) flive)
  | .reads names, live, flive =>
      wordCheckPartialColour colour names live flive
  | .branch thenBranch elseBranch, live, flive => do
      let (thenLive, thenFlive) ←
        wordCheckLiveTree colour thenBranch live flive
      let (elseLive, _) ←
        wordCheckLiveTree colour elseBranch live flive
      wordCheckPartialColour colour
        (wordLiveDifference elseLive thenLive) thenLive thenFlive
  | .seq first second, live, flive => do
      let (secondLive, secondFlive) ←
        wordCheckLiveTree colour second live flive
      wordCheckLiveTree colour first secondLive secondFlive
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordLinearScanLocationColour (state : WordLinearScanState) :
    WordLocation → Nat
  | .register register => register
  | .stack slot => 2 * state.maxColours + 1 + slot

def wordLinearScanColourAt (state : WordLinearScanState) (register : Nat) : Nat :=
  match lookupNatInfo register state.locations with
  | some location => wordLinearScanLocationColour state location
  | none => 0

def wordLinearScanLocationsComplete (state : WordLinearScanState) :
    List Nat → Bool
  | [] => true
  | register :: registers =>
      (lookupNatInfo register state.locations).isSome &&
        wordLinearScanLocationsComplete state registers

def wordLinearScanForcedSafe (state : WordLinearScanState) :
    List (Nat × Nat) → Bool
  | [] => true
  | (left, right) :: edges =>
      match lookupNatInfo left state.locations,
        lookupNatInfo right state.locations with
      | some leftLocation, some rightLocation =>
          wordLinearScanLocationColour state leftLocation !=
            wordLinearScanLocationColour state rightLocation &&
            wordLinearScanForcedSafe state edges
      | _, _ => false

def wordLinearScanAllocationSafe (tree : WordClashTree)
    (forced : List (Nat × Nat)) (state : WordLinearScanState) : Bool :=
  let liveTree := wordGetLiveTree tree
  wordLinearScanLocationsComplete state (wordLiveTreeRegisters liveTree) &&
    (wordCheckLiveTree (wordLinearScanColourAt state) liveTree [] []).isSome &&
    wordLinearScanForcedSafe state forced

def wordLinearScanAllocateClashTreeChecked (colours stackStart : Nat)
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (moves : List WordMove) : Option WordLinearScanState :=
  match wordLinearScanAllocateClashTree colours stackStart tree forced moves with
  | some state =>
      if wordLinearScanAllocationSafe tree forced state then
        some state
      else
        none
  | none => none

theorem wordLinearScanAllocateClashTreeChecked_safe
    (colours stackStart : Nat) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (moves : List WordMove)
    (state : WordLinearScanState)
    (halloc :
      wordLinearScanAllocateClashTreeChecked colours stackStart tree forced moves =
        some state) :
    wordLinearScanAllocationSafe tree forced state = true := by
  by_cases hsafe : wordLinearScanAllocationSafe tree forced state = true
  · exact hsafe
  · cases hraw : wordLinearScanAllocateClashTree colours stackStart tree
        forced moves with
    | none =>
        simp [wordLinearScanAllocateClashTreeChecked, hraw] at halloc
    | some allocated =>
        simp [wordLinearScanAllocateClashTreeChecked, hraw] at halloc
        rcases halloc with ⟨hsafeAllocated, heq⟩
        subst state
        exact False.elim (hsafe hsafeAllocated)

def wordFixLiveTree (tree : WordLiveTree) : WordLiveTree :=
  let live := wordGetLiveBackward tree []
  if live.isEmpty then tree else .seq (.writes live) tree

end Flapjack
