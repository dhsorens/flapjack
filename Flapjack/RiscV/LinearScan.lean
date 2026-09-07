import Flapjack.RiscV.Allocator

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

def wordFixLiveTree (tree : WordLiveTree) : WordLiveTree :=
  let live := wordGetLiveBackward tree []
  if live.isEmpty then tree else .seq (.writes live) tree

end Flapjack
