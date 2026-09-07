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
