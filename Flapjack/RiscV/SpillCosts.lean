import Flapjack.RiscV.Heuristics

/-!
# Spill costs and canonical move priorities

This is the final arithmetic part of CakeML's heuristic allocator boundary.
The source computes spill costs from the five usage counters, canonicalizes
unordered move pairs, groups repeated moves, and then uses the resulting
weighted count as the coalescing priority.
-/

namespace Flapjack

def wordGetSpillCost (counts : WordHeuristicCounts) (isTail : Bool) : Nat :=
  (counts.lhsConst + 2 * counts.lhsReg + 4 * counts.lhsMem +
    2 * counts.rhsReg + 4 * counts.rhsMem) *
    if isTail then 5 else 1

def wordHeuristicSpillCosts (currentFunction : Nat) (program : WordProg α) :
    NatInfoMap Nat :=
  let result := wordHeuristic currentFunction program ([], [])
  result.1.map (fun entry =>
    (entry.1, wordGetSpillCost entry.2 (!result.2.contains entry.1)))

structure WordCanonicalMove where
  count : Nat
  maxPriority : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def wordCanonicalPriorityMove (move : WordMove) : WordMove :=
  if move.left ≤ move.right then move
  else { move with left := move.right, right := move.left }

def wordPriorityMoveBefore (left right : WordMove) : Bool :=
  if left.left = right.left then
    if left.right = right.right then left.priority < right.priority
    else left.right < right.right
  else left.left < right.left

def wordInsertPriorityMove (move : WordMove) : List WordMove → List WordMove
  | [] => [move]
  | head :: moves =>
      if wordPriorityMoveBefore move head then
        move :: head :: moves
      else
        head :: wordInsertPriorityMove move moves

def wordSortPriorityMoves : List WordMove → List WordMove
  | [] => []
  | move :: moves =>
      wordInsertPriorityMove move (wordSortPriorityMoves moves)

def wordCanonicalizeMovesAux (current : WordMove) (count : Nat) :
    List WordMove → List WordCanonicalMove → List WordCanonicalMove
  | [], result =>
      { count := count, maxPriority := current.priority,
        left := current.left, right := current.right } :: result
  | move :: moves, result =>
      if current.left = move.left && current.right = move.right then
        wordCanonicalizeMovesAux
          { current with priority := max current.priority move.priority }
          (count + 1) moves result
      else
        wordCanonicalizeMovesAux move 1 moves
          ({ count := count, maxPriority := current.priority,
             left := current.left, right := current.right } :: result)

def wordCanonicalizeMoves (moves : List WordMove) : List WordCanonicalMove :=
  match wordSortPriorityMoves (moves.map wordCanonicalPriorityMove) with
  | [] => []
  | move :: moves =>
      wordCanonicalizeMovesAux move 1 moves []

def wordCoalesceMoveCost (spillCosts : NatInfoMap Nat)
    (move : WordCanonicalMove) : WordMove :=
  let leftCost := if (lookupNatInfo move.left spillCosts).isSome then 1 else 0
  let rightCost := if (lookupNatInfo move.right spillCosts).isSome then 1 else 0
  { priority := move.count *
      (10 * (move.maxPriority + 1) + leftCost + rightCost)
    left := move.left
    right := move.right }

def wordGetHeuristics (algorithm currentFunction : Nat) (program : WordProg α) :
    List WordMove × Option (NatInfoMap Nat) :=
  let moves := wordProgPrioritizedMoves program
  if algorithm % 2 = 1 then
    let spillCosts := wordHeuristicSpillCosts currentFunction program
    (wordCanonicalizeMoves moves |>.map (wordCoalesceMoveCost spillCosts),
      some spillCosts)
  else
    (moves, none)

def wordAllocateGraphFunctionWithHeuristics (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let (moves, _) := wordGetHeuristics algorithm currentFunction renamedProgram
  (wordAllocateGraphWithPrioritizedMoves tree forced
      (wordStackOnlyUnion fixedSources stackOnly.forced)
      moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

end Flapjack
