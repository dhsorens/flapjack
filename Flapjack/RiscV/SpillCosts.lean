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
  /- CakeML's Simple allocator (modes 0 and 1) deliberately receives no
     move preferences.  IRC (modes 2 and 3) receives the prioritized list;
     the linear-scan modes are dispatched before reaching this wrapper. -/
  let allocation := if algorithm < 2 then
      wordAllocateGraph tree (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources stackOnly.forced) [] colours stackStart
    else
      wordAllocateGraphWithPrioritizedMoves tree forced
        (wordStackOnlyUnion fixedSources stackOnly.forced)
        moves colours stackStart
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

/-! The location-aware StackLang lowering must retain the SSA names.  The
    coloured result above is useful for the register-only semantic boundary,
    but replacing virtual names before consulting `wordGraphLocations` makes
    lookups fail (and can also accidentally hit another virtual name). -/
def wordAllocateGraphFunctionWithHeuristicsRenamed (parameters : List Nat)
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
  let allocation := if algorithm < 2 then
      wordAllocateGraph tree (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources stackOnly.forced) [] colours stackStart
    else
      wordAllocateGraphWithPrioritizedMoves tree forced
        (wordStackOnlyUnion fixedSources stackOnly.forced)
        moves colours stackStart
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

theorem wordAllocateGraphFunctionWithHeuristics_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristics] at halloc
  split at halloc
  · rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
    exact wordAllocateGraph_sound
      (WordClashTree.seq
        (.set (wordSsaRenameFunction parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
      (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
      (wordStackOnlyUnion fixedSources
        (wordStackOnly (wordSsaRenameFunction parameters program).2.snd).forced)
      [] colours stackStart allocation' hgraph
  · rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
    exact wordAllocateGraphWithPrioritizedMoves_sound
      (WordClashTree.seq
        (.set (wordSsaRenameFunction parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
      (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
      (wordStackOnlyUnion fixedSources
        (wordStackOnly (wordSsaRenameFunction parameters program).2.snd).forced)
      (wordGetHeuristics algorithm currentFunction
        (wordSsaRenameFunction parameters program).2.snd).1
      colours stackStart allocation' hgraph

theorem wordAllocateGraphFunctionWithHeuristicsRenamed_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
      (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristicsRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation'
  have hgraph' :
      (if algorithm < 2 then
          wordAllocateGraph
            ((WordClashTree.set renamedParameters).seq
              (wordClashTree renamedProgram []))
            (wordProgForcedClashes renamedProgram)
            (wordStackOnlyUnion fixedSources
              (wordStackOnly renamedProgram).forced) [] colours stackStart
        else
          wordAllocateGraphWithPrioritizedMoves
            ((WordClashTree.set renamedParameters).seq
              (wordClashTree renamedProgram []))
            (wordProgForcedClashes renamedProgram)
            (wordStackOnlyUnion fixedSources
              (wordStackOnly renamedProgram).forced)
            (wordGetHeuristics algorithm currentFunction renamedProgram).1
            colours stackStart) = some allocation := by
    simpa [hstate, hparameters, hprogram] using hgraph
  have hcol : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring)
          renamedProgram) := by
    simp [wordAllocateGraphFunctionWithHeuristics, hstate, hparameters,
      hprogram, hgraph']
  exact wordAllocateGraphFunctionWithHeuristics_sound parameters program
    fixedSources algorithm currentFunction colours stackStart state
    renamedParameters allocation
    (wordApplyColour (wordGraphColouringAt allocation.colouring)
      renamedProgram) hcol


/-! Heuristic allocation over the complete CakeML-shaped SSA function.  The
    formal-entry move is part of the allocated program, so the graph and its
    preferences see the same boundary as the full-SSA spill pipeline. -/
def wordAllocateGraphFunctionWithHeuristicsEntryRenamed (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let (moves, _) := wordGetHeuristics algorithm currentFunction renamedProgram
  let allocation := if algorithm < 2 then
      wordAllocateGraph tree forced
        (wordStackOnlyUnion fixedSources stackOnly.forced) [] colours stackStart
    else
      wordAllocateGraphWithPrioritizedMoves tree forced
        (wordStackOnlyUnion fixedSources stackOnly.forced)
        moves colours stackStart
  allocation.map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

theorem wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithHeuristicsEntryRenamed] at halloc
  rcases halloc with ⟨allocation_, hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation_
  have hgraphFull :
      (if algorithm < 2 then
          wordAllocateGraph
            ((WordClashTree.set renamedParameters).seq
              (wordClashTree renamedProgram []))
            (wordProgForcedClashes renamedProgram)
            (wordStackOnlyUnion fixedSources
              (wordStackOnly renamedProgram).forced) [] colours stackStart
        else
          wordAllocateGraphWithPrioritizedMoves
            ((WordClashTree.set renamedParameters).seq
              (wordClashTree renamedProgram []))
            (wordProgForcedClashes renamedProgram)
            (wordStackOnlyUnion fixedSources
              (wordStackOnly renamedProgram).forced)
            (wordGetHeuristics algorithm currentFunction renamedProgram).1
            colours stackStart) = some allocation := by
    simpa [hstate, hparameters, hprogram] using hgraph
  by_cases hsimple : algorithm < 2
  · have hsimpleAlloc : wordAllocateGraph
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))
        (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources
          (wordStackOnly renamedProgram).forced) [] colours stackStart =
        some allocation := by
      simpa [hsimple] using hgraphFull
    have hsound := wordAllocateGraph_sound
      ((WordClashTree.set renamedParameters).seq
        (wordClashTree renamedProgram []))
      (wordProgForcedClashes renamedProgram)
      (wordStackOnlyUnion fixedSources
        (wordStackOnly renamedProgram).forced)
      [] colours stackStart allocation hsimpleAlloc
    simpa [hstate, hparameters, hprogram] using hsound
  · have hprioritizedAlloc : wordAllocateGraphWithPrioritizedMoves
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))
        (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources
          (wordStackOnly renamedProgram).forced)
        (wordGetHeuristics algorithm currentFunction renamedProgram).1
        colours stackStart = some allocation := by
      simpa [hsimple] using hgraphFull
    have hsound := wordAllocateGraphWithPrioritizedMoves_sound
      ((WordClashTree.set renamedParameters).seq
        (wordClashTree renamedProgram []))
      (wordProgForcedClashes renamedProgram)
      (wordStackOnlyUnion fixedSources
        (wordStackOnly renamedProgram).forced)
      (wordGetHeuristics algorithm currentFunction renamedProgram).1
      colours stackStart allocation hprioritizedAlloc
    simpa [hstate, hparameters, hprogram] using hsound

end Flapjack
