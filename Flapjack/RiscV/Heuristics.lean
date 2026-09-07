import Flapjack.RiscV.RegAlloc

/-!
# CakeML Word allocation heuristics

CakeML computes a small usage summary immediately before register allocation.
The five counters record whether a variable occurs on the left-hand side of a
constant, register, or memory operation, and on the right-hand side of a
register or memory operation.  This module ports that executable summary for
the Word fragment represented by Flapjack.

The source allocator also attaches priorities to move preferences.  The
existing graph allocator accepts unprioritized pairs for compatibility, while
the entry points below retain the source priorities and pass them to the
same coalescing machinery.
-/

namespace Flapjack

structure WordHeuristicCounts where
  lhsConst : Nat
  lhsReg : Nat
  lhsMem : Nat
  rhsReg : Nat
  rhsMem : Nat
  deriving DecidableEq, Repr

def wordHeuristicZero : WordHeuristicCounts :=
  { lhsConst := 0, lhsReg := 0, lhsMem := 0, rhsReg := 0, rhsMem := 0 }

def wordHeuristicUpdate (name : Nat)
    (update : WordHeuristicCounts → WordHeuristicCounts)
    (counts : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  let value := match lookupNatInfo name counts with
    | some value => value
    | none => wordHeuristicZero
  (name, update value) :: counts.filter (fun entry => entry.1 != name)

def wordHeuristicAddLhsConst (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsConst := value.lhsConst + 1 }) counts

def wordHeuristicAddLhsReg (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsReg := value.lhsReg + 1 }) counts

def wordHeuristicAddLhsMem (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsMem := value.lhsMem + 1 }) counts

def wordHeuristicAddRhsReg (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with rhsReg := value.rhsReg + 1 }) counts

def wordHeuristicAddRhsMem (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with rhsMem := value.rhsMem + 1 }) counts

def wordHeuristicAddLhsRegs : List Nat → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | [], counts => counts
  | name :: names, counts =>
      wordHeuristicAddLhsRegs names (wordHeuristicAddLhsReg name counts)

def wordHeuristicAddRhsRegs : List Nat → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | [], counts => counts
  | name :: names, counts =>
      wordHeuristicAddRhsRegs names (wordHeuristicAddRhsReg name counts)

def wordHeuristicInst : WordInst → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | .arith operation, counts =>
      match operation with
      | .longMul left right sourceLeft sourceRight =>
          wordHeuristicAddLhsReg right
            (wordHeuristicAddLhsReg left
              (wordHeuristicAddRhsReg sourceRight
                (wordHeuristicAddRhsReg sourceLeft counts)))
      | .longDiv left right sourceLeft sourceRight quotient =>
          wordHeuristicAddLhsReg right
            (wordHeuristicAddLhsReg left
              (wordHeuristicAddRhsReg quotient
                (wordHeuristicAddRhsReg sourceRight
                  (wordHeuristicAddRhsReg sourceLeft counts))))
      | .addCarry destination carry sourceLeft sourceRight carryIn =>
          wordHeuristicAddLhsReg carry
            (wordHeuristicAddLhsReg destination
              (wordHeuristicAddRhsReg carryIn
                (wordHeuristicAddRhsReg sourceRight
                  (wordHeuristicAddRhsReg sourceLeft counts))))
      | .div destination dividend divisor =>
          wordHeuristicAddLhsReg destination
            (wordHeuristicAddRhsReg divisor
              (wordHeuristicAddRhsReg dividend counts))
  | .mem operator destination _, counts =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          wordHeuristicAddLhsMem destination counts
      | .store | .store8 | .store16 | .store32 =>
          wordHeuristicAddRhsMem destination counts

def wordHeuristicMax (left right : WordHeuristicCounts) : WordHeuristicCounts :=
  { lhsConst := max left.lhsConst right.lhsConst
    lhsReg := max left.lhsReg right.lhsReg
    lhsMem := max left.lhsMem right.lhsMem
    rhsReg := max left.rhsReg right.rhsReg
    rhsMem := max left.rhsMem right.rhsMem }

def wordHeuristicKeys (counts : NatInfoMap WordHeuristicCounts) : List Nat :=
  counts.map Prod.fst

def wordHeuristicMaxAll (left right : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  ((wordHeuristicKeys left ++ wordHeuristicKeys right).eraseDups).foldl
    (fun result name =>
      let leftValue := match lookupNatInfo name left with
        | some value => value
        | none => wordHeuristicZero
      let rightValue := match lookupNatInfo name right with
        | some value => value
        | none => wordHeuristicZero
      wordHeuristicUpdate name (fun _ => wordHeuristicMax leftValue rightValue) result)
    []

def wordHeuristicMergeCalls (left right : List Nat) : List Nat :=
  right.foldl (fun calls name => if name ∈ calls then calls else name :: calls) left

def wordHeuristicAddCall (counts : NatInfoMap WordHeuristicCounts)
    (calls : List Nat) : List Nat :=
  wordHeuristicMergeCalls calls (wordHeuristicKeys counts)

def wordHeuristicMoves (moves : List (Nat × Nat))
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  match moves with
  | [] => counts
  | (left, right) :: moves =>
      wordHeuristicMoves moves
        (wordHeuristicAddLhsReg left (wordHeuristicAddRhsReg right counts))

def wordHeuristic (currentFunction : Nat) : WordProg α →
    NatInfoMap WordHeuristicCounts × List Nat →
    NatInfoMap WordHeuristicCounts × List Nat
  | .move _ moves, (counts, calls) => (wordHeuristicMoves moves counts, calls)
  | .inst instruction, (counts, calls) => (wordHeuristicInst instruction counts, calls)
  | .get destination _, (counts, calls) =>
      (wordHeuristicAddLhsMem destination counts, calls)
  | .set _ (.var source), (counts, calls) =>
      (wordHeuristicAddRhsMem source counts, calls)
  | .opCurrHeap _ destination source, (counts, calls) =>
      (wordHeuristicAddLhsReg destination
        (wordHeuristicAddRhsReg source counts), calls)
  | .locValue destination _, (counts, calls) =>
      (wordHeuristicAddLhsReg destination counts, calls)
  | .seq first second, state =>
      wordHeuristic currentFunction second (wordHeuristic currentFunction first state)
  | .mustTerminate body, state => wordHeuristic currentFunction body state
  | .ite _ condition right thenBranch elseBranch, (counts, calls) =>
      let thenResult := wordHeuristic currentFunction thenBranch (counts, calls)
      let elseResult := wordHeuristic currentFunction elseBranch (counts, calls)
      let merged := wordHeuristicMaxAll thenResult.1 elseResult.1
      let mergedCalls := wordHeuristicMergeCalls thenResult.2 elseResult.2
      let merged := wordHeuristicAddRhsReg condition merged
      match right with
      | .imm _ => (merged, mergedCalls)
      | .reg source =>
          (wordHeuristicAddRhsReg source merged, mergedCalls)
  | .call returns target _ handler, (counts, calls) =>
      let calls := match target with
        | some target => if target = currentFunction then
            wordHeuristicAddCall counts calls else calls
        | none => calls
      match returns with
      | none => (counts, calls)
      | some (_, _, returnCode, _, _) =>
          let returnResult := wordHeuristic currentFunction returnCode (counts, calls)
          match handler with
          | none => (returnResult.1, calls)
          | some (_, handlerCode, _, _) =>
              let handlerResult := wordHeuristic currentFunction handlerCode (counts, calls)
              (wordHeuristicMaxAll returnResult.1 handlerResult.1,
                wordHeuristicMergeCalls returnResult.2 handlerResult.2)
  | .shareInst operator name _, (counts, calls) =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (wordHeuristicAddLhsMem name counts, calls)
      | .store | .store8 | .store16 | .store32 =>
          (wordHeuristicAddRhsMem name counts, calls)
  | .loop _ body _, state => wordHeuristic currentFunction body state
  | _, state => state
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordProgPrioritizedMoves : WordProg α → List WordMove
  | .move priority moves => moves.map (fun move =>
      { priority := priority, left := move.1, right := move.2 })
  | .assign destination (.var source) =>
      [{ priority := 0, left := destination, right := source }]
  | .locValue destination source =>
      [{ priority := 0, left := destination, right := source }]
  | .seq first second =>
      wordProgPrioritizedMoves first ++ wordProgPrioritizedMoves second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgPrioritizedMoves thenBranch ++ wordProgPrioritizedMoves elseBranch
  | .loop _ body _ | .mustTerminate body => wordProgPrioritizedMoves body
  | .call returns _ _ handler =>
      (match returns with
      | none => []
      | some (_, _, returnCode, _, _) => wordProgPrioritizedMoves returnCode) ++
      (match handler with
      | none => []
      | some (_, body, _, _) => wordProgPrioritizedMoves body)
  | _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateGraphProgramWithPriorities (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordGraphAllocation × WordProg α) :=
  let tree := wordClashTree program []
  let forced := wordProgForcedClashes program
  (wordAllocateGraphWithPrioritizedMoves tree forced fixedSources
      (wordProgPrioritizedMoves program) colours stackStart).map
    (fun allocation =>
      (allocation,
        wordApplyColour
          (wordGraphColouringAt allocation.colouring) program))

end Flapjack
