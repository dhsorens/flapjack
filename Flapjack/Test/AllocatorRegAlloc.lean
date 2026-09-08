import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.WordToStack

namespace Flapjack

/-! Regression tests for the CakeML graph allocator data model. -/

example : wordTagForSource [] 1 = .atemp := by
  rfl

example : wordTagForSource [1] 1 = .stemp := by
  rfl

example : wordTagForSource [] 3 = .stemp := by
  rfl

example : wordTagForSource [] 4 = .fixed 2 := by
  rfl

example :
    (wordMkBijection
      (.seq (.delta [4] [2]) (.delta [5] [3]))).next = 4 := by
  decide +kernel

example :
    lookupNatInfo 4
        (wordMkBijection
          (.seq (.delta [4] [2]) (.delta [5] [3]))).toNode = some 2 := by
  decide +kernel

example :
    lookupNatInfo 0
        (wordInitRegAlloc (.delta [0, 1] [2]) [] []).graph.adjacency =
      some [1] := by
  decide +kernel

example :
    lookupNatInfo 1
        (wordInitRegAlloc (.delta [0, 1] [2]) [] []).graph.adjacency =
      some [0] := by
  decide +kernel

example :
    wordGraphTagColour
        (wordColourGraph 2 2 2
          (wordInitRegAlloc (.delta [0, 1] []) [] []).graph) 1 =
      some 1 := by
  decide +kernel

example :
    wordGraphColouringRespectsEdges
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  decide +kernel

example :
    wordGraphTagColour
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) 1 =
      some 2 := by
  decide +kernel

example :
    wordGraphTagsAreFixed
        (wordColourGraph 2 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  decide +kernel

example :
    wordGraphColouringRespectsEdges
        (wordColourGraphWithWorklist 1 1
          (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  decide +kernel

example :
    wordGraphTagsAreFixed
      (wordColourGraphWithWorklist 1 1
        (wordInitRegAlloc (.delta [1, 5] []) [] []).graph) = true := by
  decide +kernel

example :
    let graph : WordRegGraph :=
      { adjacency := [], tags := [(0, .atemp), (1, .atemp)], dimension := 2 }
    let state : WordRaState :=
      { graph := graph, active := [0, 1],
        degrees := [(0, 1), (1, 2)], simpWl := [],
        spillWl := [0, 1], stack := [] }
    let state := wordRaUnspill 2 state
    state.simpWl = [0] ∧ state.spillWl = [1] := by
  decide

example :
    let graph : WordRegGraph :=
      { adjacency := [(0, [1]), (1, [0, 2]), (2, [1])]
        tags := [(0, .atemp), (1, .atemp), (2, .atemp)]
        dimension := 3 }
    let state := wordInitMoveStateWithColours 1 graph []
    let state := wordMoveSpillAll (state.active.length + 1) 1 state
    state.active = [] ∧ state.spillWl = [] ∧
      state.stack = [2, 0, 1] := by
  decide

example :
    let graph : WordRegGraph :=
      { adjacency := [(0, [1, 2]), (1, [0]), (2, [0])]
        tags := [(0, .atemp), (1, .atemp), (2, .atemp)]
        dimension := 3 }
    let state := wordInitMoveStateWithColours 1 graph []
    let state := wordMoveSpillAllWithCosts 1 1
      [(0, 1000), (1, 1), (2, 1000)] state
    state.stack = [1] ∧ state.active = [0, 2] ∧
      state.spillWl = [0, 2] := by
  decide

def moveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .atemp), (1, .atemp)]
    dimension := 2 }

def fixedMoveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .fixed 3), (1, .atemp)]
    dimension := 2 }

def fixedRightMoveWorklistGraph : WordRegGraph :=
  { adjacency := []
    tags := [(0, .atemp), (1, .fixed 3)]
    dimension := 2 }

def move01 : WordMove :=
  { priority := 7, left := 0, right := 1 }

example :
    (wordRaInitialSimplify 1 moveWorklistGraph).stack = [1, 0] := by
  decide +kernel

example :
    let state := wordInitMoveStateWithColoursFromStack 1 moveWorklistGraph [move01] [0]
    state.stack = [0] ∧ state.available = [] ∧ state.unavailable = [] := by
  decide

example :
    (wordColourGraphWithWorklistAndMovesFromStack 1 1 [] [] [0]
      moveWorklistGraph).tags =
      [(0, .fixed 1), (1, .fixed 1)] := by
  decide +kernel

example :
    (wordColourGraphWithWorklistAndMovesFromStack 1 2 [] [] [0]
      { adjacency := [(0, [1]), (1, [0])]
        tags := [(0, .atemp), (1, .atemp)]
        dimension := 2 }).tags =
      [(0, .fixed 2), (1, .fixed 1)] := by
  decide +kernel

example :
    wordSortMoves
      [{ priority := 1, left := 0, right := 1 },
       { priority := 3, left := 2, right := 3 },
       { priority := 2, left := 4, right := 5 }] =
      [{ priority := 3, left := 2, right := 3 },
       { priority := 2, left := 4, right := 5 },
       { priority := 1, left := 0, right := 1 }] := by
  decide

example :
    wordPrepareMoveWorklists moveWorklistGraph [move01] =
      { available := [move01], unavailable := [] } := by
  decide

example :
    wordPrepareMoveWorklistsWithColours 1 fixedMoveWorklistGraph [move01] =
      { available := [], unavailable := [move01] } := by
  decide

example :
    wordPrepareMoveWorklistsWithColours 4 fixedMoveWorklistGraph [move01] =
      { available := [move01], unavailable := [] } := by
  decide

def briggsMoveGraph : WordRegGraph :=
  { adjacency := [(1, [2]), (2, [1, 3]), (3, [2])]
    tags := [(0, .atemp), (1, .atemp), (2, .atemp), (3, .atemp)]
    dimension := 4 }

example : wordBgOk 2 briggsMoveGraph 0 1 = some ([], [2]) := by
  decide

example : wordBgOk 1 briggsMoveGraph 0 1 = none := by
  decide

example : wordCoalesceSafe 1 briggsMoveGraph [0, 1] move01 = false := by
  decide

example :
    let state := wordInitMoveStateWithColours 2 moveWorklistGraph [move01]
    let state := wordMovePrefreeze 2 state
    state.available = [] ∧ state.unavailable = [] ∧
      state.stack = [1, 0] := by
  decide

example :
    let state := wordInitMoveStateWithColours 2 moveWorklistGraph [move01]
    let state := wordMovePrefreeze 2 state
    state.related = [] ∧ state.freezeWl = [] := by
  decide

example :
    let graph : WordRegGraph :=
      { adjacency := [(2, [0]), (0, [2])]
        tags := [(0, .atemp), (1, .atemp), (2, .atemp)]
        dimension := 3 }
    let move : WordMove := { priority := 3, left := 0, right := 1 }
    let state : WordMoveState :=
      { graph := graph
        active := [0, 1, 2]
        degrees := [(0, 1), (1, 0), (2, 1)]
        parents := [(0, 0), (1, 1), (2, 2)]
        related := [0, 1]
        available := []
        unavailable := [move]
        freezeWl := []
        spillWl := []
        stack := [] }
    let state := wordMoveReviveUnavailable 2 [2] state
    state.available = [move] ∧ state.unavailable = [] := by
  decide

example :
    let graph : WordRegGraph :=
      { adjacency := [(0, [1, 2]), (1, [0]), (2, [0])]
        tags := [(0, .atemp), (1, .atemp), (2, .atemp)]
        dimension := 3 }
    let state : WordMoveState :=
      { graph := graph, active := [0, 1, 2],
        degrees := [(0, 2), (1, 1), (2, 1)],
        parents := [(0, 0), (1, 1), (2, 2)],
        related := [0], available := [], unavailable := [],
        freezeWl := [0], spillWl := [], stack := [] }
    let state := wordMoveRespill 2 0 state
    state.freezeWl = [] ∧ state.spillWl = [0] := by
  decide

example :
    wordMoveFreezeCandidates 2 moveWorklistGraph
      [(0, 0), (1, 1)] [0, 1] = [0, 1] := by
  decide

example :
    let state := wordInitMoveStateWithColours 2 moveWorklistGraph [move01]
    let state := wordFreezeAllAvailable 2 state
    state.available = [] ∧ state.unavailable = [] ∧ state.stack = [0] := by
  decide

example :
    wordPrepareMoveWorklists moveWorklistGraph
      [{ priority := 0, left := 0, right := 0 }] =
      { available := [],
        unavailable := [{ priority := 0, left := 0, right := 0 }] } := by
  decide

example :
    wordPrepareMoveWorklists
      { adjacency := [(0, [1]), (1, [0])]
        tags := [(0, .atemp), (1, .atemp)]
        dimension := 2 }
      [move01] =
      { available := [], unavailable := [move01] } := by
  decide

example :
    wordCanonicalizeMove fixedMoveWorklistGraph move01 =
      { priority := 7, left := 0, right := 1 } := by
  decide

example :
    wordCanonicalizeMove fixedRightMoveWorklistGraph move01 =
      { priority := 7, left := 1, right := 0 } := by
  decide

example :
    (wordCoalesceParentFuel 4 moveWorklistGraph
      [(0, 0), (1, 0), (2, 1)] 2) =
      (0, [(2, 0), (1, 0), (0, 0)]) := by
  decide

example :
    (wordCoalesceMove 1
      (wordInitMoveState fixedMoveWorklistGraph [move01]) move01).map
        (fun state => lookupNatInfo 1 state.parents) = some (some 0) := by
  decide

example :
    (wordCoalesceMove 1
      (wordInitMoveState fixedMoveWorklistGraph [move01]) move01).map
        (fun state => state.stack) = some [1] := by
  decide

example :
    let state := wordInitMoveState
      { adjacency := []
        tags := [(0, .fixed 3), (1, .atemp), (2, .atemp)]
        dimension := 3 }
      [move01, { priority := 2, left := 1, right := 2 }]
    let state := wordCoalesceAllAvailable 1 state
    lookupNatInfo 2 state.parents = some 0 ∧ state.stack = [2, 1] ∧
      state.available = [] := by
  decide

example : wordGraphColouringAt [(4, 8)] 4 = 8 := by
  decide

example : wordGraphColouringAt [(4, 8)] 6 = 6 := by
  decide

example :
    (wordAllocateGraph (.delta [0, 1] []) [] [] [] 1 1).isSome = true := by
  decide +kernel

example :
    (wordAllocateGraph (.delta [0, 1] []) [] [] [] 1 1).map
        (fun allocation =>
          (lookupNatInfo 0 allocation.colouring,
            lookupNatInfo 1 allocation.colouring)) =
      some (some 0, some 2) := by
  decide +kernel

example :
    (wordAllocateGraphFunction [2]
      (.skip : WordProg Nat) [] 1 1).map
        (fun result =>
          (result.2.1,
            lookupNatInfo 5 result.2.2.1.colouring)) =
      some ([5], some 2) := by
  decide +kernel

#guard
    wordStackOnly
      ((.seq (.assign 5 (.var 7)) (.assign 3 (.var 5))) : WordProg Nat) =
      { temporary := [], forced := [] }

example :
    wordStackOnly (.move 0 [(3, 5)] : WordProg Nat) =
      { temporary := [5], forced := [] } := by
  decide

#guard
    (wordAllocateGraphFunctionWithStackOnly [2]
      (.seq (.assign 5 (.var 7)) (.assign 3 (.var 5)) : WordProg Nat)
      [] 1 1).isSome

example :
    (wordAllocateGraph
      (.seq (.set [5]) (.delta [9] [5])) [] [5] [(9, 5)] 13 13).isSome = true := by
  decide +kernel

#guard
    wordStackOnly (.assign 9 (.var 5) : WordProg Nat) =
      { temporary := [], forced := [] }

#guard
    (wordAllocateGraphFunctionWithStackOnly [2]
      (.assign 3 (.var 2) : WordProg Nat) [] 13 14).isSome

#guard
    ((wordAllocateGraphFunctionWithStackOnly [2]
      (.assign 3 (.var 2) : WordProg (RiscV.Word 64)) [] 13 14).map
        (fun (_, _, allocation, _) =>
          (lookupNatInfo 5 (wordGraphLocations allocation 13 14)).isSome &&
            (lookupNatInfo 9 (wordGraphLocations allocation 13 14)).isSome)).getD false = true

#guard
    ((wordAllocateGraphFunctionWithStackOnly [2]
      (.assign 3 (.var 2) : WordProg (RiscV.Word 64)) [] 13 14).map
        (fun (_, _, allocation, _) =>
          (lookupNatInfo 5 (wordGraphLocations allocation 13 14),
            lookupNatInfo 9 (wordGraphLocations allocation 13 14)))).getD
      (none, none) =
      (some (WordLocation.register 2), some (WordLocation.register 2))

#guard
    ((wordAllocateGraphFunctionWithStackOnlyRenamed [2]
      (.assign 3 (.var 2) : WordProg (RiscV.Word 64)) [] 13 14).bind
        (fun (_, parameters, allocation, program) =>
          RiscV.wordToStackFunctionWithParameters
            { locations := wordGraphLocations allocation 13 14,
              scratch := 31, stackBase := 0, addressScratch := 29 }
            parameters program)).isSome

example :
    wordProgForcedClashes
      (.inst (.arith (.longMul 4 5 6 7)) : WordProg Nat) =
      [(4, 5), (4, 6), (4, 7)] := by
  decide +kernel

#guard
    (wordAllocateGraphProgram
      (.assign 2 (.var 3) : WordProg Nat) [] 1 1).map
        (fun allocation =>
          match allocation.2 with
          | .assign destination (.var source) => (destination, source)
          | _ => (0, 0)) =
      some (2, 2)

end Flapjack
