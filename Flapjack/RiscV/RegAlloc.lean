import Flapjack.RiscV.Allocator

namespace Flapjack

/-!
The data model used by the CakeML graph-colouring allocator.

The executable spill allocator in Allocator.lean is deliberately small.  This
module ports the next layer of the source development: Fixed/Atemp/Stemp node
tags, the source-variable to graph-node bijection, and the graph builder that
interprets a clash tree as cliques.
-/

inductive WordRegTag where
  | fixed (colour : Nat)
  | atemp
  | stemp
  deriving DecidableEq, Repr

def wordTagColour : WordRegTag → Nat
  | .fixed colour => colour
  | .atemp | .stemp => 0

def wordIsStackVar (name : Nat) : Prop :=
  name % 4 = 3

def wordIsPhysicalVar (name : Nat) : Prop :=
  name % 2 = 0

def wordIsAllocVar (name : Nat) : Prop :=
  name % 4 = 1

def wordTagForSource (fixedSources : List Nat)
    (source : Nat) : WordRegTag :=
  let remainder := source % 4
  if remainder = 1 then
    if source ∈ fixedSources then .stemp else .atemp
  else if remainder = 3 then
    .stemp
  else
    .fixed (source / 2)

def wordMkTags (dimension : Nat) (fixedSources : List Nat)
    (fromNode : NatInfoMap Nat) : NatInfoMap WordRegTag :=
  (List.range dimension).map (fun node =>
    let source := match lookupNatInfo node fromNode with
      | some source => source
      | none => 0
    (node, wordTagForSource fixedSources source))

structure WordRegGraph where
  adjacency : NatInfoMap (List Nat)
  tags : NatInfoMap WordRegTag
  dimension : Nat
  deriving Repr

def wordGraphNeighbours (graph : WordRegGraph) (node : Nat) : List Nat :=
  match lookupNatInfo node graph.adjacency with
  | some neighbours => neighbours
  | none => []

def wordGraphUpdate (node : Nat) (neighbours : List Nat)
    (adjacency : NatInfoMap (List Nat)) : NatInfoMap (List Nat) :=
  (node, neighbours) :: adjacency.filter (fun entry => entry.1 != node)

def wordGraphInsertNeighbour (node neighbour : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let current := wordGraphNeighbours graph node
  if neighbour ∈ current then
    graph
  else
    { graph with adjacency :=
        wordGraphUpdate node (neighbour :: current) graph.adjacency }

def wordGraphInsertEdge (left right : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let graph := wordGraphInsertNeighbour left right graph
  wordGraphInsertNeighbour right left graph

def wordGraphInsertEdges (node : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | neighbour :: neighbours, graph =>
      wordGraphInsertEdges node neighbours
        (wordGraphInsertEdge node neighbour graph)

def wordGraphExtendClique : List Nat → List Nat → WordRegGraph →
    WordRegGraph × List Nat
  | [], clique, graph => (graph, clique)
  | node :: nodes, clique, graph =>
      if node ∈ clique then
        wordGraphExtendClique nodes clique graph
      else
        wordGraphExtendClique nodes (node :: clique)
          (wordGraphInsertEdges node clique graph)

def wordGraphInsertClique : List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordGraphInsertClique nodes
        (wordGraphInsertEdges node nodes graph)

structure WordBijection where
  toNode : NatInfoMap Nat
  fromNode : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordListRemap : List Nat → WordBijection → WordBijection
  | [], bijection => bijection
  | source :: sources, bijection =>
      match lookupNatInfo source bijection.toNode with
      | some _ => wordListRemap sources bijection
      | none =>
          wordListRemap sources
            { toNode := (source, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, source) :: bijection.fromNode
              next := bijection.next + 1 }

def wordClashTreeBijection : WordClashTree → WordBijection →
    WordBijection
  | .delta writes reads, bijection =>
      wordListRemap (writes ++ reads) bijection
  | .set names, bijection => wordListRemap names bijection
  | .branch branchLive thenBranch elseBranch, bijection =>
      let bijection := wordClashTreeBijection thenBranch bijection
      let bijection := wordClashTreeBijection elseBranch bijection
      match branchLive with
      | none => bijection
      | some names => wordListRemap names bijection
  | .seq first second, bijection =>
      wordClashTreeBijection first
        (wordClashTreeBijection second bijection)
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordMkBijection (tree : WordClashTree) : WordBijection :=
  wordClashTreeBijection tree
    { toNode := [], fromNode := [], next := 0 }

def wordBijectionToNode (bijection : WordBijection) (source : Nat) : Nat :=
  match lookupNatInfo source bijection.toNode with
  | some node => node
  | none => bijection.next

structure WordGraphResult where
  graph : WordRegGraph
  liveIn : List Nat
  deriving Repr

def wordMkGraph (toNode : Nat → Nat) : WordClashTree → List Nat →
    WordRegGraph → WordGraphResult
  | .delta writes reads, liveOut, graph =>
      let writes := writes.map toNode
      let reads := reads.map toNode
      let (graph, live) := wordGraphExtendClique writes liveOut graph
      let live := live.filter (fun node => node ∉ writes)
      let (graph, liveIn) := wordGraphExtendClique reads live graph
      { graph := graph, liveIn := liveIn }
  | .set names, _, graph =>
      let names := names.map toNode
      { graph := wordGraphInsertClique names graph, liveIn := names }
  | .branch branchLive thenBranch elseBranch, liveOut, graph =>
      let thenResult := wordMkGraph toNode thenBranch liveOut graph
      let elseResult :=
        wordMkGraph toNode elseBranch liveOut thenResult.graph
      match branchLive with
      | none =>
          let (graph, liveIn) := wordGraphExtendClique
            thenResult.liveIn elseResult.liveIn elseResult.graph
          { graph := graph, liveIn := liveIn }
      | some names =>
          let names := names.map toNode
          { graph := wordGraphInsertClique names elseResult.graph
            liveIn := names }
  | .seq first second, liveOut, graph =>
      let secondResult := wordMkGraph toNode second liveOut graph
      wordMkGraph toNode first secondResult.liveIn secondResult.graph
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordTagFixedColour : WordRegTag → Option Nat
  | .fixed colour => some colour
  | .atemp | .stemp => none

def wordFixedNeighbourColours (nodes : List Nat)
    (tags : NatInfoMap WordRegTag) : List Nat :=
  match nodes with
  | [] => []
  | node :: nodes =>
      let colours := match lookupNatInfo node tags with
        | some tag =>
            match wordTagFixedColour tag with
            | some colour => [colour]
            | none => []
        | none => []
      colours ++ wordFixedNeighbourColours nodes tags

def wordRemoveColours (removed colours : List Nat) : List Nat :=
  match colours with
  | [] => []
  | colour :: colours =>
      if colour ∈ removed then
        wordRemoveColours removed colours
      else
        colour :: wordRemoveColours removed colours

def wordStackColourCandidates (start : Nat) (blocked : List Nat) : List Nat :=
  (List.range (start + blocked.length + 1)).filter
    (fun colour => colour ≥ start)

def wordUnboundColour (start : Nat) (blocked : List Nat) : Nat :=
  match wordFirstAvailable (wordStackColourCandidates start blocked) blocked with
  | some colour => colour
  | none => start

def wordGraphUpdateTag (node : Nat) (tag : WordRegTag)
    (tags : NatInfoMap WordRegTag) : NatInfoMap WordRegTag :=
  (node, tag) :: tags.filter (fun entry => entry.1 != node)

def wordAssignAtempTag (colours : List Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .atemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      match wordFirstAvailable (wordRemoveColours blocked colours) blocked with
      | some colour =>
          { graph with tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      | none =>
          { graph with tags := wordGraphUpdateTag node .stemp graph.tags }
  | some (.fixed _) | some .stemp | none => graph

def wordAssignAtemps (colours : List Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignAtemps colours nodes (wordAssignAtempTag colours node graph)

def wordAssignStempTag (stackStart : Nat) (node : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .stemp =>
      let blocked := wordFixedNeighbourColours
        (wordGraphNeighbours graph node) graph.tags
      let colour := wordUnboundColour stackStart blocked
      { graph with tags :=
          wordGraphUpdateTag node (.fixed colour) graph.tags }
  | some (.fixed _) | some .atemp | none => graph

def wordAssignStemps (stackStart : Nat) : List Nat →
    WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      wordAssignStemps stackStart nodes
        (wordAssignStempTag stackStart node graph)

def wordColourGraph (dimension colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let nodes := List.range dimension
  let colours := (List.range colours).map (fun colour => colour + 1)
  let graph := wordAssignAtemps colours nodes graph
  wordAssignStemps stackStart nodes graph

def wordGraphTagColour (graph : WordRegGraph) (node : Nat) : Option Nat :=
  match lookupNatInfo node graph.tags with
  | some tag => wordTagFixedColour tag
  | none => none

def wordGraphTagsAreFixed (graph : WordRegGraph) : Bool :=
  graph.tags.all (fun entry =>
    match entry.2 with
    | .fixed _ => true
    | .atemp | .stemp => false)

def wordGraphColouringRespectsEdges (graph : WordRegGraph) : Bool :=
  graph.adjacency.all (fun entry =>
    let node := entry.1
    entry.2.all (fun neighbour =>
      match wordGraphTagColour graph node,
        wordGraphTagColour graph neighbour with
      | some left, some right => left != right
      | _, _ => false))

structure WordRaState where
  graph : WordRegGraph
  active : List Nat
  degrees : NatInfoMap Nat
  simpWl : List Nat
  spillWl : List Nat
  stack : List Nat
  deriving Repr

def wordRaNodeIsAtemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .atemp => true
  | some (.fixed _) | some .stemp | none => false

def wordRaNodeIsStemp (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some .stemp => true
  | some (.fixed _) | some .atemp | none => false

def wordRaDegree (graph : WordRegGraph) (node : Nat) : Nat :=
  (wordGraphNeighbours graph node).length

def wordRaDegrees (graph : WordRegGraph) : NatInfoMap Nat :=
  (List.range graph.dimension).map (fun node => (node, wordRaDegree graph node))

def wordRaRefreshWorklists (colours : Nat) (state : WordRaState) :
    WordRaState :=
  let simpWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree < colours
      | none => false)
  let spillWl := state.active.filter (fun node =>
    wordRaNodeIsAtemp state.graph node &&
      match lookupNatInfo node state.degrees with
      | some degree => degree ≥ colours
      | none => false)
  { state with simpWl := simpWl, spillWl := spillWl }

def wordRaInit (colours : Nat) (graph : WordRegGraph) : WordRaState :=
  let active := List.range graph.dimension
  let state : WordRaState :=
    { graph := graph
      active := active
      degrees := wordRaDegrees graph
      simpWl := []
      spillWl := []
      stack := [] }
  wordRaRefreshWorklists colours state

def wordRaDegreesForActive (graph : WordRegGraph)
    (active : List Nat) : NatInfoMap Nat :=
  active.map (fun node =>
    (node, ((wordGraphNeighbours graph node).filter
      (fun neighbour => active.contains neighbour)).length))

def wordRaInitFromStack (colours : Nat) (preStack : List Nat)
    (graph : WordRegGraph) : WordRaState :=
  let active := (List.range graph.dimension).filter
    (fun node => !preStack.contains node)
  let state : WordRaState :=
    { graph := graph
      active := active
      degrees := wordRaDegreesForActive graph active
      simpWl := []
      spillWl := []
      stack := preStack }
  wordRaRefreshWorklists colours state

def wordRaPartitionBy (predicate : Nat → Bool) : List Nat →
    List Nat × List Nat
  | [] => ([], [])
  | node :: nodes =>
      let (yes, no) := wordRaPartitionBy predicate nodes
      if predicate node then
        (node :: yes, no)
      else
        (yes, node :: no)

/- Move spill candidates that have become low degree into the simplify
   worklist. This is the register-side part of CakeML unspill; move revival
   is handled by WordMoveState after coalescing. -/
def wordRaUnspill (colours : Nat) (state : WordRaState) : WordRaState :=
  let (low, high) := wordRaPartitionBy (fun node =>
    (lookupNatInfo node state.degrees).getD 0 < colours) state.spillWl
  { state with
    simpWl := low ++ state.simpWl
    spillWl := high }

def wordRaRemoveNode (colours : Nat) (node : Nat)
    (_forceSpill : Bool) (state : WordRaState) : WordRaState :=
  let graph := state.graph
  let degrees := (wordGraphNeighbours state.graph node).foldl
    (fun degrees neighbour =>
      match lookupNatInfo neighbour degrees with
      | some degree =>
          (neighbour, degree - 1) :: degrees.filter
            (fun entry => entry.1 != neighbour)
      | none => degrees)
    state.degrees
  let state := { state with
    graph := graph
    active := state.active.erase node
    degrees := degrees
    simpWl := state.simpWl.erase node
    spillWl := state.spillWl.erase node
    stack := node :: state.stack }
  wordRaUnspill colours state


def wordRaChooseSpillNodeByDegree (degrees : NatInfoMap Nat) :
    Nat → List Nat → Nat
  | node, [] => node
  | node, candidate :: candidates =>
      let best := wordRaChooseSpillNodeByDegree degrees node candidates
      let candidateDegree := (lookupNatInfo candidate degrees).getD 0
      let bestDegree := (lookupNatInfo best degrees).getD 0
      if bestDegree < candidateDegree then candidate else best

def wordRaSimplifyAll : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAll fuel colours
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | node :: nodes =>
              let chosen := wordRaChooseSpillNodeByDegree state.degrees node nodes
              wordRaSimplifyAll fuel colours
                (wordRaRemoveNode colours chosen true state)
          | [] => state

def wordRaSimplifyLow : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyLow fuel colours
            (wordRaRemoveNode colours node false state)
      | [] => state

def wordRaInitialSimplify (colours : Nat)
    (graph : WordRegGraph) : WordRaState :=
  let state := wordRaInit colours graph
  wordRaSimplifyLow (state.active.length + 1) colours state

def wordRaFinalizeStemps (state : WordRaState) : WordRaState :=
  let stempNodes := state.active.filter (wordRaNodeIsStemp state.graph)
  { state with
    active := state.active.filter (fun node => !wordRaNodeIsStemp state.graph node)
    stack := stempNodes.reverse ++ state.stack }

def wordRaChooseColour (colours stackStart : Nat)
    (graph : WordRegGraph) (node : Nat) : Nat :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  match lookupNatInfo node graph.tags with
  | some .stemp => wordUnboundColour stackStart blocked
  | some .atemp =>
      match wordFirstAvailable
          (wordRemoveColours blocked
            ((List.range colours).map (fun colour => colour + 1))) blocked with
      | some colour => colour
      | none => wordUnboundColour stackStart blocked
  | some (.fixed colour) => colour
  | none => 0

def wordRaAtempHasAvailableColour (colours : Nat)
    (graph : WordRegGraph) (node : Nat) : Bool :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  (wordFirstAvailable
    (wordRemoveColours blocked ((List.range colours).map (fun colour => colour + 1))) blocked).isSome

def wordRaMarkUncolourableAtemp (colours : Nat)
    (graph : WordRegGraph) (node : Nat) : WordRegGraph :=
  match lookupNatInfo node graph.tags with
  | some .atemp =>
      if wordRaAtempHasAvailableColour colours graph node then graph
      else 
        { graph with tags := wordGraphUpdateTag node .stemp graph.tags }
  | some (.fixed _) | some .stemp | none => graph

def wordRaColourStack (colours stackStart : Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let graph := wordRaMarkUncolourableAtemp colours graph node
      let colour := wordRaChooseColour colours stackStart graph node
      let graph := { graph with
        tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      wordRaColourStack colours stackStart nodes graph

def wordColourGraphWithWorklist (colours stackStart : Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let state := wordRaInit colours graph
  let state := wordRaSimplifyAll (state.active.length + 1) colours state
  let state := wordRaFinalizeStemps state
  wordRaColourStack colours stackStart state.stack state.graph

/-! Move worklists and the first coalescing step.

    CakeML keeps move preferences separate from clash edges.  A move is first
    rejected when it is reflexive, already clashes, or has two fixed
    endpoints.  The remaining moves are canonicalised so a fixed endpoint is
    always the coalescing target.  The full CakeML allocator has additional
    freeze and move-revival phases; this section ports the data and the safe
    coalescing transition those phases build on.
-/

structure WordMove where
  priority : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def wordMoveEndpoints (move : WordMove) : List Nat :=
  [move.left, move.right]

def wordTagIsFixed : WordRegTag → Bool
  | .fixed _ => true
  | .atemp | .stemp => false

def wordTagIsAtemp : WordRegTag → Bool
  | .atemp => true
  | .fixed _ | .stemp => false

def wordGraphTagIs (predicate : WordRegTag → Bool)
    (graph : WordRegGraph) (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some tag => predicate tag
  | none => false

def wordMoveRelatedNodes (moves : List WordMove) : List Nat :=
  (moves.flatMap wordMoveEndpoints).eraseDups

def wordMoveConsistent (graph : WordRegGraph) (related : List Nat)
    (move : WordMove) : Bool :=
  let fixedLeft := wordGraphTagIs wordTagIsFixed graph move.left
  let fixedRight := wordGraphTagIs wordTagIsFixed graph move.right
  let leftMayMove := fixedLeft || (related.contains move.left)
  let rightMayMove := fixedRight || (related.contains move.right)
  move.left != move.right &&
    !(wordGraphNeighbours graph move.right).contains move.left &&
    leftMayMove && rightMayMove && !(fixedLeft && fixedRight)

def wordGraphTagFixedBelow (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some (.fixed colour) => colour < colours
  | some .atemp | some .stemp | none => false

def wordPartitionBy (predicate : Nat → Bool) : List Nat →
    List Nat × List Nat
  | [] => ([], [])
  | node :: nodes =>
      let (yes, no) := wordPartitionBy predicate nodes
      if predicate node then
        (node :: yes, no)
      else
        (yes, node :: no)

def wordConsideredVar (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  wordGraphTagIs wordTagIsAtemp graph node ||
    wordGraphTagFixedBelow colours graph node

def wordDegreeOrInf (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Nat :=
  if wordGraphTagFixedBelow colours graph node then
    colours
  else
    wordRaDegree graph node

def wordBgOk (colours : Nat) (graph : WordRegGraph)
    (target absorbed : Nat) : Option (List Nat × List Nat) :=
  let targetNeighbours := wordGraphNeighbours graph target
  let absorbedNeighbours := wordGraphNeighbours graph absorbed
  let (case1, case2) := wordPartitionBy
    (fun node => targetNeighbours.contains node) absorbedNeighbours
  let case1 := case1.filter (wordConsideredVar colours graph)
  let case2 := case2.filter (wordConsideredVar colours graph)
  let case2Degrees := case2.filter (fun node =>
    wordDegreeOrInf colours graph node ≥ colours)
  let case2Length := case2Degrees.length
  if case2Length = 0 then
    some (case1, case2)
  else
    let case3 := targetNeighbours.filter (fun node =>
      !(absorbedNeighbours.contains node) &&
        wordConsideredVar colours graph node)
    let case1Degrees := case1.map (wordDegreeOrInf (colours + 1) graph)
    let case3Degrees := case3.map (wordDegreeOrInf colours graph)
    let case1Length := (case1Degrees.filter (fun degree =>
      degree - 1 ≥ colours)).length
    let case3Length := (case3Degrees.filter (fun degree =>
      degree ≥ colours)).length
    if case1Length + case2Length + case3Length < colours then
      some (case1, case2)
    else
      none

def wordFullMoveConsistent (colours : Nat) (graph : WordRegGraph)
    (move : WordMove) : Bool :=
  let fixedLeft := wordGraphTagFixedBelow colours graph move.left
  let fixedRight := wordGraphTagFixedBelow colours graph move.right
  let atempLeft := wordGraphTagIs wordTagIsAtemp graph move.left
  let atempRight := wordGraphTagIs wordTagIsAtemp graph move.right
  move.left < graph.dimension && move.right < graph.dimension &&
    move.left != move.right &&
    !(wordGraphNeighbours graph move.right).contains move.left &&
    (fixedLeft || atempLeft) && (fixedRight || atempRight) &&
    !(fixedLeft && fixedRight)

def wordCanonicalizeMove (graph : WordRegGraph) (move : WordMove) : WordMove :=
  let leftFixed := wordGraphTagIs wordTagIsFixed graph move.left
  let rightFixed := wordGraphTagIs wordTagIsFixed graph move.right
  if rightFixed then
    { move with left := move.right, right := move.left }
  else if leftFixed then
    move
  else if move.left ≤ move.right then
    move
  else
    { move with left := move.right, right := move.left }

structure WordMoveWorklists where
  available : List WordMove
  unavailable : List WordMove
  deriving DecidableEq, Repr

def wordInsertMoveSorted (move : WordMove) : List WordMove → List WordMove
  | [] => [move]
  | head :: moves =>
      if move.priority ≥ head.priority then
        move :: head :: moves
      else
        head :: wordInsertMoveSorted move moves

def wordSortMoves : List WordMove → List WordMove
  | [] => []
  | move :: moves => wordInsertMoveSorted move (wordSortMoves moves)

def wordSortMoveWorklists (worklists : WordMoveWorklists) :
    WordMoveWorklists :=
  { available := wordSortMoves worklists.available
    unavailable := wordSortMoves worklists.unavailable }

def wordPrepareMoveWorklists (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveWorklists :=
  let related := wordMoveRelatedNodes moves
  let worklists := moves.foldl (fun worklists move =>
    let move := wordCanonicalizeMove graph move
    if wordMoveConsistent graph related move then
      { worklists with available := worklists.available ++ [move] }
    else
      { worklists with unavailable := worklists.unavailable ++ [move] })
    { available := [], unavailable := [] }
  wordSortMoveWorklists worklists

def wordPrepareMoveWorklistsWithColours (colours : Nat)
    (graph : WordRegGraph) (moves : List WordMove) : WordMoveWorklists :=
  let worklists := moves.foldl (fun worklists move =>
    let move := wordCanonicalizeMove graph move
    if wordFullMoveConsistent colours graph move then
      { worklists with available := worklists.available ++ [move] }
    else
      { worklists with unavailable := worklists.unavailable ++ [move] })
    { available := [], unavailable := [] }
  wordSortMoveWorklists worklists

def wordPreferenceMoves : List (Nat × Nat) → List WordMove
  | [] => []
  | (left, right) :: moves =>
      { priority := 0, left := left, right := right } ::
        wordPreferenceMoves moves

def wordRemapMove (bijection : WordBijection) (move : WordMove) : WordMove :=
  { move with
    left := wordBijectionToNode bijection move.left
    right := wordBijectionToNode bijection move.right }

def wordRemapMoves (bijection : WordBijection) : List WordMove → List WordMove
  | [] => []
  | move :: moves =>
      wordRemapMove bijection move :: wordRemapMoves bijection moves

def wordParentUpdate (node parent : Nat)
    (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  (node, parent) :: parents.filter (fun entry => entry.1 != node)

def wordParentOf (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  match lookupNatInfo node parents with
  | some parent => parent
  | none => node

/- A CakeML freeze candidate is a live Atemp that is still move-related and
   has degree below the register budget.  Fixed nodes and coalesced nodes stay
   out of this worklist. -/
def wordMoveFreezeCandidates (colours : Nat) (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (related : List Nat) : List Nat :=
  (List.range graph.dimension).filter (fun node =>
    wordParentOf parents node = node &&
      wordGraphTagIs wordTagIsAtemp graph node &&
      wordRaDegree graph node < colours && related.contains node)

def wordCoalesceParentFuel : Nat → WordRegGraph → NatInfoMap Nat → Nat →
    Nat × NatInfoMap Nat
  | 0, _graph, parents, node => (wordParentOf parents node, parents)
  | fuel + 1, graph, parents, node =>
      let parent := wordParentOf parents node
      if parent = node then
        (node, parents)
      else if wordGraphTagIs wordTagIsFixed graph parent then
        (parent, parents)
      else if node ≤ parent then
        (node, parents)
      else
        let (ancestor, parents) :=
          wordCoalesceParentFuel fuel graph parents parent
        (ancestor, wordParentUpdate node ancestor parents)

def wordRaMovePreferredNodes (moves : List WordMove)
    (node : Nat) : List Nat :=
  match moves with
  | [] => []
  | head :: moves =>
      if head.left = node then
        head.right :: wordRaMovePreferredNodes moves node
      else if head.right = node then
        head.left :: wordRaMovePreferredNodes moves node
      else
        wordRaMovePreferredNodes moves node

def wordRaFirstMatchingFixedColour (available : List Nat)
    (graph : WordRegGraph) : List Nat → Option Nat
  | [] => none
  | node :: nodes =>
      match lookupNatInfo node graph.tags with
      | some (.fixed colour) =>
          if colour ∈ available then some colour
          else wordRaFirstMatchingFixedColour available graph nodes
      | some .atemp | some .stemp | none =>
          wordRaFirstMatchingFixedColour available graph nodes

def wordRaChooseColourWithMoves (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat)
    (graph : WordRegGraph) (node : Nat) : Nat :=
  let blocked := wordFixedNeighbourColours
    (wordGraphNeighbours graph node) graph.tags
  let preferred := wordRaMovePreferredNodes moves node
  match lookupNatInfo node graph.tags with
  | some .stemp =>
      match wordRaFirstMatchingFixedColour
          (wordStackColourCandidates stackStart blocked) graph preferred with
      | some colour => colour
      | none => wordUnboundColour stackStart blocked
  | some .atemp =>
      let available := wordRemoveColours blocked
        ((List.range colours).map (fun colour => colour + 1))
      let (root, _) := wordCoalesceParentFuel
        (graph.dimension + 1) graph parents node
      match wordRaFirstMatchingFixedColour available graph (root :: preferred) with
      | some colour => colour
      | none =>
          match wordFirstAvailable available blocked with
          | some colour => colour
          | none => wordUnboundColour stackStart blocked
  | some (.fixed colour) => colour
  | none => 0

def wordRaColourStackWithMoves (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let colour := wordRaChooseColourWithMoves colours stackStart moves
        parents graph node
      let graph := { graph with
        tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
      wordRaColourStackWithMoves colours stackStart moves parents nodes graph

def wordRaColourAtempsWithMoves (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let graph := wordRaMarkUncolourableAtemp colours graph node
      let graph := match lookupNatInfo node graph.tags with
        | some .atemp =>
            let colour := wordRaChooseColourWithMoves colours stackStart moves
              parents graph node
            { graph with tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
        | some (.fixed _) | some .stemp | none => graph
      wordRaColourAtempsWithMoves colours stackStart moves parents nodes graph

def wordRaColourStempsWithMoves (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
      let graph := match lookupNatInfo node graph.tags with
        | some .stemp =>
            let colour := wordRaChooseColourWithMoves colours stackStart moves
              parents graph node
            { graph with tags := wordGraphUpdateTag node (.fixed colour) graph.tags }
        | some (.fixed _) | some .atemp | none => graph
      wordRaColourStempsWithMoves colours stackStart moves parents nodes graph

def wordRaColourTwoPass (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat)
    (state : WordRaState) : WordRegGraph :=
  let moves := wordSortMoves moves
  let nodes := state.stack ++ List.range state.graph.dimension
  let graph := wordRaColourAtempsWithMoves colours stackStart moves parents
    nodes state.graph
  wordRaColourStempsWithMoves colours stackStart moves parents
    (List.range graph.dimension) graph

def wordColourGraphWithWorklistAndMovesFromStack (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat)
    (preStack : List Nat) (graph : WordRegGraph) : WordRegGraph :=
  let state := wordRaInitFromStack colours preStack graph
  let state := wordRaSimplifyAll (state.active.length + 1) colours state
  wordRaColourTwoPass colours stackStart moves parents state

def wordColourGraphWithWorklistAndMoves (colours stackStart : Nat)
    (moves : List WordMove) (parents : NatInfoMap Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  wordColourGraphWithWorklistAndMovesFromStack colours stackStart moves parents [] graph

def wordMoveFreezeCandidatesForActive (colours : Nat)
    (graph : WordRegGraph) (active : List Nat)
    (degrees : NatInfoMap Nat) (parents : NatInfoMap Nat)
    (related : List Nat) : List Nat :=
  active.filter (fun node =>
    wordParentOf parents node = node &&
      wordGraphTagIs wordTagIsAtemp graph node &&
      (lookupNatInfo node degrees).getD 0 < colours &&
      related.contains node)

def wordMoveSpillCandidatesForActive (colours : Nat)
    (graph : WordRegGraph) (active : List Nat)
    (degrees : NatInfoMap Nat) : List Nat :=
  active.filter (fun node =>
    wordGraphTagIs wordTagIsAtemp graph node &&
      (lookupNatInfo node degrees).getD 0 >= colours)

structure WordMoveState where
  graph : WordRegGraph
  active : List Nat
  degrees : NatInfoMap Nat
  parents : NatInfoMap Nat
  related : List Nat
  available : List WordMove
  unavailable : List WordMove
  freezeWl : List Nat
  spillWl : List Nat
  stack : List Nat
  deriving Repr

def wordMoveRefreshFreeze (colours : Nat) (state : WordMoveState) :
    WordMoveState :=
  let related := wordMoveRelatedNodes (state.available ++ state.unavailable)
  { state with
    related := related
    freezeWl := wordMoveFreezeCandidatesForActive colours state.graph
      state.active state.degrees state.parents related }

def wordInitMoveState (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveState :=
  let worklists := wordPrepareMoveWorklists graph moves
  let active := List.range graph.dimension
  { graph := graph
    active := active
    degrees := wordRaDegreesForActive graph active
    parents := active.map (fun node => (node, node))
    related := wordMoveRelatedNodes moves
    available := worklists.available
    unavailable := worklists.unavailable
    freezeWl := []
    spillWl := []
    stack := [] }

def wordInitMoveStateWithColours (colours : Nat) (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveState :=
  let worklists := wordPrepareMoveWorklistsWithColours colours graph moves
  let active := List.range graph.dimension
  let parents := active.map (fun node => (node, node))
  let related := wordMoveRelatedNodes moves
  let degrees := wordRaDegreesForActive graph active
  { graph := graph
    active := active
    degrees := degrees
    parents := parents
    related := related
    available := worklists.available
    unavailable := worklists.unavailable
    freezeWl := wordMoveFreezeCandidatesForActive colours graph active degrees
      parents related
    spillWl := wordMoveSpillCandidatesForActive colours graph active degrees
    stack := [] }

def wordInitMoveStateWithColoursFromStack (colours : Nat)
    (graph : WordRegGraph) (moves : List WordMove)
    (preStack : List Nat) : WordMoveState :=
  let moves := moves.filter (fun move =>
    !preStack.contains move.left && !preStack.contains move.right)
  let active := (List.range graph.dimension).filter
    (fun node => !preStack.contains node)
  let state := wordInitMoveStateWithColours colours graph moves
  let degrees := wordRaDegreesForActive graph active
  { state with
    active := active
    degrees := degrees
    stack := preStack
    freezeWl := wordMoveFreezeCandidatesForActive colours graph active
      degrees state.parents state.related
    spillWl := wordMoveSpillCandidatesForActive colours graph active degrees }

def wordMoveReplaceNode (oldNode newNode : Nat) (move : WordMove) : WordMove :=
  { move with
    left := if move.left = oldNode then newNode else move.left
    right := if move.right = oldNode then newNode else move.right }

def wordResolveMove (state : WordMoveState) (move : WordMove) :
    WordMove × NatInfoMap Nat :=
  let (left, parents) := wordCoalesceParentFuel
    (state.graph.dimension + 1) state.graph state.parents move.left
  let (right, parents) := wordCoalesceParentFuel
    (state.graph.dimension + 1) state.graph parents move.right
  ({ move with left := left, right := right }, parents)

def wordCoalesceFreshNeighbours (graph : WordRegGraph)
    (target absorbed : Nat) : List Nat :=
  (wordGraphNeighbours graph absorbed).filter (fun node =>
    node != target && !(wordGraphNeighbours graph target).contains node)

def wordCoalesceSignificant (colours : Nat) (graph : WordRegGraph)
    (node : Nat) : Bool :=
  match lookupNatInfo node graph.tags with
  | some (.fixed _) => true
  | some .atemp | some .stemp => wordRaDegree graph node ≥ colours
  | none => true

def wordCoalesceSafe (colours : Nat) (graph : WordRegGraph)
    (related : List Nat) (move : WordMove) : Bool :=
  if !wordMoveConsistent graph related move then
    false
  else
    let move := wordCanonicalizeMove graph move
    let target := move.left
    let absorbed := move.right
    (wordBgOk colours graph target absorbed).isSome

def wordPartitionMoves (predicate : WordMove → Bool) : List WordMove →
    List WordMove × List WordMove
  | [] => ([], [])
  | move :: moves =>
      let (yes, no) := wordPartitionMoves predicate moves
      if predicate move then
        (move :: yes, no)
      else
        (yes, move :: no)

/- Revive unavailable moves incident on neighbors whose degree may have
   decreased after a coalescing step. This is the CakeML revive_moves phase:
   revived moves return to the priority-sorted available worklist. -/
def wordMoveReviveUnavailable (colours : Nat) (nodes : List Nat)
    (state : WordMoveState) : WordMoveState :=
  let neighbours := nodes.flatMap (wordGraphNeighbours state.graph)
  let (revived, unavailable) := wordPartitionMoves (fun move =>
    (wordMoveEndpoints move).any (fun endpoint => neighbours.contains endpoint))
    state.unavailable
  let state := { state with
    available := wordSortMoves (revived ++ state.available)
    unavailable := unavailable }
  wordMoveRefreshFreeze colours state
def wordMoveSetDegree (node degree : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  (node, degree) :: degrees.filter (fun entry => entry.1 != node)

def wordMoveIncDegree (node amount : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  match lookupNatInfo node degrees with
  | some degree => wordMoveSetDegree node (degree + amount) degrees
  | none => degrees

def wordMoveDecDegree (node : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  match lookupNatInfo node degrees with
  | some degree => wordMoveSetDegree node (degree - 1) degrees
  | none => degrees

def wordMoveDecNeighbours (graph : WordRegGraph) (node : Nat)
    (degrees : NatInfoMap Nat) : NatInfoMap Nat :=
  (wordGraphNeighbours graph node).foldl
    (fun degrees neighbour => wordMoveDecDegree neighbour degrees) degrees

def wordMoveRespill (colours : Nat) (node : Nat)
    (state : WordMoveState) : WordMoveState :=
  if (lookupNatInfo node state.degrees).getD 0 < colours ||
      !state.freezeWl.contains node then
    state
  else
    { state with
      freezeWl := state.freezeWl.erase node
      spillWl := if node ∈ state.spillWl then state.spillWl
        else node :: state.spillWl }

def wordCoalesceMove (colours : Nat) (state : WordMoveState)
    (move : WordMove) : Option WordMoveState :=
  let (move, parents) := wordResolveMove state move
  let state := { state with parents := parents }
  let move := wordCanonicalizeMove state.graph move
  if !wordCoalesceSafe colours state.graph state.related move then
    none
  else
    match wordBgOk colours state.graph move.left move.right with
    | none => none
    | some (case1, case2) =>
      let fresh := wordCoalesceFreshNeighbours
        state.graph move.left move.right
      let graph := fresh.foldl
        (fun graph node => wordGraphInsertEdge move.left node graph)
        state.graph
      let degrees := wordMoveIncDegree move.left case2.length state.degrees
      let degrees := case1.foldl
        (fun degrees node => wordMoveDecDegree node degrees) degrees
      let degrees := wordMoveSetDegree move.right 0 degrees
      let active := state.active.erase move.right
      let parents := wordParentUpdate move.right move.left state.parents
      let pending := (state.available ++ state.unavailable).map
        (wordMoveReplaceNode move.right move.left)
      let worklists := wordPrepareMoveWorklists graph pending
      let state : WordMoveState :=
        { graph := graph
          active := active
          degrees := degrees
          parents := parents
          related := wordMoveRelatedNodes pending
          available := worklists.available
          unavailable := worklists.unavailable
          freezeWl := wordMoveFreezeCandidatesForActive colours graph active
            degrees parents (wordMoveRelatedNodes pending)
          spillWl := state.spillWl.erase move.right
          stack := move.right :: state.stack }
      let state := wordMoveReviveUnavailable colours case1 state
      some (wordMoveRespill colours move.left state)

def wordMoveTouches (node : Nat) (move : WordMove) : Bool :=
  move.left = node || move.right = node

/- Freeze one node as in CakeML's `do_freeze`: all moves incident on the node
   become unavailable/retired, after which the node is no longer move-related.
   The graph itself is retained for the later degree-based colouring pass. -/
def wordFreezeNode (colours : Nat) (node : Nat)
    (state : WordMoveState) : WordMoveState :=
  let available := state.available.filter (fun move =>
    !wordMoveTouches node move)
  let unavailable := state.unavailable.filter (fun move =>
    !wordMoveTouches node move)
  let degrees := wordMoveDecNeighbours state.graph node state.degrees
  let degrees := wordMoveSetDegree node 0 degrees
  let active := state.active.erase node
  let state := { state with
    active := active
    degrees := degrees
    available := available
    unavailable := unavailable
    spillWl := state.spillWl.erase node
    stack := if node ∈ state.stack then state.stack else node :: state.stack }
  wordMoveRefreshFreeze colours state

def wordMovePrefreeze (colours : Nat) (state : WordMoveState) : WordMoveState :=
  let unavailable := state.unavailable.filter (wordMoveConsistent state.graph state.related)
  let spillWl := state.spillWl.filter (fun node =>
    wordParentOf state.parents node = node)
  let state := { state with
    available := []
    unavailable := unavailable
    spillWl := spillWl }
  let state := wordMoveRefreshFreeze colours state
  let simplifiable := state.active.filter (fun node =>
    wordParentOf state.parents node = node &&
      wordGraphTagIs wordTagIsAtemp state.graph node &&
      (lookupNatInfo node state.degrees).getD 0 < colours &&
      !state.related.contains node)
  simplifiable.foldl (fun state node => wordFreezeNode colours node state) state

def wordFreezeAll : Nat → Nat → WordMoveState → WordMoveState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.freezeWl with
      | [] => state
      | node :: _ => wordFreezeAll fuel colours (wordFreezeNode colours node state)

def wordFreezeAllAvailable (colours : Nat) (state : WordMoveState) :
    WordMoveState :=
  wordFreezeAll (state.freezeWl.length + state.graph.dimension + 1)
    colours state

/-! Repeated coalescing mirrors CakeML's do_coalesce loop.  Invalid moves
    are retired to the unavailable list, while a successful merge rebuilds
    the pending worklists so moves that became useful are reconsidered. -/

def wordMoveSpillNode (node : Nat) (state : WordMoveState) : WordMoveState :=
  let degrees := wordMoveDecNeighbours state.graph node state.degrees
  let degrees := wordMoveSetDegree node 0 degrees
  { state with
    active := state.active.erase node
    degrees := degrees
    freezeWl := state.freezeWl.erase node
    spillWl := state.spillWl.erase node
    stack := node :: state.stack }

def wordMoveSpillAll : Nat → Nat → WordMoveState → WordMoveState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.spillWl with
      | [] => state
      | node :: nodes =>
          let chosen := wordRaChooseSpillNodeByDegree state.degrees node nodes
          let state := wordMoveSpillNode chosen state
          let state := wordMovePrefreeze colours state
          let state := wordFreezeAllAvailable colours state
          wordMoveSpillAll fuel colours state

def wordCoalesceAll : Nat → Nat → WordMoveState → WordMoveState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.available with
      | [] => state
      | move :: moves =>
          if wordCoalesceSafe colours state.graph state.related move then
            match wordCoalesceMove colours state move with
            | some state => wordCoalesceAll fuel colours state
            | none =>
                wordCoalesceAll fuel colours
                  { state with
                    available := moves
                    unavailable := move :: state.unavailable }
          else
            wordCoalesceAll fuel colours
              { state with
                available := moves
                unavailable := move :: state.unavailable }

def wordCoalesceAllAvailable (colours : Nat) (state : WordMoveState) :
    WordMoveState :=
  wordCoalesceAll
    (state.available.length + state.unavailable.length + state.graph.dimension + 1)
    colours state

structure WordRegAllocInput where
  bijection : WordBijection
  graph : WordRegGraph
  deriving Repr

def wordInitRegAlloc (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat) :
    WordRegAllocInput :=
  let bijection := wordMkBijection tree
  let emptyGraph : WordRegGraph :=
    { adjacency := [], tags := [], dimension := bijection.next }
  let graphResult := wordMkGraph
    (wordBijectionToNode bijection) tree [] emptyGraph
  let graph := forced.foldl
    (fun graph edge =>
      wordGraphInsertEdge
        (wordBijectionToNode bijection edge.1)
        (wordBijectionToNode bijection edge.2) graph)
    graphResult.graph
  { bijection := bijection
    graph := { graph with
      tags := wordMkTags bijection.next fixedSources bijection.fromNode } }

/-! Bridge the graph allocator back to source variables.

    CakeML stores compressed graph colours and applies total_colour only at
    the Word boundary.  In particular, physical source variables are tagged
    with half their architectural register number and total colours are
    doubled again.  Keeping this conversion explicit avoids accidentally
    treating a graph colour as a RISC-V register number. -/

def wordGraphNodeFinalColour (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  let (root, _) := wordCoalesceParentFuel
    (graph.dimension + 1) graph parents node
  match wordGraphTagColour graph root with
  | some colour => colour
  | none => 0

def wordGraphTotalColourAt (graph : WordRegGraph)
    (parents : NatInfoMap Nat) (node : Nat) : Nat :=
  2 * wordGraphNodeFinalColour graph parents node

def wordGraphColouringAt (colouring : NatInfoMap Nat)
    (source : Nat) : Nat :=
  match lookupNatInfo source colouring with
  | some colour => colour
  | none => if source % 2 == 0 then source else 0

def wordGraphTotalColouring (input : WordRegAllocInput)
    (graph : WordRegGraph) (parents : NatInfoMap Nat) : NatInfoMap Nat :=
  input.bijection.fromNode.map (fun entry =>
    (entry.2, wordGraphTotalColourAt graph parents entry.1))

structure WordGraphAllocation where
  bijection : WordBijection
  initialTags : NatInfoMap WordRegTag
  graph : WordRegGraph
  colouring : NatInfoMap Nat
  parents : NatInfoMap Nat
  deriving Repr

/-!
The graph colours are deliberately kept separate from the physical locations
consumed by `word_to_stack`.  Fixed source variables retain their architectural
register, while Atemps use the even ABI registers selected by the allocator;
Stemps and spilled Atemps use consecutive stack slots starting at
`stackStart`.  Keeping the source-to-node bijection in the allocation makes
this conversion total for formals that are unused by the body as well.
-/
def wordGraphLocationAt (allocation : WordGraphAllocation)
    (colours stackStart : Nat) (source : Nat) : WordLocation :=
  match lookupNatInfo source allocation.bijection.toNode with
  | none =>
      if source % 2 = 0 then .register source else .stack 0
  | some node =>
      let colour := wordGraphNodeFinalColour allocation.graph
        allocation.parents node
      match lookupNatInfo node allocation.initialTags with
      | some (.fixed _) => .register (2 * colour)
      | some .atemp | some .stemp =>
          if colour ≤ colours then
            .register (2 * colour)
          else
            .stack (colour - stackStart)
      | none => .stack 0

def wordGraphLocations (allocation : WordGraphAllocation)
    (colours stackStart : Nat) : NatInfoMap WordLocation :=
  allocation.bijection.fromNode.map (fun entry =>
    (entry.2, wordGraphLocationAt allocation colours stackStart entry.2))

/-! Cost-aware spill selection from CakeML `do_spill`.  The heuristic
    costs are keyed by source names, while the graph worklist operates on
    bijection nodes, so translate the finite map once at allocation setup. -/
def wordSpillCostsToNodes (bijection : WordBijection)
    (costs : NatInfoMap Nat) : NatInfoMap Nat :=
  costs.foldl (fun result entry =>
    match lookupNatInfo entry.1 bijection.toNode with
    | some node => (node, entry.2) :: result
    | none => result) []

def wordRaSpillCost (costs : NatInfoMap Nat) (node : Nat) : Nat :=
  (lookupNatInfo node costs).getD 0

/-! CakeML's `safe_div` ranks a spill candidate by its cost divided by
    its current degree.  The degree map is the mutable active-graph degree
    maintained by the worklist state. -/
def wordRaSafeDiv (numerator denominator : Nat) : Nat :=
  if denominator = 0 then 0 else numerator / denominator

def wordRaSpillPriority (costs degrees : NatInfoMap Nat) (node : Nat) : Nat :=
  wordRaSafeDiv (wordRaSpillCost costs node)
    ((lookupNatInfo node degrees).getD 0)

def wordRaChooseSpillNode (costs degrees : NatInfoMap Nat) : Nat → List Nat → Nat
  | node, [] => node
  | node, candidate :: candidates =>
      let best := wordRaChooseSpillNode costs degrees node candidates
      if wordRaSpillPriority costs degrees candidate <
          wordRaSpillPriority costs degrees best then
        candidate
      else
        best

def wordRaSimplifyAllWithSpillCosts : Nat → Nat → NatInfoMap Nat →
    WordRaState → WordRaState
  | 0, _, _, state => state
  | fuel + 1, colours, costs, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAllWithSpillCosts fuel colours costs
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | [] => state
          | node :: nodes =>
              let chosen := wordRaChooseSpillNode costs state.degrees node nodes
              wordRaSimplifyAllWithSpillCosts fuel colours costs
                (wordRaRemoveNode colours chosen true state)

def wordMoveSpillAllWithCosts : Nat → Nat → NatInfoMap Nat →
    WordMoveState → WordMoveState
  | 0, _, _, state => state
  | fuel + 1, colours, costs, state =>
      match state.spillWl with
      | [] => state
      | node :: nodes =>
          let chosen := wordRaChooseSpillNode costs state.degrees node nodes
          let state := wordMoveSpillNode chosen state
          let state := wordMovePrefreeze colours state
          let state := wordFreezeAllAvailable colours state
          wordMoveSpillAllWithCosts fuel colours costs state

def wordColourGraphWithWorklistAndSpillCostsFromStack (colours stackStart : Nat)
    (costs : NatInfoMap Nat) (moves : List WordMove)
    (parents : NatInfoMap Nat) (preStack : List Nat)
    (graph : WordRegGraph) : WordRegGraph :=
  let state := wordRaInitFromStack colours preStack graph
  let state := wordRaSimplifyAllWithSpillCosts
    (state.active.length + 1) colours costs state
  wordRaColourTwoPass colours stackStart moves parents state

def wordColourGraphWithWorklistAndSpillCosts (colours stackStart : Nat)
    (costs : NatInfoMap Nat) (moves : List WordMove)
    (parents : NatInfoMap Nat) (graph : WordRegGraph) : WordRegGraph :=
  wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart costs
    moves parents [] graph

def wordAllocateGraphWithSpillCosts (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat)
    (costs : NatInfoMap Nat) : Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let costs := wordSpillCostsToNodes input.bijection costs
  let moves := wordRemapMoves input.bijection (wordPreferenceMoves moves)
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph moves
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart costs moves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

def wordGraphCheckAllocation (tree : WordClashTree)
    (candidate : WordGraphAllocation) : Option WordGraphAllocation :=
  let colour := wordGraphColouringAt candidate.colouring
  if wordGraphTagsAreFixed candidate.graph &&
      wordGraphColouringRespectsEdges candidate.graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some candidate
  else
    none

theorem wordGraphCheckAllocation_sound
    (tree : WordClashTree) (allocation : WordGraphAllocation)
    (hcheck : wordGraphCheckAllocation tree allocation = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  have hcheck' :
      wordGraphTagsAreFixed allocation.graph = true ∧
        wordGraphColouringRespectsEdges allocation.graph = true ∧
        wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
          tree [] [] ≠ none := by
    simpa [wordGraphCheckAllocation] using hcheck
  rcases hcheck' with ⟨hfixed, hedges, hnotnone⟩
  have htree :
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
    cases hresult : wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring) tree [] [] with
    | none => exact (hnotnone hresult).elim
    | some value => simp
  exact ⟨hfixed, hedges, htree⟩

def wordAllocateGraphWithPrefreezeMovesAndSpillCostsCandidate
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (spillCosts : NatInfoMap Nat) :
    WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let costs := wordSpillCostsToNodes input.bijection spillCosts
  let coalesceMoves := wordRemapMoves input.bijection coalesceMoves
  let colourMoves := wordRemapMoves input.bijection colourMoves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph
    coalesceMoves initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordMovePrefreeze colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let moveState := wordMoveSpillAllWithCosts
    (moveState.active.length + 1) colours costs moveState
  let graph := wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart
    costs colourMoves moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  { bijection := input.bijection
    initialTags := input.graph.tags
    graph := graph
    colouring := colouring
    parents := moveState.parents }

def wordAllocateGraphWithPrefreezeMovesAndSpillCosts
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (spillCosts : NatInfoMap Nat) :
    Option WordGraphAllocation :=
  let candidate := wordAllocateGraphWithPrefreezeMovesAndSpillCostsCandidate
    tree forced fixedSources coalesceMoves colourMoves colours stackStart spillCosts
  wordGraphCheckAllocation tree candidate

theorem wordAllocateGraphWithPrefreezeMovesAndSpillCosts_sound
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (costs : NatInfoMap Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithPrefreezeMovesAndSpillCosts tree forced
      fixedSources coalesceMoves colourMoves colours stackStart costs =
      some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithPrefreezeMovesAndSpillCosts,
    wordGraphCheckAllocation] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordAllocateGraphWithPrioritizedMovesAndSpillCosts (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List WordMove) (colours stackStart : Nat)
    (costs : NatInfoMap Nat) : Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moves := wordRemapMoves input.bijection moves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph moves
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart costs moves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

theorem wordAllocateGraphWithSpillCosts_sound
    (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat)
    (costs : NatInfoMap Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithSpillCosts tree forced fixedSources moves
      colours stackStart costs = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithSpillCosts] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

theorem wordAllocateGraphWithPrioritizedMovesAndSpillCosts_sound
    (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List WordMove) (colours stackStart : Nat)
    (costs : NatInfoMap Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithPrioritizedMovesAndSpillCosts tree forced
      fixedSources moves colours stackStart costs = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithPrioritizedMovesAndSpillCosts] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordAllocateGraphSimpleWithColourMoves (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (colourMoves : List WordMove) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let colourMoves := wordRemapMoves input.bijection colourMoves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph []
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndMovesFromStack colours stackStart colourMoves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

def wordAllocateGraphSimpleWithColourMovesAndSpillCosts (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (colourMoves : List WordMove) (colours stackStart : Nat)
    (costs : NatInfoMap Nat) : Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let costs := wordSpillCostsToNodes input.bijection costs
  let colourMoves := wordRemapMoves input.bijection colourMoves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph []
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart costs
    colourMoves moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

theorem wordAllocateGraphSimpleWithColourMovesAndSpillCosts_sound
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (colourMoves : List WordMove)
    (colours stackStart : Nat) (costs : NatInfoMap Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphSimpleWithColourMovesAndSpillCosts tree
      forced fixedSources colourMoves colours stackStart costs = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphSimpleWithColourMovesAndSpillCosts] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

theorem wordAllocateGraphSimpleWithColourMoves_sound
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (colourMoves : List WordMove)
    (colours stackStart : Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphSimpleWithColourMoves tree forced fixedSources
      colourMoves colours stackStart = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphSimpleWithColourMoves] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordAllocateGraphWithPrioritizedMovesAndColourMoves (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) : Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let coalesceMoves := wordRemapMoves input.bijection coalesceMoves
  let colourMoves := wordRemapMoves input.bijection colourMoves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph coalesceMoves
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndMovesFromStack colours stackStart colourMoves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

def wordAllocateGraphWithPrioritizedMovesAndColourMovesAndSpillCosts
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (costs : NatInfoMap Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let costs := wordSpillCostsToNodes input.bijection costs
  let coalesceMoves := wordRemapMoves input.bijection coalesceMoves
  let colourMoves := wordRemapMoves input.bijection colourMoves
  let initial := wordRaInitialSimplify colours input.graph
  let moveState := wordInitMoveStateWithColoursFromStack colours input.graph coalesceMoves
    initial.stack
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndSpillCostsFromStack colours stackStart costs
    colourMoves moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

theorem wordAllocateGraphWithPrioritizedMovesAndColourMoves_sound
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithPrioritizedMovesAndColourMoves tree
      forced fixedSources coalesceMoves colourMoves colours stackStart =
      some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithPrioritizedMovesAndColourMoves] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

theorem wordAllocateGraphWithPrioritizedMovesAndColourMovesAndSpillCosts_sound
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (coalesceMoves colourMoves : List WordMove)
    (colours stackStart : Nat) (costs : NatInfoMap Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithPrioritizedMovesAndColourMovesAndSpillCosts
      tree forced fixedSources coalesceMoves colourMoves colours stackStart costs =
      some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithPrioritizedMovesAndColourMovesAndSpillCosts] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordAllocateGraph (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moves := wordRemapMoves input.bijection (wordPreferenceMoves moves)
  let moveState := wordInitMoveStateWithColours colours input.graph moves
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndMovesFromStack colours stackStart moves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

/-! The graph allocator performs a prefreeze repair between coalescing and
    freezing.  Keep this entry point separate from `wordAllocateGraph` so the
    existing graph-colouring contract keeps its small unfolding proofs. -/
def wordAllocateGraphWithPrefreeze (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moves := wordRemapMoves input.bijection (wordPreferenceMoves moves)
  let moveState := wordInitMoveStateWithColours colours input.graph moves
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordMovePrefreeze colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let moveState := wordMoveSpillAll (moveState.active.length + 1) colours moveState
  let graph := wordColourGraphWithWorklistAndMovesFromStack colours stackStart moves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

def wordAllocateGraphWithPrioritizedMoves (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List WordMove) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moves := wordRemapMoves input.bijection moves
  let moveState := wordInitMoveStateWithColours colours input.graph moves
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklistAndMovesFromStack colours stackStart moves
    moveState.parents moveState.stack moveState.graph
  let colouring := wordGraphTotalColouring input graph moveState.parents
  let colour := wordGraphColouringAt colouring
  if wordGraphTagsAreFixed graph &&
      wordGraphColouringRespectsEdges graph &&
      (wordClashTreeCheck colour tree [] []).isSome then
    some
      { bijection := input.bijection
        initialTags := input.graph.tags
        graph := graph
        colouring := colouring
        parents := moveState.parents }
  else
    none

theorem wordAllocateGraphWithPrioritizedMoves_sound
    (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List WordMove) (colours stackStart : Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphWithPrioritizedMoves tree forced fixedSources
      moves colours stackStart = some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        tree [] []).isSome = true := by
  simp [wordAllocateGraphWithPrioritizedMoves] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

theorem wordAllocateGraph_sound (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat)
    (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraph tree forced fixedSources moves colours stackStart =
      some allocation) :
    wordGraphTagsAreFixed allocation.graph = true ∧
    wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
      tree [] []).isSome = true := by
  simp [wordAllocateGraph] at halloc
  rcases halloc with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

def wordProgForcedClashes : WordProg α → List (Nat × Nat)
  | .skip | .move _ _ | .get _ _ | .store _ _ | .set _ _ | .break _ | .continue _ |
      .raise _ | .return _ _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ |
      .mustTerminate _ | .alloc _ _ | .storeConsts _ _ _ _ _ |
      .opCurrHeap _ _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ |
      .dataBufferWrite _ _ => []
  | .assign _ _ => []
  | .inst instruction => wordInstForcedClashes instruction
  | .seq first second =>
      wordProgForcedClashes first ++ wordProgForcedClashes second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgForcedClashes thenBranch ++ wordProgForcedClashes elseBranch
  | .loop _ body _ => wordProgForcedClashes body
  | .call _ _ _ none => []
  | .call _ _ _ (some (_, body, _, _)) => wordProgForcedClashes body
  | .shareInst _ _ _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateGraphProgram (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordGraphAllocation × WordProg α) :=
  let tree := wordClashTree program []
  let forced := wordProgForcedClashes program
  let moves := wordProgPreferenceEdges program
  (wordAllocateGraph tree forced fixedSources moves colours stackStart).map
    (fun allocation =>
      (allocation,
        wordApplyColour
          (wordGraphColouringAt allocation.colouring) program))

/- Function-level graph allocation.  CakeML's full SSA entry sequence makes
   every renamed formal an allocation participant, including an unused formal.
   The seed `Set` below still gives the graph all renamed formals and the
   clash oracle their ABI-entry interference; explicit entry `Move` programs
   are represented separately when the stack boundary is emitted. -/
def wordAllocateGraphFunction (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraph tree forced fixedSources moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

/-! Full-SSA graph allocation includes the parameter-entry moves in the
    coloured program.  `fixedSources` identifies the source names which are
    already architectural inputs (the usual RISC-V ABI formals); keeping that
    list explicit lets callers choose the same fixed-source policy as the HOL
    allocator. -/

def wordAllocateGraphFunctionWithEntry (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraph tree forced fixedSources moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

/-! The stack boundary needs the SSA names and allocation map together; it
    applies locations there rather than consuming graph-coloured names. -/

def wordAllocateGraphFunctionWithEntryRenamed (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraph tree forced fixedSources moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

/-! Backward forced-stack analysis from CakeML's get_stack_only.  The two
    lists correspond to its temporary-stack and forced-stack sets.  Lists are
    used as finite sets here so the analysis remains executable and easy to
    inspect in small RISC-V allocation regressions. -/

structure WordStackOnlyState where
  temporary : List Nat
  forced : List Nat
  deriving DecidableEq, Repr

def wordStackOnlyInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def wordStackOnlyDelete (name : Nat) (names : List Nat) : List Nat :=
  names.filter (fun candidate => candidate != name)

def wordStackOnlyUnion (left right : List Nat) : List Nat :=
  right.foldl (fun names name => wordStackOnlyInsert name names) left

def wordStackOnlyIntersection (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∈ right)

def wordStackOnlyDifference (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∉ right)

def wordStackOnlyRemoveTemps (names : List Nat)
    (state : WordStackOnlyState) : WordStackOnlyState :=
  let temporary := names.foldl
    (fun temporary name => wordStackOnlyDelete name temporary)
    state.temporary
  { state with temporary := temporary }

def wordStackOnlyMergeMove (destination source : Nat)
    (state : WordStackOnlyState) : WordStackOnlyState :=
  if destination ∈ state.temporary then
    let temporary := if source % 4 = 1 then
      wordStackOnlyInsert source state.temporary else state.temporary
    let forced := if source % 2 = 0 then state.forced
      else wordStackOnlyInsert destination state.forced
    { temporary := temporary
      forced := forced }
  else if destination % 4 = 3 then
    let temporary := if source % 4 = 1 then
      wordStackOnlyInsert source state.temporary else state.temporary
    { temporary := temporary
      forced := state.forced }
  else
    { state with temporary := wordStackOnlyDelete source state.temporary }

def wordStackOnlyMergeBranches (base left right : WordStackOnlyState) :
    WordStackOnlyState :=
  let keep := wordStackOnlyIntersection right.temporary
    (wordStackOnlyIntersection left.temporary base.temporary)
  let newOnly := wordStackOnlyUnion
    (wordStackOnlyDifference left.temporary base.temporary)
    (wordStackOnlyDifference right.temporary base.temporary)
  { temporary := wordStackOnlyUnion keep newOnly
    forced := wordStackOnlyUnion left.forced right.forced }

def wordStackOnlyFallback (program : WordProg α)
      (state : WordStackOnlyState) : WordStackOnlyState :=
  match wordClashTree program [] with
  | .delta writes reads =>
      wordStackOnlyRemoveTemps (writes ++ reads) state
  | _ => state

def wordStackOnlyProgramAux (program : WordProg α)
      (state : WordStackOnlyState) : WordStackOnlyState :=
    match program with
    | .move _ moves =>
        List.foldr (fun move state =>
          wordStackOnlyMergeMove move.1 move.2 state) state moves
    | .seq first second =>
        wordStackOnlyProgramAux first
          (wordStackOnlyProgramAux second state)
    | .mustTerminate body => wordStackOnlyProgramAux body state
    | .ite _ condition right thenBranch elseBranch =>
        let thenState := wordStackOnlyProgramAux thenBranch state
        let elseState := wordStackOnlyProgramAux elseBranch state
        let merged := wordStackOnlyMergeBranches state thenState elseState
        let conditionNames := condition :: match right with
          | .reg name => [name]
          | .imm _ => []
        wordStackOnlyRemoveTemps conditionNames merged
    | .loop _ body _ => wordStackOnlyProgramAux body state
    | .call returns _ _ handler =>
        match returns with
        | none => state
        | some (_, _, returnHandler, _, _) =>
            let returnState := wordStackOnlyProgramAux returnHandler state
            match handler with
            | none => returnState
            | some (_, handlerBody, _, _) =>
                let handlerState := wordStackOnlyProgramAux handlerBody state
                wordStackOnlyMergeBranches state returnState handlerState
    | .skip | .assign _ _ | .inst _ | .get _ _ | .store _ _ | .set _ _ |
        .raise _ | .return _ _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ |
        .shareInst _ _ _ | .alloc _ _ | .storeConsts _ _ _ _ _ |
        .opCurrHeap _ _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ |
        .dataBufferWrite _ _ | .break _ | .continue _ =>
        wordStackOnlyFallback program state

def wordStackOnly (program : WordProg α) : WordStackOnlyState :=
  wordStackOnlyProgramAux program { temporary := [], forced := [] }

def wordAllocateGraphFunctionWithStackOnly (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraph tree forced
      (wordStackOnlyUnion fixedSources stackOnly.forced)
      moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation,
        wordApplyColour (wordGraphColouringAt allocation.colouring) renamedProgram))

/-! Stack lowering consumes the SSA names together with a `WordLocation` map;
it must not consume the graph-coloured names, since those names erase the
identity needed by `word_to_stack` to perform loads and stores. -/
def wordAllocateGraphFunctionWithStackOnlyRenamed (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraph tree forced
      (wordStackOnlyUnion fixedSources stackOnly.forced)
      moves colours stackStart).map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

def wordAllocateGraphFunctionWithStackOnlyPrefreezeRenamed (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let stackOnly := wordStackOnly renamedProgram
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraphWithPrefreeze tree forced
      (wordStackOnlyUnion fixedSources stackOnly.forced)
      moves colours stackStart).map
    (fun allocation => (state, renamedParameters, allocation, renamedProgram))

def wordAllocateGraphFunctionWithEntryPrefreezeRenamed (parameters : List Nat)
    (program : WordProg α) (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordGraphAllocation × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordProgPreferenceEdges renamedProgram
  (wordAllocateGraphWithPrefreeze tree forced fixedSources moves colours stackStart).map
    (fun allocation => (state, renamedParameters, allocation, renamedProgram))

end Flapjack
