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

def wordRaRemoveNode (colours : Nat) (node : Nat)
    (forceSpill : Bool) (state : WordRaState) : WordRaState :=
  let graph := if forceSpill then
      { state.graph with tags :=
          wordGraphUpdateTag node .stemp state.graph.tags }
    else
      state.graph
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
  wordRaRefreshWorklists colours state

def wordRaSimplifyAll : Nat → Nat → WordRaState → WordRaState
  | 0, _, state => state
  | fuel + 1, colours, state =>
      match state.simpWl with
      | node :: _ =>
          wordRaSimplifyAll fuel colours
            (wordRaRemoveNode colours node false state)
      | [] =>
          match state.spillWl with
          | node :: _ =>
              wordRaSimplifyAll fuel colours
                (wordRaRemoveNode colours node true state)
          | [] => state

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

def wordRaColourStack (colours stackStart : Nat) :
    List Nat → WordRegGraph → WordRegGraph
  | [], graph => graph
  | node :: nodes, graph =>
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

structure WordMoveState where
  graph : WordRegGraph
  parents : NatInfoMap Nat
  related : List Nat
  available : List WordMove
  unavailable : List WordMove
  freezeWl : List Nat
  stack : List Nat
  deriving Repr

def wordMoveRefreshFreeze (colours : Nat) (state : WordMoveState) :
    WordMoveState :=
  let related := wordMoveRelatedNodes (state.available ++ state.unavailable)
  { state with
    related := related
    freezeWl := wordMoveFreezeCandidates colours state.graph
      state.parents related }

def wordInitMoveState (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveState :=
  let worklists := wordPrepareMoveWorklists graph moves
  { graph := graph
    parents := (List.range graph.dimension).map (fun node => (node, node))
    related := wordMoveRelatedNodes moves
    available := worklists.available
    unavailable := worklists.unavailable
    freezeWl := []
    stack := [] }

def wordInitMoveStateWithColours (colours : Nat) (graph : WordRegGraph)
    (moves : List WordMove) : WordMoveState :=
  let worklists := wordPrepareMoveWorklistsWithColours colours graph moves
  let parents := (List.range graph.dimension).map (fun node => (node, node))
  let related := wordMoveRelatedNodes moves
  { graph := graph
    parents := parents
    related := related
    available := worklists.available
    unavailable := worklists.unavailable
    freezeWl := wordMoveFreezeCandidates colours graph parents related
    stack := [] }

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

def wordCoalesceMove (colours : Nat) (state : WordMoveState)
    (move : WordMove) : Option WordMoveState :=
  let (move, parents) := wordResolveMove state move
  let state := { state with parents := parents }
  let move := wordCanonicalizeMove state.graph move
  if !wordCoalesceSafe colours state.graph state.related move then
    none
  else
    let fresh := wordCoalesceFreshNeighbours
      state.graph move.left move.right
    let graph := fresh.foldl
      (fun graph node => wordGraphInsertEdge move.left node graph)
      state.graph
    let parents := wordParentUpdate move.right move.left state.parents
    let pending := (state.available ++ state.unavailable).map
      (wordMoveReplaceNode move.right move.left)
    let worklists := wordPrepareMoveWorklists graph pending
    some
      { graph := graph
        parents := parents
        related := wordMoveRelatedNodes pending
        available := worklists.available
        unavailable := worklists.unavailable
        freezeWl := wordMoveFreezeCandidates colours graph parents
          (wordMoveRelatedNodes pending)
        stack := move.right :: state.stack }

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
  let state := { state with
    available := available
    unavailable := unavailable
    stack := if node ∈ state.stack then state.stack else node :: state.stack }
  wordMoveRefreshFreeze colours state

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

def wordAllocateGraph (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves : List (Nat × Nat)) (colours stackStart : Nat) :
    Option WordGraphAllocation :=
  let input := wordInitRegAlloc tree forced fixedSources
  let moveState := wordInitMoveStateWithColours colours input.graph
    (wordPreferenceMoves moves)
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklist colours stackStart moveState.graph
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
  let moveState := wordInitMoveStateWithColours colours input.graph moves
  let moveState := wordCoalesceAllAvailable colours moveState
  let moveState := wordFreezeAllAvailable colours moveState
  let graph := wordColourGraphWithWorklist colours stackStart moveState.graph
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

def wordStackOnlyTerminalVars (program : WordProg α) : List Nat :=
  wordProgVariables program

def wordStackOnlyProgramAux (program : WordProg α)
      (state : WordStackOnlyState) : WordStackOnlyState :=
    match program with
    | .assign destination (.var source) =>
        wordStackOnlyMergeMove destination source state
    | .move _ moves =>
        moves.foldl (fun state move =>
          wordStackOnlyMergeMove move.1 move.2 state) state
    | .assign _ _ | .inst _ | .get _ _ | .store _ _ | .set _ _ | .raise _ |
        .return _ _ | .tick | .locValue _ _ | .ffi _ _ _ _ _ _ |
        .shareInst _ _ _ | .alloc _ _ | .storeConsts _ _ _ _ _ |
        .opCurrHeap _ _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ |
        .dataBufferWrite _ _ =>
        wordStackOnlyRemoveTemps (wordStackOnlyTerminalVars program) state
    | .skip => wordStackOnlyRemoveTemps [] state
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
    | .break _ | .continue _ =>
        wordStackOnlyRemoveTemps (wordStackOnlyTerminalVars program) state
    | .call returns _ arguments handler =>
        let state := match handler with
          | none => state
          | some (_, body, _, _) => wordStackOnlyProgramAux body state
        let returnNames := match returns with
          | none => []
          | some (values, cutsets, _, _, _) =>
              values ++ cutsets.1 ++ cutsets.2
        wordStackOnlyRemoveTemps (arguments ++ returnNames) state

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

end Flapjack
