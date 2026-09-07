import Flapjack.RiscV.SpillCosts
import Flapjack.RiscV.AllocatorDriver

/-!
# Heuristic function-allocation driver

This is the executable composition corresponding to CakeML's allocator
decision boundary: an accepted oracle wins first, then the prioritized graph
allocator is attempted, and finally the checked spill allocator is used.  The
linear-scan and Simple/IRC distinctions remain explicit future work; the
current graph engine is the implementation used by this boundary.
-/

namespace Flapjack

def wordAllocateFunctionWithOracleOrHeuristicOrSpill
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else
    match wordAllocateGraphFunctionWithHeuristics parameters program fixedSources
        algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

def wordHeuristicDriverUsesOracle
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsOracle result

def wordHeuristicDriverUsesGraph
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsGraph result

def wordHeuristicDriverUsesSpill
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsSpill result

end Flapjack
