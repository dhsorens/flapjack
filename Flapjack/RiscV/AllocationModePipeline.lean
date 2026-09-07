import Flapjack.RiscV.HeuristicPipeline
import Flapjack.RiscV.LinearScanPipeline

/-!
# CakeML allocation-mode dispatch

CakeML encodes allocator selection numerically: modes 0--3 select Simple or
IRC, with odd modes enabling spill heuristics, and modes 4 and above select
linear scan.  The numeric decoding is kept explicit here.  The checked graph
path currently backs all modes below 4; the exact Simple-versus-IRC worklist
distinction remains tracked as part of the full allocator port.
-/

namespace Flapjack

inductive WordAllocationAlgorithm where
  | simple
  | simpleHeuristic
  | irc
  | ircHeuristic
  | linearScan
  deriving DecidableEq, Repr

def wordAllocationAlgorithmOfNat : Nat → WordAllocationAlgorithm
  | 0 => .simple
  | 1 => .simpleHeuristic
  | 2 => .irc
  | 3 => .ircHeuristic
  | _ + 4 => .linearScan

def wordAllocationAlgorithmUsesHeuristics :
    WordAllocationAlgorithm → Bool
  | .simple | .irc => false
  | .simpleHeuristic | .ircHeuristic => true
  | .linearScan => false

def wordAllocationAlgorithmIsLinearScan :
    WordAllocationAlgorithm → Bool
  | .linearScan => true
  | .simple | .simpleHeuristic | .irc | .ircHeuristic => false

def wordAllocationAlgorithmIsLinearScanNat (algorithm : Nat) : Bool :=
  wordAllocationAlgorithmIsLinearScan
    (wordAllocationAlgorithmOfNat algorithm)

def pipelineWordFunctionsAllocatedWithSourceAlgorithm [NeZero width]
    (algorithm : Nat) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | functions =>
      if wordAllocationAlgorithmIsLinearScanNat algorithm then
        pipelineWordFunctionsAllocatedWithLinearScan functions
      else
        pipelineWordFunctionsAllocatedWithHeuristics algorithm functions

def compileFlapjackRiscVViaSourceAlgorithmStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (algorithm : Nat) (architecture : RiscV.Architecture)
    (bytesInWord : RiscV.Word width) (fromNat : Nat → RiscV.Word width)
    (services : List (FunName × Nat)) (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSourceAlgorithm algorithm
    pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

end Flapjack
