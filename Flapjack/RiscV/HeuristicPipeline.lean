import Flapjack.Pipeline
import Flapjack.RiscV.SpillCosts

/-!
# Heuristic-allocated RISC-V pipeline

This entry point threads the CakeML heuristic allocator through the existing
Word-to-Stack and StackRemove stages.  The function label is used as the
heuristic call context; the allocator mode is kept as an explicit argument.
The underlying graph engine is currently the checked implementation for the
supported modes.
-/

namespace Flapjack

def pipelineWordFunctionsAllocatedWithHeuristics [NeZero width]
    (algorithm : Nat) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := loopToWordProg context body
      let (_, renamedParameters, allocation, renamedBody) ←
        wordAllocateGraphFunctionWithHeuristicsRenamed wordParameters unallocatedBody
          [] algorithm label 13 14
      let config : RiscV.WordStackConfig :=
        { locations := wordGraphLocations allocation 13 14
          scratch := 31
          stackBase := 0
          addressScratch := 29 }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config
        renamedParameters renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithHeuristics algorithm functions
      pure ((label, wordParameters, stackBody) :: rest)

def compileFlapjackRiscVViaHeuristicAllocatedStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (algorithm : Nat) (architecture : RiscV.Architecture)
    (bytesInWord : RiscV.Word width) (fromNat : Nat → RiscV.Word width)
    (services : List (FunName × Nat)) (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithHeuristics algorithm pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

end Flapjack
