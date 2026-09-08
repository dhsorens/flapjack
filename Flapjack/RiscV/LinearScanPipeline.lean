import Flapjack.Pipeline
import Flapjack.RiscV.LinearScanDriver

/-!
# RISC-V pipeline using linear-scan allocation

The entry point below is intentionally parallel to the graph/spill pipeline:
front-end compilation produces LoopLang functions, each function is lowered
to Word, SSA-renamed and linearly allocated, then the existing Word-to-Stack
and StackRemove stages emit RISC-V code.
-/

namespace Flapjack

def pipelineWordFunctionsAllocatedWithLinearScan [NeZero width]
    : List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := loopToWordProg context body
      let (_, renamedParameters, allocation, renamedBody) ←
        wordAllocateLinearScanFunctionWithEntry wordParameters unallocatedBody 13 14
      let config : RiscV.WordStackConfig :=
        { locations := wordLinearScanLocations allocation
          scratch := 31
          stackBase := 0
          addressScratch := 29 }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config
        renamedParameters renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithLinearScan functions
      pure ((label, wordParameters, stackBody) :: rest)

def compileFlapjackRiscVViaLinearScanStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture)
    (bytesInWord : RiscV.Word width) (fromNat : Nat → RiscV.Word width)
    (services : List (FunName × Nat)) (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithLinearScan pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

end Flapjack
