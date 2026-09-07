import Flapjack.Correctness

namespace Flapjack

/-! Executable source-to-Crepe call boundary.  The evaluator uses the
    flattened `CompiledFunction` table emitted by `compileToCrepe`; this
    regression keeps the declaration-call path tied to the source call
    semantics before the later Loop and Word bridges. -/

def crepCallContext : CompileContext (RiscV.Word 64) :=
  { vars := []
    functions := functionInfos pipelineCallDeclarations
    exceptions := []
    maxVar := 0
    bytesInWord := BitVec.ofNat 64 8 }

def crepCallFunctions : List (CompiledFunction (RiscV.Word 64)) :=
  compileToCrepe crepCallContext pipelineCallDeclarations

def crepCallLocals : Nat → Option (RiscV.Word 64) := fun _ => none

#guard
    (do
      let (_, main) ← lookupCompiledFunction "main" crepCallFunctions
      let (_, values) ← evalCrepStateProgWithFunctions crepCallFunctions 20
        crepCallLocals main
      pure values) = some [BitVec.ofNat 64 41]

#guard
    (do
      let (_, main) ← lookupCompiledFunction "main" crepCallFunctions
      let (_, values) ← evalCrepStateProgWithFunctions crepCallFunctions 20
        crepCallLocals main
      pure values) =
      (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
        pipelineCallSourceMain).map (fun result => result.2)

end Flapjack
