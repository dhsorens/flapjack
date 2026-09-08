import Flapjack.Test.SourceToLoop

/-!
Source-to-Loop call regression.

This keeps the source call evaluator and the generated Loop function table in
the same executable test.  The callee is deliberately small, but the caller
goes through the real declaration-call lowering and therefore exercises
function labels, argument temporaries, return-slot assignment, and the
continuation after the call.
-/

namespace Flapjack

open RiscV

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 pipelineCallPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions pipelineCallPipeline.pipeline.loop
        40 sourceToLoopState main
      pure (loopResultValues result)) =
      (evalPanProgWithCalls pipelineCallSourceFunctions 20
        (fun _ : VarName => none) pipelineCallSourceMain).map
          (fun result => result.2)

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 pipelineCallPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions pipelineCallPipeline.pipeline.loop
        40 sourceToLoopState main
      pure (loopResultValues result)) = some [BitVec.ofNat 64 41]

end Flapjack
