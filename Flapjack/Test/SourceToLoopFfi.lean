import Flapjack.Test.CorrectnessFfi

/-!
Source-to-Loop FFI regression.

The source handler updates the declaration local named `result`; the generated
Loop handler must update that local's allocated slot instead.  The theorem
therefore exercises declaration lowering, FFI argument materialization, the
Loop FFI callback, and the caller's declaration-call continuation together.
-/

namespace Flapjack

open RiscV

def sourceToLoopFfiState : LoopState (Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopFfiHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some { state with
        locals := updateLoopLocal state.locals 2 (configuration + 1) }
    else none

theorem sourceToLoop_ffi_simulation :
    (do
      let (_, main) ← lookupLoopFunction 2 sourceFfiPipeline.pipeline.loop
      let result ← evalLoopProgWithCallsAndFfi sourceFfiPipeline.pipeline.loop
        sourceToLoopFfiHandler 60 sourceToLoopFfiState main
      pure (loopResultValues result)) =
      (evalPanProgWithCallsAndFfi sourceFfiFunctions sourceFfiHandler 20
        (fun _ : VarName => none) sourceFfiMainBody).map (fun result =>
          match result with
          | .returned _ values => values
          | _ => []) := by
  native_decide

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 sourceFfiPipeline.pipeline.loop
      let result ← evalLoopProgWithCallsAndFfi sourceFfiPipeline.pipeline.loop
        sourceToLoopFfiHandler 60 sourceToLoopFfiState main
      pure (loopResultValues result)) = some [BitVec.ofNat 64 42]

end Flapjack
