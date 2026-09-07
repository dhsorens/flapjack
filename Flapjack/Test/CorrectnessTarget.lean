import Flapjack.Correctness

namespace Flapjack

open RiscV

/-! Target-entry correctness regression for a declaration call.  The target
    wrapper moves `main` ahead of its callee, so this checks the actual linked
    image rather than the lower-level declaration-order fixture. -/

def pipelineCallTargetPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscVTarget (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineCallDeclarations

def pipelineCallTargetLinkedImage : Option (List (RiscV.Instruction 64)) :=
  pipelineCallTargetPipeline.callLinkedFunctions.map (fun entries =>
    entries.flatMap (fun item =>
      let (_, _, _, code, _) := item
      code))

def pipelineCallTargetImage : List (RiscV.Instruction 64) :=
  [.addi 3 0 0, .addi 4 0 (BitVec.ofNat 64 41),
   .addi 2 4 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
   .storeWord 1 30, .addi 31 0 (BitVec.ofNat 64 48), .jalr 1 31 0,
   .addi 3 4 0, .loadWord 1 30,
   .addi 30 30 (BitVec.ofNat 64 8), .addi 4 3 0,
   .jalr 0 1 0,
   .addi 4 2 0, .jalr 0 1 0]

theorem pipelineCallTargetLinkedImage_shape :
    pipelineCallTargetLinkedImage = some pipelineCallTargetImage := by
  native_decide

theorem pipelineCallTarget_word_semantics :
    (do
      let (_, main) ←
        RiscV.lookupWordFunction 1 pipelineCallTargetPipeline.pipeline.word
      let (_, values) ←
        RiscV.evalWordFunctionWithCalls pipelineCallTargetPipeline.pipeline.word
          30 (RiscV.zeroState 64) main
      pure values) = some [BitVec.ofNat 64 41] := by
  native_decide

def pipelineCallTargetLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

theorem pipelineCallTarget_loop_semantics :
    (do
      let (_, main) ←
        lookupLoopFunction 1 pipelineCallTargetPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions
        pipelineCallTargetPipeline.pipeline.loop 30
        pipelineCallTargetLoopState main
      pure (loopResultValues result)) =
      some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCallTarget_compiled_execution :
    RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 0 100 []
      pipelineCallTargetImage [4] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 100) =
      some [BitVec.ofNat 64 41] := by
  decide

theorem pipelineCallTarget_source_word_machine_agreement :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let (_, main) ←
          lookupLoopFunction 1 pipelineCallTargetPipeline.pipeline.loop
        let result ← evalLoopProgWithFunctions
          pipelineCallTargetPipeline.pipeline.loop 30
          pipelineCallTargetLoopState main
        pure (loopResultValues result)) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let (_, main) ←
          RiscV.lookupWordFunction 1 pipelineCallTargetPipeline.pipeline.word
        let (_, values) ←
          RiscV.evalWordFunctionWithCalls pipelineCallTargetPipeline.pipeline.word
            30 (RiscV.zeroState 64) main
        pure values) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let image ← pipelineCallTargetLinkedImage
        RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 0 100 []
          image [4] []
          (RiscV.writeRegister (RiscV.zeroState 64) 1 100)) =
        some [BitVec.ofNat 64 41] := by
  exact ⟨pipelineCall_source_semantics, pipelineCallTarget_loop_semantics,
    pipelineCallTarget_word_semantics, by
      rw [pipelineCallTargetLinkedImage_shape]
      exact pipelineCallTarget_compiled_execution⟩

end Flapjack
