import Flapjack.Pipeline
import Flapjack.RiscV.PanSemantics

namespace Flapjack

def primitivePipelineDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .dec "result" (.comb [.one, .one])
        (.rStruct [.const 0, .const 0])
        (.seq
          (.primitive "result" .addCarry
            [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
              .const (BitVec.ofNat 64 0)])
          (.return (.rField 0 (.var .local "result")))),
      returnShape := .one }]

def primitivePipeline :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    primitivePipelineDeclarations

def primitivePipelineRun : Option (List (RiscV.Word 64)) :=
  match primitivePipeline.functions with
  | [(_, parameters, some (code, returns))] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 200 0 parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def primitivePipelineCallLinkedRun : Option (List (RiscV.Word 64)) :=
  match primitivePipeline.callLinkedFunctions with
  | some [(_, _, parameters, code, returns)] =>
      let returnAddress := BitVec.ofNat 64 (4 * code.length)
      RiscV.executeFunctionAt 300 0 0 returnAddress
        (parameters.mapM RiscV.registerOfNat |>.getD []) code returns []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 returnAddress)
  | _ => none

def primitivePipelineSource : Prog (RiscV.Word 64) :=
  .dec "result" (.comb [.one, .one])
    (.rStruct [.const 0, .const 0])
    (.seq
      (.primitive "result" .addCarry
        [.const 1, .const 2, .const 0])
      (.return (.rField 0 (.var .local "result"))))

theorem primitivePipeline_source_correct :
    (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
      (fun _ => none) (fun _ => none) (fun _ => none)
      RiscV.panPrimitiveHandler primitivePipelineSource).map
        (fun result =>
          match result.2.2.2 with
          | [.word value] => some value
          | _ => none) =
      some (some (BitVec.ofNat 64 3)) := by
  decide +kernel

theorem primitivePipeline_full_source_correct :
    (evalPanValueProgWithPrimitiveCallsAndFfi
      (α := RiscV.Word 64) RiscV.panPrimitiveHandler
      (fun _ _ _ _ _ _ => none) [] [] 0 100 8 40
      (fun _ => none) (fun _ => none) (fun _ => none)
      primitivePipelineSource).map
        (fun result =>
          match result with
          | .returned _ _ _ [.word value] => some value
          | _ => none) =
      some (some (BitVec.ofNat 64 3)) := by
  decide +kernel

#guard
    primitivePipelineRun =
      (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
        (fun _ => none) (fun _ => none) (fun _ => none)
        RiscV.panPrimitiveHandler primitivePipelineSource).map
        (fun result =>
          match result.2.2.2 with
          | [.word value] => [value]
          | _ => [])

#guard
    primitivePipelineRun =
      (evalPanValueProgWithPrimitiveCallsAndFfi
        (α := RiscV.Word 64) RiscV.panPrimitiveHandler
        (fun _ _ _ _ _ _ => none) [] [] 0 100 8 40
        (fun _ => none) (fun _ => none) (fun _ => none)
        primitivePipelineSource).map
        (fun result =>
          match result with
          | .returned _ _ _ values => values.map (fun value =>
              match value with
              | .word value => value
              | _ => 0)
          | _ => [])

def primitiveCallSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("produce", [],
      .dec "result" (.comb [.one, .one])
        (.rStruct [.const 0, .const 0])
        (.seq
          (.primitive "result" .addCarry
            [.const 1, .const 2, .const 0])
          (.return (.rField 0 (.var .local "result")))))]

def primitiveCallSource : Prog (RiscV.Word 64) :=
  .decCall "out" .one "produce" []
    (.return (.var .local "out"))

theorem primitiveCall_full_source_correct :
    (evalPanValueProgWithPrimitiveCallsAndFfi
      (α := RiscV.Word 64) RiscV.panPrimitiveHandler
      (fun _ _ _ _ _ _ => none) [] primitiveCallSourceFunctions 0 100 8 50
      (fun _ => none) (fun _ => none) (fun _ => none)
      primitiveCallSource).map
        (fun result =>
          match result with
          | .returned _ _ _ [.word value] => some value
          | _ => none) =
      some (some (BitVec.ofNat 64 3)) := by
  decide +kernel

#guard
    primitivePipelineCallLinkedRun = some [BitVec.ofNat 64 3]

end Flapjack
