import Flapjack.Pipeline
import Flapjack.Semantics
import Flapjack.PanValues
import Flapjack.LoopSemantics
import Flapjack.RiscV.Backend
import Flapjack.WordSemantics

/-!
Initial end-to-end correctness theorem for the executable Flapjack pipeline.

This module deliberately starts with a small, fully parameterized RV64
function. It connects the source Pancake evaluator to the artifact emitted by
the complete front-end/Loop/Word/RISC-V composition; larger simulation
relations can be added beside this theorem as more instructions and states are
ported.
-/

namespace Flapjack

def pipelineAddDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "add", inline := false, exported := false,
      params := [("left", .one), ("right", .one)],
      body := .return (.op .add
        [.var .local "left", .var .local "right"]), returnShape := .one }]

def pipelineAddPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineAddDeclarations

def pipelineAddFunctions := pipelineAddPipeline.functions

def pipelineAddLinkedFunctions := pipelineAddPipeline.linkedFunctions

theorem pipelineAddFunctions_shape :
    pipelineAddFunctions =
      [(1, [2, 3], some ([.add 5 2 3], [5]))] := by
  native_decide

theorem pipelineAddLinkedFunctions_shape :
    pipelineAddLinkedFunctions =
      some [(1, 0, [2, 3], [.add 5 2 3], [5])] := by
  change RiscV.linkRiscVFunctions 0 pipelineAddFunctions = _
  rw [pipelineAddFunctions_shape]
  rfl

def compiledPipelineAddRun (left right : RiscV.Word 64) :
    Option (List (RiscV.Word 64)) :=
  match pipelineAddLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns
            [left, right] (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineAddSource (_left _right : RiscV.Word 64) : Prog (RiscV.Word 64) :=
  .return (.op .add [.var .local "left", .var .local "right"])

def pipelineAddLocals (left right : RiscV.Word 64) :
    VarName → Option (RiscV.Word 64) :=
  fun name => if name == "left" then some left
    else if name == "right" then some right else none

theorem compiledPipelineAdd_correct (left right : RiscV.Word 64) :
    compiledPipelineAddRun left right =
      evalPanProg (pipelineAddLocals left right) (pipelineAddSource left right) := by
  simp [compiledPipelineAddRun, pipelineAddLinkedFunctions_shape,
    pipelineAddSource, pipelineAddLocals, evalPanProg, evalPanExp]
  exact RiscV.executeFunction_add_general left right

def pipelineMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := false, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)]),
      returnShape := .one }]

def pipelineMulPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineMulDeclarations

def pipelineMulLinkedFunctions := pipelineMulPipeline.linkedFunctions

theorem pipelineMulFunctions_shape :
    pipelineMulPipeline.functions =
      [(1, [], some ([.addi 3 0 (BitVec.ofNat 64 2),
        .addi 4 0 (BitVec.ofNat 64 3), .mulHU 5 3 4, .mul 5 3 4,
        .addi 6 5 0], [6]))] := by
  native_decide

theorem pipelineMulLinkedFunctions_shape :
    pipelineMulLinkedFunctions =
      some [(1, 0, [],
        [.addi 3 0 (BitVec.ofNat 64 2), .addi 4 0 (BitVec.ofNat 64 3),
          .mulHU 5 3 4, .mul 5 3 4, .addi 6 5 0], [6])] := by
  change RiscV.linkRiscVFunctions 0 pipelineMulPipeline.functions = _
  rw [pipelineMulFunctions_shape]
  rfl

def compiledPipelineMulRun : Option (List (RiscV.Word 64)) :=
  match pipelineMulLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineMulSource : Prog (RiscV.Word 64) :=
  .return (.panOp .mul
    [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)])

#guard
    compiledPipelineMulRun =
      evalPanProg (fun _ => none) pipelineMulSource

def pipelineSubDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "sub", inline := false, exported := false, params := [],
      body := .return (.op .sub
        [.const (BitVec.ofNat 64 9), .const (BitVec.ofNat 64 4)]),
      returnShape := .one }]

def pipelineSubPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineSubDeclarations

def compiledPipelineSubRun : Option (List (RiscV.Word 64)) :=
  match pipelineSubPipeline.linkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineSubSource : Prog (RiscV.Word 64) :=
  .return (.op .sub
    [.const (BitVec.ofNat 64 9), .const (BitVec.ofNat 64 4)])

#guard
    compiledPipelineSubRun =
      evalPanProg (fun _ => none) pipelineSubSource

def pipelineBitwiseDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "bitwise", inline := false, exported := false, params := [],
      body := .return (.op .and
        [.const (BitVec.ofNat 64 13), .const (BitVec.ofNat 64 7)]),
      returnShape := .one }]

def pipelineBitwisePipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineBitwiseDeclarations

def compiledPipelineBitwiseRun : Option (List (RiscV.Word 64)) :=
  match pipelineBitwisePipeline.linkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineBitwiseSource : Prog (RiscV.Word 64) :=
  .return (.op .and
    [.const (BitVec.ofNat 64 13), .const (BitVec.ofNat 64 7)])

#guard
    compiledPipelineBitwiseRun =
      evalPanProg (fun _ => none) pipelineBitwiseSource

def pipelineStoreLoadDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "storeLoad", inline := false, exported := true, params := [],
      body := .seq
        (.store (.const (BitVec.ofNat 64 100))
          (.const (BitVec.ofNat 64 42)))
        (.return (.load .one (.const (BitVec.ofNat 64 100)))),
      returnShape := .one }]

def pipelineStoreLoadPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineStoreLoadDeclarations

def compiledPipelineStoreLoadRun : Option (List (RiscV.Word 64)) :=
  match pipelineStoreLoadPipeline.functions with
  | [(_, _, some (code, returns))] =>
      RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
        (RiscV.zeroState 64)
  | _ => none

def pipelineStoreLoadSource : Prog (RiscV.Word 64) :=
  .seq
    (.store (.const (BitVec.ofNat 64 100))
      (.const (BitVec.ofNat 64 42)))
    (.return (.load .one (.const (BitVec.ofNat 64 100))))

#guard
    compiledPipelineStoreLoadRun =
      evalPanMemResult (fun _ => none) (fun _ => none)
        pipelineStoreLoadSource

def pipelineIteDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "ite", inline := false, exported := false, params := [],
      body := .ite (.const (BitVec.ofNat 64 1))
        (.return (.const (BitVec.ofNat 64 7)))
        (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]

def pipelineItePipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineIteDeclarations

def compiledPipelineIteRun : Option (List (RiscV.Word 64)) :=
  match pipelineItePipeline.linkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 40 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineIteSource : Prog (RiscV.Word 64) :=
  .ite (.const (BitVec.ofNat 64 1))
    (.return (.const (BitVec.ofNat 64 7)))
    (.return (.const (BitVec.ofNat 64 8)))

#guard
    compiledPipelineIteRun =
      evalPanProg (fun _ => none) pipelineIteSource

def pipelineCompareIteDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "compareIte", inline := false, exported := false,
      params := [("left", .one), ("right", .one)],
      body := .ite (.cmp .equal (.var .local "left") (.var .local "right"))
        (.return (.const (BitVec.ofNat 64 7)))
        (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]

def pipelineCompareItePipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineCompareIteDeclarations

theorem pipelineCompareIteFunctions_shape :
    pipelineCompareItePipeline.functions =
      [(1, [2, 3], some (
        [.addi 5 2 0, .addi 6 3 0,
         .branchNe 5 6 (BitVec.ofNat 64 12),
         .addi 5 0 1, .branchEq 0 0 (BitVec.ofNat 64 8),
         .addi 5 0 0, .addi 0 0 0, .addi 7 5 0,
         .branchEq 7 0 (BitVec.ofNat 64 12),
         .addi 5 0 7, .branchEq 0 0 (BitVec.ofNat 64 8),
         .addi 5 0 8], [5]))] := by
  native_decide

theorem pipelineCompareIteLinkedFunctions_shape :
    pipelineCompareItePipeline.linkedFunctions =
      some [(1, 0, [2, 3],
        [.addi 5 2 0, .addi 6 3 0,
         .branchNe 5 6 (BitVec.ofNat 64 12),
         .addi 5 0 1, .branchEq 0 0 (BitVec.ofNat 64 8),
         .addi 5 0 0, .addi 0 0 0, .addi 7 5 0,
         .branchEq 7 0 (BitVec.ofNat 64 12),
         .addi 5 0 7, .branchEq 0 0 (BitVec.ofNat 64 8),
         .addi 5 0 8], [5])] := by
  change RiscV.linkRiscVFunctions 0 pipelineCompareItePipeline.functions = _
  rw [pipelineCompareIteFunctions_shape]
  rfl

def compiledPipelineCompareIteRun
    (left right : RiscV.Word 64) : Option (List (RiscV.Word 64)) :=
  match pipelineCompareItePipeline.linkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 20 entry parameters code returns
            [left, right] (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineCompareIteSource (_left _right : RiscV.Word 64) : Prog (RiscV.Word 64) :=
  .ite (.cmp .equal (.var .local "left") (.var .local "right"))
    (.return (.const (BitVec.ofNat 64 7)))
    (.return (.const (BitVec.ofNat 64 8)))

def pipelineCompareIteLocals (left right : RiscV.Word 64) :
    VarName → Option (RiscV.Word 64) :=
  fun name => if name == "left" then some left
    else if name == "right" then some right else none

#guard
    compiledPipelineCompareIteRun (BitVec.ofNat 64 9) (BitVec.ofNat 64 9) =
      evalPanProg (pipelineCompareIteLocals 9 9)
        (pipelineCompareIteSource 9 9)

#guard
    compiledPipelineCompareIteRun (BitVec.ofNat 64 9) (BitVec.ofNat 64 10) =
      evalPanProg (pipelineCompareIteLocals 9 10)
        (pipelineCompareIteSource 9 10)

/-!
The first end-to-end call regression. The source program uses a declaration
call rather than an unbound low-level call, so the static front end allocates
the result local and the call-aware linker can recover the callee's return
layout. The concrete image also checks the ordinary-call link register
save/restore sequence.
-/
def pipelineCallDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "result")), returnShape := .one }]

def pipelineCallPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineCallDeclarations

#guard
    pipelineCallPipeline.callLinkedFunctions.isSome

def pipelineCallImage : List (RiscV.Instruction 64) :=
  [.addi 4 2 0, .jalr 0 1 0,
   .addi 3 0 0, .addi 4 0 (BitVec.ofNat 64 41),
   .addi 2 4 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
   .storeWord 1 30, .addi 31 0 0, .jalr 1 31 0,
   .addi 3 4 0, .loadWord 1 30,
   .addi 30 30 (BitVec.ofNat 64 8), .addi 4 3 0,
   .jalr 0 1 0]

def pipelineCallLinkedImage : Option (List (RiscV.Instruction 64)) :=
  pipelineCallPipeline.callLinkedFunctions.map (fun entries =>
    entries.flatMap (fun item =>
      let (_, _, _, code, _) := item
      code))

theorem pipelineCallLinkedImage_shape :
    pipelineCallLinkedImage = some pipelineCallImage := by
  native_decide

theorem pipelineCall_word_semantics :
    (do
      let (_, main) ←
        RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
      let (_, values) ←
        RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
          30 (RiscV.zeroState 64) main
      pure values) = some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCall_compiled_execution :
    RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
      pipelineCallImage [4] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 100) =
      some [BitVec.ofNat 64 41] := by
  decide

theorem pipelineCall_generated_compiled_execution :
    (do
      let image ← pipelineCallLinkedImage
      RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
        image [4] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 100)) =
      some [BitVec.ofNat 64 41] := by
  rw [pipelineCallLinkedImage_shape]
  exact pipelineCall_compiled_execution

def pipelineCallSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def pipelineCallSourceMain : Prog (RiscV.Word 64) :=
  .decCall "result" .one "id"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "result"))

theorem pipelineCall_source_semantics :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
      some [BitVec.ofNat 64 41] := by
  decide +kernel

def pipelineStructuredNoFfi : PanValueFfiHandler (RiscV.Word 64) :=
  fun _ _ _ _ _ _ => none

theorem pipelineCall_structured_source_semantics :
    (evalPanValueProgWithCallsAndFfi (α := RiscV.Word 64) []
      pipelineCallSourceFunctions pipelineStructuredNoFfi
      0 (BitVec.ofNat 64 100) 8 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      pipelineCallSourceMain).map (fun result =>
        match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some (BitVec.ofNat 64 41)) := by
  decide +kernel

def pipelineHandlerSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("raise", [], .raise "E" (.const (BitVec.ofNat 64 7)))]

def pipelineHandlerSourceMain : Prog (RiscV.Word 64) :=
  .call
    (some (none, some ("E", "exception",
      .return (.var .local "exception"))))
    "raise" []

theorem pipelineHandler_source_semantics :
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20 (fun _ => none)
      pipelineHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 7] := by
  decide +kernel

def pipelineFfiHandler :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      (VarName → Option (RiscV.Word 64)) →
      Option (VarName → Option (RiscV.Word 64)) :=
  fun function configuration _ array _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + array + 1))
    else none

def pipelineFfiSource : Prog (RiscV.Word 64) :=
  .extCall "inc"
    (.const (BitVec.ofNat 64 41)) (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))

theorem pipelineFfi_source_semantics :
    (evalPanFfiProg pipelineFfiHandler (fun _ => none) pipelineFfiSource).map
      (fun locals => locals "result") = some (some (BitVec.ofNat 64 42)) := by
  decide

def pipelineFfiCallFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("ffiId", ["x"],
      .seq
        (.extCall "inc" (.var .local "x") (.const 0)
          (.const 0) (.const 0))
        (.return (.var .local "result")))]

def pipelineFfiCallMain : Prog (RiscV.Word 64) :=
  .decCall "answer" .one "ffiId"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "answer"))

theorem pipelineFfi_call_source_semantics :
    (evalPanProgWithCallsAndFfi pipelineFfiCallFunctions pipelineFfiHandler 50
      (fun _ => none) pipelineFfiCallMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42] := by
  decide +kernel

def pipelineStructuredFfiHandler :
    PanValueFfiHandler (RiscV.Word 64) :=
  fun function configuration _ array _ locals =>
    if function == "inc" then
      some (updatePanValueMap locals "result"
        (.word (configuration + array + 1)))
    else none

theorem pipelineFfi_structured_call_source_semantics :
    (evalPanValueProgWithCallsAndFfi (α := RiscV.Word 64) []
      pipelineFfiCallFunctions pipelineStructuredFfiHandler
      0 (BitVec.ofNat 64 100) 8 50
      (fun _ => none) (fun _ => none) (fun _ => none)
      pipelineFfiCallMain).map (fun result =>
        match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some (BitVec.ofNat 64 42)) := by
  decide +kernel

theorem pipelineCall_source_word_machine_agreement :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let (_, main) ←
          RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
        let (_, values) ←
          RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
            30 (RiscV.zeroState 64) main
        pure values) = some [BitVec.ofNat 64 41] ∧
      (do
        let image ← pipelineCallLinkedImage
        RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
          image [4] []
          (RiscV.writeRegister (RiscV.zeroState 64) 1 100)) =
        some [BitVec.ofNat 64 41] := by
  exact ⟨pipelineCall_source_semantics, pipelineCall_word_semantics,
    pipelineCall_generated_compiled_execution⟩

/-!
This is the first pass-composed semantic bridge.  It relates a Pancake
constant return to the result of the actual `compileProg` and
`loopCompileProg` passes, using the executable Loop evaluator.  The fixed fuel
bound is sufficient for the generated temporary-assignment sequence and is
deliberately explicit until a general fuel monotonicity theorem is available.
-/
theorem compilePanToLoop_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (value : α) :
    (evalLoopProg 12 state
      (loopCompileProg loopContext live
        (compileProg compileContext (.return (.const value))))).map loopResultValues =
      evalPanProg (fun _ => none) (.return (.const value)) := by
  simp [compileProg, compileExp, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, loopResultValues, evalPanProg,
    evalPanExp]

/-!
The same pass-composed bridge also covers a constant binary operation.  This
is the first source-to-Loop theorem that checks expression lowering beyond a
literal: Pancake's `add` is represented by a Crepe operation and evaluated by
the corresponding Loop operation.
-/
theorem compilePanToLoop_return_add_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (left right : α) :
    (evalLoopProg 12 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.return (.op .add [.const left, .const right]))))).map
        loopResultValues =
      evalPanProg (fun _ => none)
        (.return (.op .add [.const left, .const right])) := by
  simp [compileProg, compileExp,
    loopCompileProg, loopCompileExp,
    compileExp.compileExpList, cexpHeads, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    evalLoopBinOp, loopReadLocals, updateLoopLocal, loopResultValues,
    evalPanProg, evalPanExp, evalPanBinOp]

/-!
Pancake multiplication takes the Crepe `crepOp` path and is expanded by the
Loop compiler into the same-destination `longMul` operation.  This bridge
checks that expansion at the executable Loop level, before the later
Loop-to-Word/RISC-V simulation layers.
-/
theorem compilePanToLoop_return_mul_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (left right : α) :
    (evalLoopProg 16 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.return (.panOp .mul [.const left, .const right]))))).map
        loopResultValues =
      evalPanProg (fun _ => none)
        (.return (.panOp .mul [.const left, .const right])) := by
  let argsResult : LoopCompileExpsResult α :=
    { expressions := [.const left, .const right], code := [],
      nextTemp := loopContext.maxVar + 1, live := live }
  have hargs :
      loopCompileExp.loopCompileExps loopContext (loopContext.maxVar + 1) live
        [.const left, .const right] = argsResult := by
    rw [loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_1]
    rfl
  have hargsExpressions :
      (loopCompileExp.loopCompileExps loopContext (loopContext.maxVar + 1) live
        [.const left, .const right]).expressions =
        [.const left, .const right] := by
    simpa [argsResult] using congrArg (fun result => result.expressions) hargs
  have hmulExp :
      loopCompileExp loopContext (loopContext.maxVar + 1) live
        (.crepOp .mul [.const left, .const right]) =
      { code := argsResult.code ++
          [.assign argsResult.nextTemp (.const left),
           .assign (argsResult.nextTemp + 1) (.const right),
           .arith (.longMul (argsResult.nextTemp + 1 + 1)
             (argsResult.nextTemp + 1 + 1) argsResult.nextTemp
             (argsResult.nextTemp + 1))],
        expression := .var (argsResult.nextTemp + 1 + 1),
        nextTemp := argsResult.nextTemp + 1 + 1 + 1,
        live := (argsResult.nextTemp + 1 + 1) :: argsResult.nextTemp ::
          (argsResult.nextTemp + 1) :: argsResult.live } := by
    rw [loopCompileExp.eq_8 (context := loopContext)
      (tmp := loopContext.maxVar + 1) (live := live)
      (arguments := [.const left, .const right])
      (left := .const left) (right := .const right) hargsExpressions]
    rw [hargs]
  have hmulList :
      loopCompileExp.loopCompileExps loopContext (loopContext.maxVar + 1) live
        [.crepOp .mul [.const left, .const right]] =
      { expressions :=
          [(loopCompileExp loopContext (loopContext.maxVar + 1) live
            (.crepOp .mul [.const left, .const right])).expression],
        code := (loopCompileExp loopContext (loopContext.maxVar + 1) live
          (.crepOp .mul [.const left, .const right])).code,
        nextTemp := (loopCompileExp loopContext (loopContext.maxVar + 1) live
          (.crepOp .mul [.const left, .const right])).nextTemp,
        live := (loopCompileExp loopContext (loopContext.maxVar + 1) live
          (.crepOp .mul [.const left, .const right])).live } := by
    rw [loopCompileExp.loopCompileExps.eq_2,
      loopCompileExp.loopCompileExps.eq_1]
    simp
  simp [compileProg, compileExp, compilePanOp, compileExp.compileExpList,
    cexpHeads, loopCompileProg, loopCompileExps, hmulList, hmulExp, argsResult]
  simp [loopNestedSeq, loopTempNames, loopAssignTemps, evalLoopProg,
    evalLoopExp, loopReadLocals, updateLoopLocal, loopResultValues,
    evalPanProg, evalPanExp]

/-!
Comparison lowering materializes both operands and executes the selected
condition in a Loop ite.  This equality case is the first source-to-Loop
bridge that checks the generated control flow as well as expression values.
-/
theorem compilePanToLoop_return_equal_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (left right : α) :
    (evalLoopProg 30 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.return (.cmp .equal (.const left) (.const right)))))).map
        loopResultValues =
      evalPanProg (fun _ => none)
        (.return (.cmp .equal (.const left) (.const right))) := by
  simp [compileProg, compileExp, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    evalLoopCondition, loopReadLocals, updateLoopLocal, evalPanProg,
    evalPanExp, evalPanCmp]
  by_cases h : left == right <;>
    simp [h, updateLoopLocal]
  all_goals rfl

/-!
The previous comparison bridge is used here as a condition: compiling a
constant Pancake conditional must materialize the comparison, branch in Loop,
and then preserve the selected return value.
-/
theorem compilePanToLoop_ite_equal_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α)
    (conditionLeft conditionRight thenValue elseValue : α)
    (one_ne_zero : (1 : α) ≠ 0) :
    (evalLoopProg 60 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.ite (.cmp .equal (.const conditionLeft) (.const conditionRight))
            (.return (.const thenValue)) (.return (.const elseValue)))))).map
        loopResultValues =
      evalPanProg (fun _ => none)
        (.ite (.cmp .equal (.const conditionLeft) (.const conditionRight))
          (.return (.const thenValue)) (.return (.const elseValue))) := by
  simp [compileProg, compileExp, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    evalLoopCondition, loopReadLocals, updateLoopLocal, evalPanProg,
    evalPanExp, evalPanCondition]
  by_cases h : conditionLeft == conditionRight <;>
    simp [h, one_ne_zero, updateLoopLocal]
  all_goals rfl

/-!
This environment-sensitive bridge follows CakeML's slot allocation: a source
local assignment is lowered to its declared Crepe slot, and the subsequent
source-local return reads the same slot through the Loop evaluator.
-/
theorem compilePanToLoop_local_assign_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (name : VarName) (slot : Nat)
    (value : α)
    (lookup : lookupInfo name compileContext.vars = some (.one, [slot])) :
    (evalLoopProg 30 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))))).map loopResultValues =
      (evalPanStateProg (fun _ => none)
        (.seq (.assign .local name (.const value))
          (.return (.var .local name)))).map Prod.snd := by
  simp [compileProg, compileExp, crepNestedSeq, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, updatePanLocal, loopResultValues,
    evalPanStateProg, evalPanExp, lookup, distinctLists]

/-!
Returning an existing source local requires an explicit state relation: the
source name is resolved to its declared Crepe slot, and the Loop state must
contain the same value at that slot.
-/
theorem compilePanToLoop_local_return_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (locals : VarName → Option α)
    (name : VarName) (slot : Nat)
    (lookup : lookupInfo name compileContext.vars = some (.one, [slot]))
    (environment_agrees : state.locals slot = locals name) :
    (evalLoopProg 16 state
      (loopCompileProg loopContext live
        (compileProg compileContext (.return (.var .local name))))).map
        loopResultValues =
      (evalPanStateProg locals
        (.return (.var .local name) : Prog α)).map Prod.snd := by
  simp [compileProg, compileExp, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    loopReadLocals, evalPanStateProg,
    evalPanExp, lookup, environment_agrees]
  cases h : locals name <;>
    simp [updateLoopLocal] <;> rfl

/-!
A closed scalar declaration extends the source environment and the compiled
Loop environment at the same allocated slot.  The body can then read that
slot through the usual local-return path.
-/
theorem compilePanToLoop_dec_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (locals : VarName → Option α)
    (name : VarName) (value : α)
    (maxVar_agrees : loopContext.maxVar = compileContext.maxVar) :
    (evalLoopProg 16 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.dec name .one (.const value) (.return (.var .local name)))))).map
        loopResultValues =
      (evalPanStateProg locals
        (.dec name .one (.const value) (.return (.var .local name)))).map
        Prod.snd := by
  have hcompiled :
      loopCompileProg loopContext live
        (.dec (compileContext.maxVar + 1) (.const value)
          (.return [.var (compileContext.maxVar + 1)])) =
        .seq .skip
          (.seq (.assign (compileContext.maxVar + 1) (.const value))
            (.seq
              (.seq (.assign (loopContext.maxVar + 1 + 1)
                (.var (compileContext.maxVar + 1))) .skip)
              (.return [loopContext.maxVar + 1 + 1]))) := by
    simp [loopCompileProg, loopCompileExp, loopCompileExps,
      loopCompileExp.loopCompileExps, loopNestedSeq, loopTempNames,
      loopAssignTemps, maxVar_agrees]
  simp [compileProg, compileExp, allocatedNames, nestedDecs, hcompiled,
    evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, updatePanLocal, loopResultValues,
    evalPanStateProg, evalPanExp, lookupInfo, maxVar_agrees]

/-!
The declaration bridge also preserves a computed value: the arithmetic
expression is evaluated once into the declaration slot, then the body reads
that slot through the compiled local variable.
-/
theorem compilePanToLoop_dec_return_add_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (locals : VarName → Option α)
    (name : VarName) (left right : α)
    (maxVar_agrees : loopContext.maxVar = compileContext.maxVar) :
    (evalLoopProg 20 state
      (loopCompileProg loopContext live
        (compileProg compileContext
          (.dec name .one (.op .add [.const left, .const right])
            (.return (.var .local name)))))).map loopResultValues =
      (evalPanStateProg locals
        (.dec name .one (.op .add [.const left, .const right])
          (.return (.var .local name)))).map Prod.snd := by
  have hcompiled :
      loopCompileProg loopContext live
        (.dec (compileContext.maxVar + 1)
          (.op .add [.const left, .const right])
          (.return [.var (compileContext.maxVar + 1)])) =
        .seq .skip
          (.seq
            (.assign (compileContext.maxVar + 1)
              (.op .add [.const left, .const right]))
            (.seq
              (.seq (.assign (loopContext.maxVar + 1 + 1)
                (.var (compileContext.maxVar + 1))) .skip)
              (.return [loopContext.maxVar + 1 + 1]))) := by
    simp [loopCompileProg, loopCompileExp, loopCompileExps,
      loopCompileExp.loopCompileExps, loopNestedSeq, loopTempNames,
      loopAssignTemps, maxVar_agrees]
  simp [compileProg, compileExp, compileExp.compileExpList, cexpHeads,
    allocatedNames, nestedDecs, hcompiled,
    evalLoopProg, evalLoopExp, evalLoopBinOp,
    loopReadLocals, updateLoopLocal, updatePanLocal, loopResultValues,
    evalPanStateProg, evalPanExp, evalPanBinOp, lookupInfo, maxVar_agrees]

/-!
The first compositional bridge between the Loop and Word semantic states.
Only the destination register is observed here; the full state relation will
add globals, memory, live-register preservation, and control results as the
remaining Word operations are ported.
-/
def loopRegisterState [NeZero width] (state : RiscV.State width) :
    LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat name).map (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMapped [NeZero width] (context : WordContext)
    (state : RiscV.State width) : LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat (wordFindVar context name)).map
        (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMappedWithMemory [NeZero width] (context : WordContext)
    (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width)) :
    LoopState (RiscV.Word width) :=
  { loopRegisterStateMapped context state with memory := memory }

/-!
This is the first context-parametric Loop-to-Word state observation. The
source local and its mapped register need not have the same numeric name; the
only required premise is that the mapped destination is a valid RISC-V
register. It is the base case needed before extending the relation to
expression evaluation and sequencing.
-/
theorem loopToWord_const_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination : Nat) (value : RiscV.Word width) (register : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hregister :
      RiscV.registerOfNat (wordFindVar context destination) = some register)
    (hregister_nonzero : register ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.const value)))).map
        (fun state => RiscV.readRegister state register) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterStateMapped,
    loopToWordProg, wordCompileExp, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, hregister, hregister_nonzero, hzero]

theorem loopToWord_add_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination left right : Nat) (destinationRegister leftRegister rightRegister : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hleft :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.op .add [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op .add [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp,
    loopRegisterStateMapped, loopToWordProg, wordCompileExp,
    wordCompileExp.wordCompileExpList,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
    RiscV.nextPc, updateLoopLocal, hdestination, hleft, hright,
    hdestination_nonzero]

theorem loopToWord_binop_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (operator : BinOp) (destination left right : Nat)
    (destinationRegister leftRegister rightRegister : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) = some destinationRegister)
    (hleft :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.op operator [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have hand (x y : RiscV.Word width) : AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  have hor (x y : RiscV.Word width) : OrOp.or x y = x ||| y := by
    change x.or y = x ||| y
    exact BitVec.or_eq x y
  cases operator <;>
    simp [evalLoopProg, evalLoopExp, evalLoopBinOp,
      loopRegisterStateMapped, loopToWordProg, wordCompileExp,
      wordCompileExp.wordCompileExpList,
      RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      RiscV.nextPc, updateLoopLocal, hdestination, hleft, hright,
      hdestination_nonzero, hand, hor]

theorem loopToWord_locValue_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination source : Nat) (destinationRegister sourceRegister : Fin 32)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) = some destinationRegister)
    (hsource :
      RiscV.registerOfNat (wordFindVar context source) = some sourceRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.locValue destination source)).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.locValue destination source))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  simp [evalLoopProg, loopRegisterStateMapped, loopToWordProg,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, hdestination, hsource, hdestination_nonzero]

theorem loopToWord_load32_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory : memory addressValue = some value)
    (hmachine : RiscV.readWord32 state addressValue = value)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.load32 address destination)).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.load32 address destination))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, 
    RiscV.evalWordProg, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc,
    haddress, hdestination, 
    hdestination_nonzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmemory, hmachine]
  simp [updateLoopLocal]

theorem loopToWord_loadByte_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue _value : RiscV.Word width) (byteValue : BitVec 8)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory :
      memory addressValue =
        some (BitVec.ofNat width byteValue.toNat))
    (hmachine :
      RiscV.readByte state addressValue = byteValue)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .load8 destination (.var address))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load8 destination (.var address)))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  rw [evalLoopProg_shMem_load
    (loopRegisterStateMappedWithMemory context state memory) .load8
    destination (.var address) addressValue
    (BitVec.ofNat width byteValue.toNat) (by simp) haddress_eval hmemory]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, 
    hdestination_nonzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmachine]

theorem loopToWord_storeByte_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .store8 value (.var address))).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store8 value (.var address)))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state addressValue).toNat) := by
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  have hvalue_eval :
      (loopRegisterStateMappedWithMemory context state memory).locals value =
        some valueValue := by
    simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
      hvalue, hvalue_value]
  rw [evalLoopProg_shMem_store
    (loopRegisterStateMappedWithMemory context state memory) .store8
    value (.var address) addressValue valueValue
    (by simp) haddress_eval hvalue_eval]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeByte, RiscV.readByte, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem loopToWord_load16_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory : memory addressValue = some value)
    (hmachine : RiscV.readWord16 state addressValue = value)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .load16 destination (.var address))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load16 destination (.var address)))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  rw [evalLoopProg_shMem_load
    (loopRegisterStateMappedWithMemory context state memory) .load16
    destination (.var address) addressValue value (by simp) haddress_eval hmemory]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, 
    hdestination_nonzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmachine]

theorem loopToWord_store16_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .store16 value (.var address))).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store16 value (.var address)))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state (RiscV.byteAddress addressValue 0)).toNat) := by
  simp [evalLoopProg, evalLoopExp, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, 
    RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeWord16,
    RiscV.writeByte, RiscV.readByte, RiscV.byteAddress, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, NeZero.ne width]

theorem loopToWord_store32_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue)
    (width_ge_8 : 8 ≤ width) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.store32 address value)).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.store32 address value))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state (RiscV.byteAddress addressValue 0)).toNat) := by
  have hwidth0 : width ≠ 0 := NeZero.ne width
  have h2 : (BitVec.ofNat width 2) ≠ 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hpow : 2 ^ 2 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow' : 4 ≤ 2 ^ width := by
      simpa using hpow
    have hlt : (2 : Nat) < 2 ^ width :=
      Nat.lt_of_lt_of_le (by decide : (2 : Nat) < 4) hpow'
    have h'' : (2 : Nat) = 0 := by
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt] at h'
    omega
  have h3 : (BitVec.ofNat width 3) ≠ 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hpow : 2 ^ 2 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow' : 4 ≤ 2 ^ width := by
      simpa using hpow
    have hlt : (3 : Nat) < 2 ^ width :=
      Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 4) hpow'
    have h'' : (3 : Nat) = 0 := by
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt] at h'
    omega
  simp [evalLoopProg, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, RiscV.evalWordProg,
    RiscV.execute, RiscV.writeWord32, RiscV.writeByte,
    RiscV.readByte, RiscV.byteAddress, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  split <;> rename_i h
  · exact (h3 h).elim
  · split <;> rename_i h'
    · exact (h2 h').elim
    · have hvalue_byte : BitVec.toNat valueValue % 256 < 2 ^ 8 := by
        have hmod := Nat.mod_lt (BitVec.toNat valueValue) (by decide : 0 < 256)
        simpa using hmod
      rw [BitVec.setWidth_ofNat_of_le_of_lt (by omega : 8 ≤ width) hvalue_byte]

theorem loopToWord_const_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state)
    (value : RiscV.Word width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.const value)))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterState, loopToWordProg, 
    wordCompileExp, wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal, hzero]

theorem loopToWord_add_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.op .add [.var 2, .var 3]))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.op .add [.var 2, .var 3])))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp, loopRegisterState,
    loopToWordProg, wordCompileExp, wordCompileExp.wordCompileExpList,
    wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal]

theorem loopToWord_longMul_register_agreement [NeZero width]
    (state : RiscV.State width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.arith (.longMul 1 1 2 3))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.arith (.longMul 1 1 2 3)))).map
        (fun state => RiscV.readRegister state 1) := by
  simp [evalLoopProg, loopRegisterState, loopToWordProg, wordArith,
    wordFindVar, lookupNatInfo, RiscV.evalWordProg,
    RiscV.wordArithToInstructions, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal]

/-!
The local relation used by the HOL loop_to_word proof is represented here as
a direct register witness.  This theorem lifts the constructor-specific
mapped binop observations above to an arbitrary Loop local environment:
every source local has a mapped RISC-V register carrying the same word, and
the destination mapping is required to be writable.
-/
def loopLocalsMappedToRiscV [NeZero width] (context : WordContext)
    (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width) : Prop :=
  ∀ name value, locals name = some value →
    ∃ register,
      RiscV.registerOfNat (wordFindVar context name) = some register ∧
        RiscV.readRegister state register = value

theorem loopToWord_longMul_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination sourceLeft sourceRight : Nat)
    (destinationRegister : Fin 32) (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals sourceLeft = some leftValue)
    (hright : loopState.locals sourceRight = some rightValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.arith (.longMul destination destination sourceLeft sourceRight))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination (leftValue * rightValue))
        resultState := by
  intro resultState hresult
  rcases hlocals sourceLeft leftValue hleft with
    ⟨leftRegister, hleft_register, hleft_value⟩
  rcases hlocals sourceRight rightValue hright with
    ⟨rightRegister, hright_register, hright_value⟩
  have hleft_value' : state.registers leftRegister = leftValue := by
    exact hleft_value
  have hright_value' : state.registers rightRegister = rightValue := by
    exact hright_value
  have hleft_lt : wordFindVar context sourceLeft < 32 :=
    RiscV.registerOfNat_some_lt hleft_register
  have hright_lt : wordFindVar context sourceRight < 32 :=
    RiscV.registerOfNat_some_lt hright_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hleft_fin :
      (⟨wordFindVar context sourceLeft, hleft_lt⟩ : Fin 32) = leftRegister := by
    have h := hleft_register
    simp [RiscV.registerOfNat, hleft_lt] at h
    exact h
  have hright_fin :
      (⟨wordFindVar context sourceRight, hright_lt⟩ : Fin 32) = rightRegister := by
    have h := hright_register
    simp [RiscV.registerOfNat, hright_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  by_cases halias :
      wordFindVar context destination = wordFindVar context sourceLeft ∨
        wordFindVar context destination = wordFindVar context sourceRight
  · simp [loopToWordProg, wordArith, RiscV.evalWordProg,
      RiscV.wordArithToInstructions, halias] at hresult
  · simp [loopToWordProg, wordArith, RiscV.evalWordProg,
      RiscV.wordArithToInstructions, RiscV.executeInstructions,
      RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      RiscV.registerOfNat, hleft_lt, hright_lt, hdestination_lt,
      hleft_fin, hright_fin, hdestination_fin, hleft_value', hright_value',
      halias, hdestination_nonzero] at hresult
    have hleft_not_destination : leftRegister ≠ destinationRegister := by
      intro heq
      have hvars := RiscV.registerOfNat_injective hleft_register
        hdestination heq
      exact halias (Or.inl hvars.symm)
    have hright_not_destination : rightRegister ≠ destinationRegister := by
      intro heq
      have hvars := RiscV.registerOfNat_injective hright_register
        hdestination heq
      exact halias (Or.inr hvars.symm)
    cases hresult
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : leftValue * rightValue = current := by
        simpa [updateLoopLocal] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.readRegister, 
        
        hleft_not_destination,
        hright_not_destination]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.readRegister, 
        hregister_nonalias]
      exact hregister_value

theorem pipelineWordContext_register_nonalias
    (slots : List Nat) (name destination : Nat)
    (hname : name ∈ slots) (hdestination : destination ∈ slots)
    (hneq : name ≠ destination)
    (nameRegister destinationRegister : Fin 32)
    (hname_register :
      RiscV.registerOfNat
        (wordFindVar (pipelineWordContext slots) name) = some nameRegister)
    (hdestination_register :
      RiscV.registerOfNat
        (wordFindVar (pipelineWordContext slots) destination) =
        some destinationRegister) :
    nameRegister ≠ destinationRegister := by
  intro heq
  have hnames := RiscV.registerOfNat_injective hname_register
    hdestination_register heq
  rw [wordFindVar_pipelineWordContext_of_mem slots name hname,
    wordFindVar_pipelineWordContext_of_mem slots destination hdestination] at hnames
  exact hneq (Nat.add_right_cancel hnames)

theorem loopToWordExp_var_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (name : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hvalue : ∃ value, loopState.locals name = some value) :
    evalLoopExp loopState (.var name) =
      (wordCompileExp context (.var name)).bind
        (RiscV.evalWordExp state) := by
  obtain ⟨value, hvalue⟩ := hvalue
  rcases hlocals name value hvalue with
    ⟨register, hregister, hregister_value⟩
  simp [evalLoopExp, wordCompileExp, RiscV.evalWordExp,
    hvalue, hregister, hregister_value]

theorem loopLocalsMappedToRiscV_update [NeZero width]
    (context : WordContext) (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width) (destination : Nat)
    (destinationRegister : Fin 32) (value : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context locals state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    loopLocalsMappedToRiscV context (updateLoopLocal locals destination value)
      (RiscV.writeRegister state destinationRegister value) := by
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.writeRegister, RiscV.readRegister, hdestination_nonzero]
  · have hcurrent' : locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp only [RiscV.readRegister, RiscV.writeRegister,
      if_neg hdestination_nonzero]
    simp only [if_neg hregister_nonalias]
    change RiscV.readRegister state register = current
    exact hregister_value

theorem loopToWord_tick_preserves_mapped_locals [NeZero width]
    (context : WordContext) (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width)
    (hlocals : loopLocalsMappedToRiscV context locals state) :
    ∀ resultState,
      RiscV.evalWordProg state (.tick : WordProg (RiscV.Word width)) =
        some resultState →
      loopLocalsMappedToRiscV context locals resultState := by
  intro resultState hresult
  simp [RiscV.evalWordProg] at hresult
  subst resultState
  intro name value hvalue
  rcases hlocals name value hvalue with
    ⟨register, hregister, hregister_value⟩
  refine ⟨register, hregister, ?_⟩
  by_cases hzero : register = 0
  · subst register
    exact hregister_value
  · simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister]
    exact hregister_value

theorem loopToWord_skip_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ finalLoop finalWord,
      evalLoopProg 1 loopState (.skip) = some (.normal finalLoop) →
      RiscV.evalWordProg state
        (loopToWordProg context (.skip)) = some finalWord →
      loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  intro finalLoop finalWord hloop hword
  simp [evalLoopProg] at hloop
  simp [loopToWordProg, RiscV.evalWordProg] at hword
  subst finalLoop
  subst finalWord
  exact hlocals

def loopResultMappedToRiscV [NeZero width] (context : WordContext) :
    LoopResult (RiscV.Word width) → RiscV.WordLoopResult width → Prop
  | .normal loopState, .normal state =>
      loopLocalsMappedToRiscV context loopState.locals state
  | .broke loopState loopLabel, .broke state wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals state
  | .continued loopState loopLabel, .continued state wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals state
  | _, _ => False

/-!
Control results for the handler-aware evaluator.  Break and continue are
handled by the separate Word-loop result relation above; ordinary function
sequencing only needs normal completion, return, and raise propagation.
-/
def loopControlResultMappedToRiscV [NeZero width] (context : WordContext) :
    LoopResult (RiscV.Word width) → RiscV.WordControlResult width → Prop
  | .normal loopState, .normal wordState =>
      loopLocalsMappedToRiscV context loopState.locals wordState
  | .returned loopState loopValues, .returned wordState wordValues =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordValues = loopValues
  | .raised loopState loopException, .raised wordState wordException =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordException = loopException
  | _, _ => False

theorem loopToWord_seq_control_simulation [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (fuel : Nat) (first second : LoopProg (RiscV.Word width))
    (loopResult : LoopResult (RiscV.Word width))
    (wordResult : RiscV.WordControlResult width)
    (hfirst : ∀ (_middleLoop : LoopState (RiscV.Word width))
      (_middleWord : RiscV.State width) firstResult firstWordResult,
      evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first =
        some firstResult →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        wordState (loopToWordProg context first) = some firstWordResult →
      loopControlResultMappedToRiscV context firstResult firstWordResult)
    (hsecond : ∀ middleLoop middleWord secondResult secondWordResult,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
        some secondResult →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        middleWord (loopToWordProg context second) = some secondWordResult →
      loopControlResultMappedToRiscV context secondResult secondWordResult)
    (hloop :
      evalLoopProgWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        (.seq first second) = some loopResult)
    (hword :
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState (loopToWordProg context (.seq first second)) = some wordResult) :
    loopControlResultMappedToRiscV context loopResult wordResult := by
  cases hfirstLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
                some loopResult := by
            simpa [evalLoopProgWithCallsAndFfi, hfirstLoop] using hloop
          cases hfirstWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
                hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondWord :
                      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                        middleWord (loopToWordProg context second) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordFunctionWithHandlersAndFfi, hfirstWord] using hword
                  have hfirstResult := hfirst middleLoop middleWord
                    (.normal middleLoop) (.normal middleWord) hfirstLoop hfirstWord
                  exact hsecond middleLoop middleWord loopResult wordResult
                    hfirstResult hsecondLoop hsecondWord
              | returned middleWord values =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.normal middleLoop) (.returned middleWord values)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | raised middleWord exception =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.normal middleLoop) (.raised middleWord exception)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
      | returned middleLoop values =>
          cases hfirstWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
                hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.returned middleLoop values) (.normal middleWord)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | returned middleWord wordValues =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.returned middleLoop values) (.returned middleWord wordValues)
                    hfirstLoop hfirstWord
                  have hloop' :
                      some (.returned middleLoop values) = some loopResult := by
                    simpa [evalLoopProgWithCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.returned middleWord wordValues) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordFunctionWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  cases hloopResult
                  cases hwordResult
                  exact hfirstResult
              | raised middleWord exception =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.returned middleLoop values) (.raised middleWord exception)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
      | raised middleLoop exception =>
          cases hfirstWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
                hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.raised middleLoop exception) (.normal middleWord)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | returned middleWord values =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.raised middleLoop exception) (.returned middleWord values)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | raised middleWord wordException =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.raised middleLoop exception) (.raised middleWord wordException)
                    hfirstLoop hfirstWord
                  have hloop' :
                      some (.raised middleLoop exception) = some loopResult := by
                    simpa [evalLoopProgWithCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.raised middleWord wordException) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordFunctionWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  cases hloopResult
                  cases hwordResult
                  exact hfirstResult
      | broke middleLoop label =>
          cases hfirstWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
                hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.broke middleLoop label) (.normal middleWord)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | returned middleWord values =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.broke middleLoop label) (.returned middleWord values)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | raised middleWord exception =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.broke middleLoop label) (.raised middleWord exception)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
      | continued middleLoop label =>
          cases hfirstWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
                hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.continued middleLoop label) (.normal middleWord)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | returned middleWord values =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.continued middleLoop label) (.returned middleWord values)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult
              | raised middleWord exception =>
                  have hfirstResult := hfirst middleLoop middleWord
                    (.continued middleLoop label) (.raised middleWord exception)
                    hfirstLoop hfirstWord
                  simp [loopControlResultMappedToRiscV] at hfirstResult

/-!
Return values are read from mapped Word registers.  The source result stores
the values obtained from its local names, so a mapped-local relation is enough
to show that the two return lists are identical.
-/
theorem loopToWord_return_simulation [NeZero width]
    (context : WordContext)
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (values : List Nat) (fuel : Nat)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (loopResultValues wordResultValues : List (RiscV.Word width))
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopProg (fuel + 1) loopState (.return values) =
        some (.returned finalLoop loopResultValues))
    (hword :
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState (loopToWordProg context (.return values)) =
        some (.returned finalWord wordResultValues)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord ∧
      wordResultValues = loopResultValues := by
  have hread_values : ∀ (names : List Nat) (readValues : List (RiscV.Word width)),
      loopReadLocals loopState.locals names = some readValues →
      (wordMapVars context names).mapM (fun name => do
        let register ← RiscV.registerOfNat name
        pure (RiscV.readRegister wordState register)) = some readValues := by
    intro names
    induction names with
    | nil =>
        intro readValues hread
        have hread' : readValues = [] := by
          simpa [loopReadLocals] using hread
        subst readValues
        simp [wordMapVars]
    | cons name names ih =>
        intro readValues hread
        cases hlocal : loopState.locals name with
        | none =>
            simp [loopReadLocals, hlocal] at hread
        | some value =>
            cases hrest : loopReadLocals loopState.locals names with
            | none =>
                simp [loopReadLocals, hlocal, hrest] at hread
            | some rest =>
                have hread' : readValues = value :: rest := by
                  simpa [loopReadLocals, hlocal, hrest] using hread.symm
                subst readValues
                rcases hlocals name value hlocal with
                  ⟨register, hregister, hvalue⟩
                have htail := ih rest hrest
                have htail' :
                    (wordMapVars context names).mapM (fun name =>
                      (RiscV.registerOfNat name).bind (fun register =>
                        some (RiscV.readRegister wordState register))) = some rest := by
                  simpa using htail
                simp [wordMapVars, hregister, hvalue]
                rw [htail']
                simp
  cases hread : loopReadLocals loopState.locals values with
  | none =>
      simp [evalLoopProg, hread] at hloop
  | some readValues =>
      have hloop' :
          some (LoopResult.returned loopState readValues) =
            some (LoopResult.returned finalLoop loopResultValues) := by
        simpa [evalLoopProg, hread] using hloop
      injection hloop' with hreturned
      injection hreturned with hfinalLoop hresultValues
      subst finalLoop
      subst loopResultValues
      cases hwordValues :
          (wordMapVars context values).mapM (fun name => do
            let register ← RiscV.registerOfNat name
            pure (RiscV.readRegister wordState register)) with
      | none =>
          have hwordValues' :
              (wordMapVars context values).mapM (fun name =>
                (RiscV.registerOfNat name).bind (fun register =>
                  some (RiscV.readRegister wordState register))) = none := by
            simpa using hwordValues
          simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
            hwordValues'] at hword
      | some mappedValues =>
          have hwordValues' :
              (wordMapVars context values).mapM (fun name =>
                (RiscV.registerOfNat name).bind (fun register =>
                  some (RiscV.readRegister wordState register))) = some mappedValues := by
            simpa using hwordValues
          have hword' :
              some (RiscV.WordControlResult.returned wordState mappedValues) =
                some (RiscV.WordControlResult.returned finalWord wordResultValues) := by
            simpa [loopToWordProg,
              RiscV.evalWordFunctionWithHandlersAndFfi, hwordValues'] using hword
          injection hword' with hreturnedWord
          injection hreturnedWord with hfinalWord hwordResultValues
          subst finalWord
          subst wordResultValues
          have hmapped := hread_values values readValues hread
          rw [hwordValues] at hmapped
          injection hmapped with hmappedValues
          subst mappedValues
          exact ⟨hlocals, rfl⟩

theorem loopToWord_raise_simulation [NeZero width]
    (context : WordContext)
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (exception : Nat) (fuel : Nat)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (loopException wordException : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopProg (fuel + 1) loopState (.raise exception) =
        some (LoopResult.raised finalLoop loopException))
    (hword :
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState (loopToWordProg context (.raise exception)) =
        some (RiscV.WordControlResult.raised finalWord wordException)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord ∧
      loopException = wordException := by
  cases hlocal : loopState.locals exception with
  | none =>
      simp [evalLoopProg, hlocal] at hloop
  | some exceptionValue =>
      have hloop' :
          some (LoopResult.raised loopState exceptionValue) =
            some (LoopResult.raised finalLoop loopException) := by
        simpa [evalLoopProg, hlocal] using hloop
      injection hloop' with hraised
      injection hraised with hfinalLoop hloopException
      subst finalLoop
      rcases hlocals exception exceptionValue hlocal with
        ⟨exceptionRegister, hexceptionRegister, hexceptionValue⟩
      cases hwordRegister :
          RiscV.registerOfNat (wordFindVar context exception) with
      | none =>
          simp [loopToWordProg, RiscV.evalWordFunctionWithHandlersAndFfi,
            hwordRegister] at hword
      | some register =>
          have hword' :
              some (RiscV.WordControlResult.raised wordState
                (RiscV.readRegister wordState register)) =
                some (RiscV.WordControlResult.raised finalWord wordException) := by
            simpa [loopToWordProg,
              RiscV.evalWordFunctionWithHandlersAndFfi, hwordRegister] using hword
          injection hword' with hraisedWord
          injection hraisedWord with hfinalWord hwordException
          subst finalWord
          have hregister : register = exceptionRegister := by
            rw [hwordRegister] at hexceptionRegister
            injection hexceptionRegister
          subst register
          exact ⟨hlocals,
            hloopException.symm.trans (hexceptionValue.symm.trans hwordException)⟩

theorem loopRepeat_mapped_locals [NeZero width]
    (context : WordContext) (body : LoopProg (RiscV.Word width))
    (wordBody : WordProg (RiscV.Word width))
    (hbody : ∀ fuel loopState state loopResult wordResult,
      loopLocalsMappedToRiscV context loopState.locals state →
      evalLoopProg fuel loopState body = some loopResult →
      RiscV.evalWordLoopProg fuel state wordBody = some wordResult →
      loopResultMappedToRiscV context loopResult wordResult) :
    ∀ fuel loopState state loopResult wordResult,
      loopLocalsMappedToRiscV context loopState.locals state →
      evalLoopRepeat fuel loopState body = some loopResult →
      RiscV.evalWordLoopRepeat fuel state wordBody = some wordResult →
      loopResultMappedToRiscV context loopResult wordResult := by
  intro fuel
  induction fuel with
  | zero =>
      intro loopState state loopResult wordResult hlocals hloop hword
      simp [evalLoopRepeat] at hloop
  | succ fuel ih =>
      intro loopState state loopResult wordResult hlocals hloop hword
      cases hbodyLoop : evalLoopProg fuel loopState body with
      | none =>
          simp [evalLoopRepeat, hbodyLoop] at hloop
      | some loopBodyResult =>
          cases hbodyWord : RiscV.evalWordLoopProg fuel state wordBody with
          | none =>
              simp [RiscV.evalWordLoopRepeat, hbodyWord] at hword
          | some wordBodyResult =>
              have hbodyResult := hbody fuel loopState state
                loopBodyResult wordBodyResult hlocals hbodyLoop hbodyWord
              cases loopBodyResult with
              | normal middleLoop =>
                  cases wordBodyResult with
                  | normal middleWord =>
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult
                      apply ih middleLoop middleWord loopResult wordResult hlocals'
                      · simpa [evalLoopRepeat, hbodyLoop] using hloop
                      · simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                  | broke middleWord label | continued middleWord label =>
                      exact False.elim (by simp [loopResultMappedToRiscV] at hbodyResult)
              | broke middleLoop label =>
                  cases wordBodyResult with
                  | normal middleWord | continued middleWord wordLabel =>
                      exact False.elim (by simp [loopResultMappedToRiscV] at hbodyResult)
                  | broke middleWord wordLabel =>
                      have hlabel : label = wordLabel := by
                        exact hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordLabel : wordLabel = 0 := by
                          exact hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        have hloop' :
                            some (.normal middleLoop) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop] using hloop
                        have hword' :
                            some (.normal middleWord) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                        cases hloop'
                        cases hword'
                        exact hlocals'
                      · have hwordLabel : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.broke middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.broke middleWord wordLabel) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord, hwordLabel] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩
              | continued middleLoop label =>
                  cases wordBodyResult with
                  | normal middleWord | broke middleWord wordLabel =>
                      exact False.elim (by simp [loopResultMappedToRiscV] at hbodyResult)
                  | continued middleWord wordLabel =>
                      have hlabel : label = wordLabel := by
                        exact hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordLabel : wordLabel = 0 := by
                          exact hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        apply ih middleLoop middleWord loopResult wordResult hlocals'
                        · simpa [evalLoopRepeat, hbodyLoop] using hloop
                        · simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                      · have hwordLabel : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.continued middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.continued middleWord wordLabel) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord, hwordLabel] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩
              | returned middleLoop values | raised middleLoop exception =>
                  exact False.elim (by simp [loopResultMappedToRiscV] at hbodyResult)

theorem loopToWord_loop_simulation [NeZero width]
    (context : WordContext)
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (liveIn liveOut : List Nat)
    (body : LoopProg (RiscV.Word width))
    (fuel : Nat)
    (loopResult : LoopResult (RiscV.Word width))
    (wordResult : RiscV.WordLoopResult width)
    (hbody : ∀ fuel loopState state loopResult wordResult,
      loopLocalsMappedToRiscV context loopState.locals state →
      evalLoopProg fuel loopState body = some loopResult →
      RiscV.evalWordLoopProg fuel state (loopToWordProg context body) =
        some wordResult →
      loopResultMappedToRiscV context loopResult wordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopProg (fuel + 1) loopState
        (.loop liveIn body liveOut) = some loopResult)
    (hword :
      RiscV.evalWordLoopProg (fuel + 3) wordState
        (loopToWordProg context (.loop liveIn body liveOut)) =
          some wordResult) :
    loopResultMappedToRiscV context loopResult wordResult := by
  have hloop' : evalLoopRepeat fuel loopState body = some loopResult := by
    simpa [evalLoopProg] using hloop
  cases htick : RiscV.evalWordProg wordState (.tick) with
  | none =>
      simp [loopToWordProg, RiscV.evalWordLoopProg, htick] at hword
  | some tickedWordState =>
      have hlocals' :
          loopLocalsMappedToRiscV context loopState.locals tickedWordState :=
        loopToWord_tick_preserves_mapped_locals context loopState.locals
          wordState hlocals tickedWordState htick
      cases hbodyWord :
          RiscV.evalWordLoopRepeat fuel tickedWordState
            (loopToWordProg context body) with
      | none =>
          simp [loopToWordProg, RiscV.evalWordLoopProg, htick,
            hbodyWord] at hword
      | some bodyWordResult =>
          have hrepeat := loopRepeat_mapped_locals context body
            (loopToWordProg context body) hbody fuel loopState tickedWordState
            loopResult bodyWordResult hlocals' hloop' hbodyWord
          cases bodyWordResult with
          | broke middleWord label =>
              have hword' :
                  some (.broke middleWord label) = some wordResult := by
                simpa [loopToWordProg, RiscV.evalWordLoopProg, htick,
                  hbodyWord] using hword
              cases hword'
              exact hrepeat
          | continued middleWord label =>
              have hword' :
                  some (.continued middleWord label) = some wordResult := by
                simpa [loopToWordProg, RiscV.evalWordLoopProg, htick,
                  hbodyWord] using hword
              cases hword'
              exact hrepeat
          | normal middleWord =>
              cases hfinalTick : RiscV.evalWordProg middleWord (.tick) with
              | none =>
                  simp [loopToWordProg, RiscV.evalWordLoopProg, htick,
                    hbodyWord, hfinalTick] at hword
              | some finalWord =>
                  have hword' :
                      some (.normal finalWord) = some wordResult := by
                    simpa [loopToWordProg, RiscV.evalWordLoopProg, htick,
                      hbodyWord, hfinalTick] using hword
                  cases hword'
                  cases loopResult with
                  | normal finalLoop =>
                      exact loopToWord_tick_preserves_mapped_locals context
                        finalLoop.locals middleWord hrepeat finalWord hfinalTick
                  | returned finalLoop values
                  | broke finalLoop label
                  | continued finalLoop label
                  | raised finalLoop exception =>
                      simp [loopResultMappedToRiscV] at hrepeat

theorem bindWordRegisters_single_parameter [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register) :
    RiscV.bindWordRegisters state [wordFindVar context name] [value] =
      some (RiscV.writeRegister (RiscV.clearWordRegisters state) register value) := by
  simp [RiscV.bindWordRegisters, hregister]

theorem loopLocalsMappedToRiscV_single_parameter [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register)
    (hregister_nonzero : register ≠ 0) :
    loopLocalsMappedToRiscV context
      (updateLoopLocal (fun _ => none) name value)
      (RiscV.writeRegister (RiscV.clearWordRegisters state) register value) := by
  intro current currentValue hcurrent
  by_cases hname : current = name
  · subst current
    have hvalue : value = currentValue := by
      simpa [updateLoopLocal] using hcurrent
    subst currentValue
    exact ⟨register, hregister, by
      simp [RiscV.writeRegister, RiscV.readRegister, hregister_nonzero]⟩
  · have : (none : Option (RiscV.Word width)) = some currentValue := by
      simp [updateLoopLocal, hname] at hcurrent
    simp at this

theorem loopBindParameters_single_parameter_agreement [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register)
    (hregister_nonzero : register ≠ 0) :
    ∃ locals wordState,
      loopBindParameters [name] [value] (fun _ => none) = some locals ∧
        RiscV.bindWordRegisters state
          [wordFindVar context name] [value] = some wordState ∧
        loopLocalsMappedToRiscV context locals wordState := by
  refine ⟨updateLoopLocal (fun _ => none) name value,
    RiscV.writeRegister (RiscV.clearWordRegisters state) register value,
    ?_, ?_, ?_⟩
  · simp [loopBindParameters]
  · exact bindWordRegisters_single_parameter context state name value register
      hregister
  · exact loopLocalsMappedToRiscV_single_parameter context state name value register
      hregister hregister_nonzero

/-!
Handler-free one-parameter calls.  The body proof is supplied by the caller,
which keeps this dispatcher theorem independent of the particular instruction
fragment used for the callee.  The theorem still discharges the important
boundary work: function lookup, argument reading, fresh callee-frame binding,
and propagation of the returned result back to the caller.
-/
theorem loopToWord_call_tail_simulation_single_parameter [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (target parameter argument : Nat) (argumentValue : RiscV.Word width)
    (loopBody : LoopProg (RiscV.Word width)) (fuel : Nat)
    (parameterRegister : Fin 32)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (loopResultValues wordResultValues : List (RiscV.Word width))
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hbody : ∀ calleeLoop calleeWord bodyLoop bodyWord loopValues wordValues,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel calleeLoop loopBody =
        some (.returned bodyLoop loopValues) →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        calleeWord (loopToWordProg context loopBody) =
        some (.returned bodyWord wordValues) →
      wordValues = loopValues)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        none (some target) [argument] none =
        some (.returned finalLoop loopResultValues))
    (hword :
      RiscV.evalWordCallWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState none (some target) [wordFindVar context argument] none =
        some (.returned finalWord wordResultValues)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord ∧
      wordResultValues = loopResultValues := by
  rcases hlocals argument argumentValue hargument with
    ⟨_, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, hcallee⟩
  cases hbodyLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
        hcalleeBind, hbodyLoop] at hloop
  | some bodyLoopResult =>
      cases bodyLoopResult with
      | normal bodyLoopState =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
            hcalleeBind, hbodyLoop] at hloop
      | broke bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
            hcalleeBind, hbodyLoop] at hloop
      | continued bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
            hcalleeBind, hbodyLoop] at hloop
      | raised bodyLoopState exception =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
            hcalleeBind, hbodyLoop] at hloop
      | returned bodyLoopState bodyValues =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                    harguments, hwordBind, hbodyWord] at hword
              | raised bodyWordState exception =>
                  simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                    harguments, hwordBind, hbodyWord] at hword
              | returned bodyWordState bodyValues' =>
                  have hvalues := hbody { loopState with locals := calleeLocals }
                    calleeWord bodyLoopState
                    bodyWordState bodyValues bodyValues' hcallee hbodyLoop hbodyWord
                  have hloop' :
                      some (LoopResult.returned loopState bodyValues) =
                        some (LoopResult.returned finalLoop loopResultValues) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hargument, hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  have hword' :
                      some (RiscV.WordControlResult.returned
                        { wordState with
                          memory := bodyWordState.memory
                          privilege := bodyWordState.privilege
                          mode := bodyWordState.mode }
                        bodyValues') =
                        some (RiscV.WordControlResult.returned finalWord
                          wordResultValues) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord] using hword
                  injection hloop' with hloopReturned
                  injection hloopReturned with hfinalLoop hloopValues
                  injection hword' with hwordReturned
                  injection hwordReturned with hfinalWord hwordValues
                  subst finalLoop
                  subst finalWord
                  subst loopResultValues
                  subst wordResultValues
                  refine ⟨?_, hvalues⟩
                  intro name value hvalue
                  rcases hlocals name value hvalue with
                    ⟨register, hregister, hregisterValue⟩
                  refine ⟨register, hregister, ?_⟩
                  simpa [RiscV.readRegister] using hregisterValue

def loopCallBodyResultCompatible [NeZero width] :
    LoopResult (RiscV.Word width) → RiscV.WordControlResult width → Prop
  | .normal _, .normal _ => True
  | .raised _ sourceException, .raised _ targetException =>
      sourceException = targetException
  | _, _ => False

def loopCallBodyNormalOrReturnCompatible [NeZero width] :
    LoopResult (RiscV.Word width) → RiscV.WordControlResult width → Prop
  | .normal _, .normal _ => True
  | .returned _ loopValues, .returned _ wordValues =>
      wordValues = loopValues
  | _, _ => False

/-!
Ordinary one-result calls assign the callee's singleton result back into the
caller's local/register environment.  The body compatibility hypothesis is
kept abstract so this boundary theorem can be reused by recursive body
simulation proofs.
-/
theorem loopToWord_call_return_simulation_single_parameter [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (target parameter argument destination : Nat)
    (argumentValue : RiscV.Word width) (fuel : Nat)
    (loopBody : LoopProg (RiscV.Word width)) (live : List Nat)
    (parameterRegister destinationRegister : Fin 32)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister)
    (hbody : ∀ calleeLoop calleeWord loopResult wordResult,
      RiscV.readRegister calleeWord 0 = 0 →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel calleeLoop loopBody =
        some loopResult →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        calleeWord (loopToWordProg context loopBody) = some wordResult →
      loopCallBodyNormalOrReturnCompatible loopResult wordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        (some ([destination], live)) (some target) [argument] none =
          some (.normal finalLoop))
    (hword :
      RiscV.evalWordCallWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState
          (some ([wordFindVar context destination],
            (wordMapVars context live, []), .skip, 0, 0))
          (some target) [wordFindVar context argument] none =
        some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  rcases hlocals argument argumentValue hargument with
    ⟨_, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, _⟩
  have hcalleeWordEq :
      RiscV.writeRegister (RiscV.clearWordRegisters wordState)
          parameterRegister argumentValue = calleeWord := by
    have hbind := bindWordRegisters_single_parameter context wordState parameter
      argumentValue parameterRegister hparameter
    rw [hbind] at hwordBind
    injection hwordBind
  have hcalleeZero : RiscV.readRegister calleeWord 0 = 0 := by
    rw [← hcalleeWordEq]
    by_cases hzero : parameterRegister = 0
    · exact False.elim (hparameter_nonzero hzero)
    · have hzero' : (0 : Fin 32) ≠ parameterRegister := by
        intro h
        exact hzero h.symm
      simp [RiscV.clearWordRegisters, RiscV.writeRegister, RiscV.readRegister,
        hzero, hzero']
  cases hbodyLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
        hbodyLoop] at hloop
  | some bodyLoopResult =>
      cases bodyLoopResult with
      | normal bodyLoopState =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState) (.normal bodyWordState)
                    hcalleeZero hbodyLoop hbodyWord
                  have hloop' :
                      some (LoopResult.normal loopState) =
                        some (LoopResult.normal finalLoop) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : RiscV.State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (RiscV.WordControlResult.normal returnedWordState) =
                        some (RiscV.WordControlResult.normal finalWord) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord] using hword
                  injection hloop' with hloopResult
                  injection hloopResult with hfinalLoop
                  injection hword' with hwordResult
                  injection hwordResult with hfinalWord
                  subst finalLoop
                  subst finalWord
                  intro name value hvalue
                  rcases hlocals name value hvalue with
                    ⟨register, hregister, hregisterValue⟩
                  exact ⟨register, hregister, hregisterValue⟩
              | returned bodyWordState values =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.returned bodyWordState values) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyNormalOrReturnCompatible] at hcompatible
              | raised bodyWordState value =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.raised bodyWordState value) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyNormalOrReturnCompatible] at hcompatible
      | broke bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | continued bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | raised bodyLoopState exception =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | returned bodyLoopState bodyValues =>
          cases bodyValues with
          | nil =>
              simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
                hcalleeBind, hbodyLoop, loopAssignValues] at hloop
          | cons bodyValue rest =>
              cases rest with
              | nil =>
                  cases hbodyWord :
                      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                        calleeWord (loopToWordProg context loopBody) with
                  | none =>
                      simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                        harguments, hwordBind, hbodyWord] at hword
                  | some bodyWordResult =>
                      cases bodyWordResult with
                      | normal bodyWordState =>
                          have hcompatible := hbody
                            { loopState with locals := calleeLocals } calleeWord
                            (.returned bodyLoopState [bodyValue])
                            (.normal bodyWordState) hcalleeZero hbodyLoop hbodyWord
                          simp [loopCallBodyNormalOrReturnCompatible] at hcompatible
                      | raised bodyWordState value =>
                          have hcompatible := hbody
                            { loopState with locals := calleeLocals } calleeWord
                            (.returned bodyLoopState [bodyValue])
                            (.raised bodyWordState value) hcalleeZero hbodyLoop hbodyWord
                          simp [loopCallBodyNormalOrReturnCompatible] at hcompatible
                      | returned bodyWordState wordValues =>
                          cases wordValues with
                          | nil =>
                              simp [RiscV.evalWordCallWithHandlersAndFfi,
                                hlookupWord, harguments, hwordBind, hbodyWord,
                                RiscV.assignWordRegisters] at hword
                          | cons wordValue rest' =>
                              cases rest' with
                              | cons value' rest'' =>
                                  simp [RiscV.evalWordCallWithHandlersAndFfi,
                                    hlookupWord, harguments, hwordBind, hbodyWord,
                                    RiscV.assignWordRegisters] at hword
                              | nil =>
                                  have hcompatible := hbody
                                    { loopState with locals := calleeLocals } calleeWord
                                    (.returned bodyLoopState [bodyValue])
                                    (.returned bodyWordState [wordValue])
                                    hcalleeZero hbodyLoop hbodyWord
                                  have hvalue : wordValue = bodyValue := by
                                    simpa [loopCallBodyNormalOrReturnCompatible] using hcompatible
                                  have hloop' :
                                      some (LoopResult.normal
                                        { loopState with
                                          locals := updateLoopLocal loopState.locals
                                            destination bodyValue }) =
                                        some (LoopResult.normal finalLoop) := by
                                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                                      hreadLoop, hcalleeBind, hbodyLoop,
                                      loopAssignValues] using hloop
                                  let returnedWordState : RiscV.State width :=
                                    { wordState with
                                      memory := bodyWordState.memory
                                      privilege := bodyWordState.privilege
                                      mode := bodyWordState.mode }
                                  have hword' :
                                      some (RiscV.WordControlResult.normal
                                        (RiscV.writeRegister returnedWordState
                                          destinationRegister wordValue)) =
                                        some (RiscV.WordControlResult.normal finalWord) := by
                                    simpa [RiscV.evalWordCallWithHandlersAndFfi,
                                      hlookupWord, harguments, hwordBind, hbodyWord,
                                      RiscV.assignWordRegisters, hdestination] using hword
                                  injection hloop' with hloopResult
                                  injection hloopResult with hfinalLoop
                                  injection hword' with hwordResult
                                  injection hwordResult with hfinalWord
                                  subst finalLoop
                                  subst finalWord
                                  subst wordValue
                                  have hreturnedLocals :
                                      loopLocalsMappedToRiscV context loopState.locals
                                        returnedWordState := by
                                    intro name value hvalue'
                                    rcases hlocals name value hvalue' with
                                      ⟨register, hregister, hregisterValue⟩
                                    exact ⟨register, hregister, hregisterValue⟩
                                  exact loopLocalsMappedToRiscV_update context
                                    loopState.locals returnedWordState destination
                                    destinationRegister bodyValue hreturnedLocals
                                    hdestination hdestination_nonzero hnoalias
              | cons bodyValue rest =>
                  simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop,
                    hcalleeBind, hbodyLoop, loopAssignValues] at hloop

/-!
The corresponding exception-handler boundary leaves the callee and handler
bodies abstract: their recursive simulation proofs are supplied as
hypotheses, while the call dispatcher itself proves the source/Word frame
transition and exception binding.
-/

theorem loopToWord_call_handler_simulation_single_parameter [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (RiscV.Word width)))
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (loopHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → LoopState (RiscV.Word width) →
      Option (LoopState (RiscV.Word width)))
    (wordHandler : FunName → RiscV.Word width → RiscV.Word width →
      RiscV.Word width → RiscV.Word width → RiscV.State width →
      Option (RiscV.State width))
    (target parameter argument exception : Nat)
    (argumentValue : RiscV.Word width) (fuel : Nat)
    (loopBody handlerBody : LoopProg (RiscV.Word width))
    (parameterRegister exceptionRegister : Fin 32)
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hexception :
      RiscV.registerOfNat (wordFindVar context exception) =
        some exceptionRegister)
    (hexception_nonzero : exceptionRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hnoalias :
      ∀ name, name ≠ exception →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ exceptionRegister)
    (hbody : ∀ calleeLoop calleeWord loopResult wordResult,
      RiscV.readRegister calleeWord 0 = 0 →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel calleeLoop loopBody =
        some loopResult →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
        calleeWord (loopToWordProg context loopBody) = some wordResult →
      loopCallBodyResultCompatible loopResult wordResult)
    (hhandler : ∀ exceptionValue handlerWord handlerLoop handlerFinalWord,
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals exception exceptionValue) handlerWord →
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
          { loopState with
            locals := updateLoopLocal loopState.locals exception exceptionValue }
          handlerBody = some (.normal handlerLoop) →
      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
          handlerWord (loopToWordProg context handlerBody) =
            some (.normal handlerFinalWord) →
      loopLocalsMappedToRiscV context handlerLoop.locals handlerFinalWord)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        none (some target) [argument]
        (some (exception, handlerBody, .skip, [])) =
          some (.normal finalLoop))
    (hword :
      RiscV.evalWordCallWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
        wordState none (some target) [wordFindVar context argument]
        (some (wordFindVar context exception, loopToWordProg context handlerBody,
          0, 0)) =
          some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  rcases hlocals argument argumentValue hargument with
    ⟨_, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, _⟩
  have hcalleeWordEq :
      RiscV.writeRegister (RiscV.clearWordRegisters wordState)
          parameterRegister argumentValue = calleeWord := by
    have hbind := bindWordRegisters_single_parameter context wordState parameter
      argumentValue parameterRegister hparameter
    rw [hbind] at hwordBind
    injection hwordBind
  have hcalleeZero : RiscV.readRegister calleeWord 0 = 0 := by
    rw [← hcalleeWordEq]
    by_cases hzero : parameterRegister = 0
    · exact False.elim (hparameter_nonzero hzero)
    · have hzero' : (0 : Fin 32) ≠ parameterRegister := by
        intro h
        exact hzero h.symm
      simp [RiscV.clearWordRegisters, RiscV.writeRegister, RiscV.readRegister,
        hzero, hzero']
  cases hbodyLoop :
      evalLoopProgWithCallsAndFfi functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
        hbodyLoop] at hloop
  | some bodyLoopResult =>
      cases bodyLoopResult with
      | normal bodyLoopState =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState) (.normal bodyWordState)
                    hcalleeZero hbodyLoop hbodyWord
                  have hloop' :
                      some (LoopResult.normal loopState) =
                        some (LoopResult.normal finalLoop) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  have hword' :
                      some (RiscV.WordControlResult.normal
                        { wordState with
                          memory := bodyWordState.memory
                          privilege := bodyWordState.privilege
                          mode := bodyWordState.mode }) =
                        some (RiscV.WordControlResult.normal finalWord) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord] using hword
                  injection hloop' with hloopResult
                  injection hloopResult with hfinalLoop
                  injection hword' with hwordResult
                  injection hwordResult with hfinalWord
                  subst finalLoop
                  subst finalWord
                  intro name value hvalue
                  rcases hlocals name value hvalue with
                    ⟨register, hregister, hregisterValue⟩
                  exact ⟨register, hregister, hregisterValue⟩
              | returned bodyWordState values =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.returned bodyWordState values) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | raised bodyWordState value =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.normal bodyLoopState)
                    (.raised bodyWordState value) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
      | broke bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | continued bodyLoopState label =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | returned bodyLoopState values =>
          simp [evalLoopCallWithCallsAndFfi, hlookupLoop, hreadLoop, hcalleeBind,
            hbodyLoop] at hloop
      | raised bodyLoopState sourceException =>
          cases hbodyWord :
              RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                calleeWord (loopToWordProg context loopBody) with
          | none =>
              simp [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                harguments, hwordBind, hbodyWord] at hword
          | some bodyWordResult =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.normal bodyWordState) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | returned bodyWordState values =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.returned bodyWordState values) hcalleeZero hbodyLoop hbodyWord
                  simp [loopCallBodyResultCompatible] at hcompatible
              | raised bodyWordState targetException =>
                  have hcompatible := hbody { loopState with locals := calleeLocals }
                    calleeWord (.raised bodyLoopState sourceException)
                    (.raised bodyWordState targetException) hcalleeZero hbodyLoop hbodyWord
                  have hexceptionValue : sourceException = targetException := by
                    simpa [loopCallBodyResultCompatible] using hcompatible
                  have hloopHandler :
                      evalLoopProgWithCallsAndFfi functions loopHandler fuel
                        { loopState with
                          locals := updateLoopLocal loopState.locals exception
                            sourceException }
                        handlerBody = some (.normal finalLoop) := by
                    simpa [evalLoopCallWithCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] using hloop
                  let returnedWordState : RiscV.State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hwordHandler :
                      RiscV.evalWordFunctionWithHandlersAndFfi wordFunctions
                        wordHandler fuel
                        (RiscV.writeRegister returnedWordState
                          exceptionRegister sourceException)
                        (loopToWordProg context handlerBody) =
                          some (.normal finalWord) := by
                    simpa [RiscV.evalWordCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord, hexception,
                      hexceptionValue] using hword
                  have hreturnedLocals :
                      loopLocalsMappedToRiscV context loopState.locals
                        returnedWordState := by
                    intro name value hvalue
                    rcases hlocals name value hvalue with
                      ⟨register, hregister, hregisterValue⟩
                    exact ⟨register, hregister, hregisterValue⟩
                  have hhandlerLocals :=
                    loopLocalsMappedToRiscV_update context loopState.locals
                      returnedWordState exception exceptionRegister sourceException
                      hreturnedLocals hexception hexception_nonzero hnoalias
                  exact hhandler sourceException
                    (RiscV.writeRegister returnedWordState exceptionRegister
                      sourceException) finalLoop finalWord hhandlerLocals hloopHandler
                      hwordHandler

theorem loopToWord_binop_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : BinOp)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals left = some leftValue)
    (hright : loopState.locals right = some rightValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right]))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (evalLoopBinOp operator leftValue rightValue)) resultState := by
  intro resultState hresult
  rcases hlocals left leftValue hleft with
    ⟨leftRegister, hleft_register, hleft_value⟩
  rcases hlocals right rightValue hright with
    ⟨rightRegister, hright_register, hright_value⟩
  have hleft_value' : state.registers leftRegister = leftValue := by
    exact hleft_value
  have hright_value' : state.registers rightRegister = rightValue := by
    exact hright_value
  have hand (x y : RiscV.Word width) :
      AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  have hor (x y : RiscV.Word width) :
      OrOp.or x y = x ||| y := by
    change x.or y = x ||| y
    exact BitVec.or_eq x y
  have hxor (x y : RiscV.Word width) :
      HXor.hXor x y = x ^^^ y := by
    rfl
  cases operator <;>
    simp [loopToWordProg, wordCompileExp,
      wordCompileExp.wordCompileExpList] at hresult <;>
    simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      hdestination, hleft_register, hright_register] at hresult
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .add leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, 
        hleft_value', hright_value', evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .sub leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, 
        hleft_value', hright_value', evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .and leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, 
        hleft_value', hright_value', hand, evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .or leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, 
        hleft_value', hright_value', hor, evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .xor leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, 
        hleft_value', hright_value', evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value

theorem loopToWord_shift_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Shift)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals left = some leftValue)
    (hright : loopState.locals right = some rightValue)
    (hright_bounded : rightValue.toNat < width)
    (hoperator : operator = .lsl ∨ operator = .lsr)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.shift operator (.var left) (.var right)))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (match operator with
          | .lsl => ShiftLeft.shiftLeft leftValue rightValue
          | .lsr => ShiftRight.shiftRight leftValue rightValue
          | .asr => leftValue
          | .ror => leftValue)) resultState := by
  rcases hoperator with rfl | rfl
  all_goals
    intro resultState hresult
    rcases hlocals left leftValue hleft with
      ⟨leftRegister, hleft_register, hleft_value⟩
    rcases hlocals right rightValue hright with
      ⟨rightRegister, hright_register, hright_value⟩
    have hleft_value' : state.registers leftRegister = leftValue := by
      exact hleft_value
    have hright_value' : state.registers rightRegister = rightValue := by
      exact hright_value
    have hright_amount :
        RiscV.shiftAmount rightValue = rightValue.toNat := by
      simp [RiscV.shiftAmount, Nat.mod_eq_of_lt hright_bounded]
    have hshiftLeft (x y : RiscV.Word width) :
        ShiftLeft.shiftLeft x y = x <<< y.toNat := by
      rfl
    have hshiftRight (x y : RiscV.Word width) :
        ShiftRight.shiftRight x y = x >>> y.toNat := by
      rfl
    simp [loopToWordProg, wordCompileExp,
      ] at hresult
    simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      hdestination, hleft_register, hright_register] at hresult
    subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      simp [updateLoopLocal] at hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister,
        RiscV.readRegister, hdestination_nonzero, 
        hleft_value', hright_value', hright_amount,
        hshiftLeft, hshiftRight]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value

theorem loopToWord_const_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination : Nat)
    (value : RiscV.Word width) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hzero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.assign destination (.const value))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination value) resultState := by
  intro resultState hresult
  simp [loopToWordProg, wordCompileExp] at hresult
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, hdestination_lt, hdestination_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.execute, RiscV.writeRegister,
      RiscV.readRegister, hdestination_nonzero]
    exact hzero
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_seq_evaluation_decomposition [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (first second : LoopProg (RiscV.Word width))
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hloop :
      evalLoopProg 2 loopState (.seq first second) =
        some (.normal finalLoop))
    (hword :
      RiscV.evalWordProg state (loopToWordProg context (.seq first second)) =
        some finalWord) :
    ∃ middleLoop middleWord,
      evalLoopProg 1 loopState first = some (.normal middleLoop) ∧
        evalLoopProg 1 middleLoop second = some (.normal finalLoop) ∧
        RiscV.evalWordProg state (loopToWordProg context first) =
          some middleWord ∧
        RiscV.evalWordProg middleWord (loopToWordProg context second) =
          some finalWord := by
  cases hfirst : evalLoopProg 1 loopState first with
  | none =>
      simp [evalLoopProg, hfirst] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecond :
              evalLoopProg 1 middleLoop second = some (.normal finalLoop) := by
            simpa [evalLoopProg, hfirst] using hloop
          cases hwordFirst :
              RiscV.evalWordProg state (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordProg, hwordFirst] at hword
          | some middleWord =>
              have hwordSecond :
                  RiscV.evalWordProg middleWord
                    (loopToWordProg context second) = some finalWord := by
                simpa [loopToWordProg, RiscV.evalWordProg, hwordFirst] using hword
              exact ⟨middleLoop, middleWord, rfl, hsecond,
                rfl, hwordSecond⟩
      | returned middleLoop values =>
          simp [evalLoopProg, hfirst] at hloop
      | broke middleLoop label =>
          simp [evalLoopProg, hfirst] at hloop
      | continued middleLoop label =>
          simp [evalLoopProg, hfirst] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProg, hfirst] at hloop

theorem loopToWord_seq_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (first second : LoopProg (RiscV.Word width))
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hloop :
      evalLoopProg 2 loopState (.seq first second) =
        some (.normal finalLoop))
    (hword :
      RiscV.evalWordProg state (loopToWordProg context (.seq first second)) =
        some finalWord)
    (hfirst :
      ∀ middleLoop middleWord,
        evalLoopProg 1 loopState first = some (.normal middleLoop) →
        RiscV.evalWordProg state (loopToWordProg context first) =
          some middleWord →
        loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond :
      ∀ middleLoop middleWord,
        loopLocalsMappedToRiscV context middleLoop.locals middleWord →
        ∀ finalLoop finalWord,
          evalLoopProg 1 middleLoop second = some (.normal finalLoop) →
          RiscV.evalWordProg middleWord (loopToWordProg context second) =
            some finalWord →
          loopLocalsMappedToRiscV context finalLoop.locals finalWord) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  rcases loopToWord_seq_evaluation_decomposition context loopState state
      first second finalLoop finalWord hloop hword with
    ⟨middleLoop, middleWord, hfirst_loop, hsecond_loop,
      hfirst_word, hsecond_word⟩
  exact hsecond middleLoop middleWord
    (hfirst middleLoop middleWord hfirst_loop hfirst_word)
    finalLoop finalWord hsecond_loop hsecond_word

/-!
The same normal-path sequence rule with an arbitrary source fuel budget.  The
Word evaluator is fuel-free for non-call programs, while the Loop evaluator
uses `fuel + 1` for the enclosing sequence and `fuel` for each component.
-/
theorem loopToWord_seq_preserves_mapped_locals_fuel [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (first second : LoopProg (RiscV.Word width))
    (fuel : Nat) (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hfirst : ∀ middleLoop middleWord,
      evalLoopProg fuel loopState first = some (.normal middleLoop) →
      RiscV.evalWordProg state (loopToWordProg context first) = some middleWord →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond : ∀ middleLoop middleWord,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      ∀ finalLoop finalWord,
        evalLoopProg fuel middleLoop second = some (.normal finalLoop) →
        RiscV.evalWordProg middleWord (loopToWordProg context second) =
          some finalWord →
        loopLocalsMappedToRiscV context finalLoop.locals finalWord)
    (hloop :
      evalLoopProg (fuel + 1) loopState (.seq first second) =
        some (.normal finalLoop))
    (hword :
      RiscV.evalWordProg state (loopToWordProg context (.seq first second)) =
        some finalWord) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases hfirstLoop : evalLoopProg fuel loopState first with
  | none =>
      simp [evalLoopProg, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProg fuel middleLoop second = some (.normal finalLoop) := by
            simpa [evalLoopProg, hfirstLoop] using hloop
          cases hfirstWord : RiscV.evalWordProg state
              (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordProg, hfirstWord] at hword
          | some middleWord =>
              have hsecondWord :
                  RiscV.evalWordProg middleWord (loopToWordProg context second) =
                    some finalWord := by
                simpa [loopToWordProg, RiscV.evalWordProg, hfirstWord] using hword
              exact hsecond middleLoop middleWord
                (hfirst middleLoop middleWord hfirstLoop hfirstWord)
                finalLoop finalWord hsecondLoop hsecondWord
      | returned middleLoop values =>
          simp [evalLoopProg, hfirstLoop] at hloop
      | broke middleLoop label =>
          simp [evalLoopProg, hfirstLoop] at hloop
      | continued middleLoop label =>
          simp [evalLoopProg, hfirstLoop] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProg, hfirstLoop] at hloop

theorem loopToWord_condition_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Cmp) (condition : Nat)
    (right : RegImm (RiscV.Word width))
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => loopState.locals name) = some rightValue)
    (hoperator : operator = .equal ∨ operator = .notEqual ∨
      operator = .lower ∨ operator = .notLower ∨
      operator = .test ∨ operator = .notTest) :
    evalLoopCondition operator leftValue rightValue =
      RiscV.evalWordCondition state operator (wordFindVar context condition)
        (wordRegImm context right) := by
  rcases hlocals condition leftValue hleft with
    ⟨conditionRegister, hcondition_register, hcondition_value⟩
  have hand (x y : RiscV.Word width) :
      AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  cases right with
  | imm immediate =>
      have hright_value : immediate = rightValue := by
        simpa using hright
      subst rightValue
      rcases hoperator with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [evalLoopCondition, RiscV.evalWordCondition, wordRegImm,
          hcondition_register, hcondition_value, hand]
  | reg name =>
      have hright_local : loopState.locals name = some rightValue := by
        simpa using hright
      rcases hlocals name rightValue hright_local with
        ⟨rightRegister, hright_register, hright_value⟩
      rcases hoperator with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [evalLoopCondition, RiscV.evalWordCondition, wordRegImm,
          hcondition_register, hright_register, hcondition_value,
        hright_value, hand]

theorem loopToWord_ite_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Cmp) (condition : Nat)
    (right : RegImm (RiscV.Word width))
    (thenBranch elseBranch : LoopProg (RiscV.Word width))
    (live : List Nat) (leftValue rightValue : RiscV.Word width)
    (choose : Bool)
    (_hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => loopState.locals name) = some rightValue)
    (hchooseLoop : evalLoopCondition operator leftValue rightValue = some choose)
    (hchooseWord : RiscV.evalWordCondition state operator
        (wordFindVar context condition) (wordRegImm context right) = some choose)
    (hthen : ∀ middleLoop middleWord,
      evalLoopProg 1 loopState thenBranch = some (.normal middleLoop) →
      RiscV.evalWordProg state (loopToWordProg context thenBranch) = some middleWord →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    ( helse : ∀ middleLoop middleWord,
      evalLoopProg 1 loopState elseBranch = some (.normal middleLoop) →
      RiscV.evalWordProg state (loopToWordProg context elseBranch) = some middleWord →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord) :
    ∀ finalLoop finalWord,
      evalLoopProg 2 loopState
          (.ite operator condition right thenBranch elseBranch live) =
        some (.normal finalLoop) →
      RiscV.evalWordProg state
          (loopToWordProg context
            (.ite operator condition right thenBranch elseBranch live)) =
        some finalWord →
      loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases choose with
  | false =>
      intro finalLoop finalWord hloop hword
      have helse_loop :
          evalLoopProg 1 loopState elseBranch = some (.normal finalLoop) := by
        cases right <;> simp_all [evalLoopProg]
      cases hmiddle : RiscV.evalWordProg state (loopToWordProg context elseBranch) with
      | none =>
          cases right <;>
            simp_all [loopToWordProg, RiscV.evalWordProg]
      | some middleWord =>
          have helse_word :
              RiscV.evalWordProg state (loopToWordProg context elseBranch) =
                some middleWord := hmiddle
          have htick : RiscV.evalWordProg middleWord
              (.tick : WordProg (RiscV.Word width)) = some finalWord := by
            cases right <;>
              simp_all [loopToWordProg, RiscV.evalWordProg]
          exact loopToWord_tick_preserves_mapped_locals context finalLoop.locals
            middleWord (helse finalLoop middleWord helse_loop helse_word) finalWord htick
  | true =>
      intro finalLoop finalWord hloop hword
      have hthen_loop :
          evalLoopProg 1 loopState thenBranch = some (.normal finalLoop) := by
        cases right <;> simp_all [evalLoopProg]
      cases hmiddle : RiscV.evalWordProg state (loopToWordProg context thenBranch) with
      | none =>
          cases right <;>
            simp_all [loopToWordProg, RiscV.evalWordProg]
      | some middleWord =>
          have hthen_word :
              RiscV.evalWordProg state (loopToWordProg context thenBranch) =
                some middleWord := hmiddle
          have htick : RiscV.evalWordProg middleWord
              (.tick : WordProg (RiscV.Word width)) = some finalWord := by
            cases right <;>
              simp_all [loopToWordProg, RiscV.evalWordProg]
          exact loopToWord_tick_preserves_mapped_locals context finalLoop.locals
            middleWord (hthen finalLoop middleWord hthen_loop hthen_word) finalWord htick

theorem loopToWord_loop_break_exec [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordLoopProg 6 state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.loop [] (.break 0) [])) =
      some (.normal (RiscV.execute (RiscV.execute state (.addi 0 0 0))
        (.addi 0 0 0))) := by
  simp [loopToWordProg, RiscV.evalWordLoopProg, RiscV.evalWordLoopRepeat,
    RiscV.evalWordProg, RiscV.execute, RiscV.writeRegister, RiscV.nextPc]

theorem loopToWord_div_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination dividend divisor : Nat)
    (destinationRegister : Fin 32)
    (dividendValue divisorValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hdividend : loopState.locals dividend = some dividendValue)
    (hdivisor : loopState.locals divisor = some divisorValue)
    (hdivisor_nonzero : divisorValue ≠ 0)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.arith (.div destination dividend divisor))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (dividendValue / divisorValue)) resultState := by
  intro resultState hresult
  rcases hlocals dividend dividendValue hdividend with
    ⟨dividendRegister, hdividend_register, hdividend_value⟩
  rcases hlocals divisor divisorValue hdivisor with
    ⟨divisorRegister, hdivisor_register, hdivisor_value⟩
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hdividend_lt : wordFindVar context dividend < 32 :=
    RiscV.registerOfNat_some_lt hdividend_register
  have hdivisor_lt : wordFindVar context divisor < 32 :=
    RiscV.registerOfNat_some_lt hdivisor_register
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hdividend_fin :
      (⟨wordFindVar context dividend, hdividend_lt⟩ : Fin 32) =
        dividendRegister := by
    have h := hdividend_register
    simp [RiscV.registerOfNat, hdividend_lt] at h
    exact h
  have hdivisor_fin :
      (⟨wordFindVar context divisor, hdivisor_lt⟩ : Fin 32) =
        divisorRegister := by
    have h := hdivisor_register
    simp [RiscV.registerOfNat, hdivisor_lt] at h
    exact h
  simp [loopToWordProg, wordArith] at hresult
  simp [RiscV.evalWordProg, RiscV.wordArithToInstructions,
    RiscV.wordArithToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, hdestination_lt, hdividend_lt, hdivisor_lt,
    hdestination_fin, hdividend_fin, hdivisor_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    simp [updateLoopLocal] at hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    have hdividend_value' :
        state.registers dividendRegister = dividendValue := by
      exact hdividend_value
    have hdivisor_value' :
        state.registers divisorRegister = divisorValue := by
      exact hdivisor_value
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, 
      hdividend_value', hdivisor_value', 
      BitVec.udiv_def]
    intro hzero
    exact (hdivisor_nonzero hzero).elim
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_locValue_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination source : Nat)
    (destinationRegister sourceRegister : Fin 32)
    (sourceValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hsource : loopState.locals source = some sourceValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hsource_register :
      RiscV.registerOfNat (wordFindVar context source) =
        some sourceRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.locValue destination source)) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination sourceValue) resultState := by
  intro resultState hresult
  rcases hlocals source sourceValue hsource with
    ⟨mappedSourceRegister, hsource_map, hsource_value⟩
  have hsource_map_eq : mappedSourceRegister = sourceRegister := by
    simpa [hsource_register] using hsource_map.symm
  subst mappedSourceRegister
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hsource_lt : wordFindVar context source < 32 :=
    RiscV.registerOfNat_some_lt hsource_register
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hsource_fin :
      (⟨wordFindVar context source, hsource_lt⟩ : Fin 32) =
        sourceRegister := by
    have h := hsource_register
    simp [RiscV.registerOfNat, hsource_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.registerOfNat, hdestination_lt,
    hsource_lt, hdestination_fin, hsource_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    simp [updateLoopLocal] at hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero]
    exact hsource_value
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

/-!
An ordinary variable expression is lowered to the same register move as a
`locValue`.  Keeping this case explicit is useful because the Loop compiler
can produce both forms: source-generated assignments use `.assign` while
later lowering passes introduce `.locValue` directly.
-/
theorem loopToWord_assign_var_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination source : Nat)
    (destinationRegister sourceRegister : Fin 32)
    (sourceValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hsource : loopState.locals source = some sourceValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hsource_register :
      RiscV.registerOfNat (wordFindVar context source) =
        some sourceRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.var source))) = some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination sourceValue) resultState := by
  intro resultState hresult
  rcases hlocals source sourceValue hsource with
    ⟨mappedSourceRegister, hsource_map, hsource_value⟩
  have hsource_map_eq : mappedSourceRegister = sourceRegister := by
    simpa [hsource_register] using hsource_map.symm
  subst mappedSourceRegister
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hsource_lt : wordFindVar context source < 32 :=
    RiscV.registerOfNat_some_lt hsource_register
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hsource_fin :
      (⟨wordFindVar context source, hsource_lt⟩ : Fin 32) =
        sourceRegister := by
    have h := hsource_register
    simp [RiscV.registerOfNat, hsource_lt] at h
    exact h
  simp [loopToWordProg, wordCompileExp, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.registerOfNat, hdestination_lt,
    hsource_lt, hdestination_fin, hsource_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    simp [updateLoopLocal] at hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero]
    exact hsource_value
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_binop_assign_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : BinOp)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft_present : ∃ value, loopState.locals left = some value)
    (hright_present : ∃ value, loopState.locals right = some value)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 loopState
      (.assign destination (.op operator [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  cases hleft : loopState.locals left with
  | none =>
      obtain ⟨value, hvalue⟩ := hleft_present
      simp [hleft] at hvalue
  | some leftValue =>
      cases hright : loopState.locals right with
      | none =>
          obtain ⟨value, hvalue⟩ := hright_present
          simp [hright] at hvalue
      | some rightValue =>
          rcases hlocals left leftValue hleft with
            ⟨leftRegister, hleft_register, hleft_value⟩
          rcases hlocals right rightValue hright with
            ⟨rightRegister, hright_register, hright_value⟩
          have hleft_value' : state.registers leftRegister = leftValue := by
            exact hleft_value
          have hright_value' : state.registers rightRegister = rightValue := by
            exact hright_value
          have hand (x y : RiscV.Word width) :
              AndOp.and x y = x &&& y := by
            change x.and y = x &&& y
            exact BitVec.and_eq x y
          have hor (x y : RiscV.Word width) :
              OrOp.or x y = x ||| y := by
            change x.or y = x ||| y
            exact BitVec.or_eq x y
          have hxor (x y : RiscV.Word width) :
              HXor.hXor x y = x ^^^ y := by
            rfl
          cases operator <;>
            simp [evalLoopProg, evalLoopExp, evalLoopBinOp, loopToWordProg,
              wordCompileExp, wordCompileExp.wordCompileExpList,
              RiscV.evalWordProg, RiscV.wordExpToInstructions,
              RiscV.wordExpToInstruction, RiscV.executeInstructions,
              RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
              RiscV.nextPc, updateLoopLocal, hleft, hright,
              hleft_register, hright_register, 
              hleft_value', hright_value',
              hdestination, hdestination_nonzero, hand, hor]

theorem loopToWord_shift_assign_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Shift)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft_present : ∃ value, loopState.locals left = some value)
    (hright_present : ∃ value, loopState.locals right = some value)
    (hright_bounded :
      ∀ value, loopState.locals right = some value → value.toNat < width)
    (hoperator : operator = .lsl ∨ operator = .lsr)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 loopState
      (.assign destination (.shift operator (.var left) (.var right)))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.shift operator (.var left) (.var right))))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  cases hleft : loopState.locals left with
  | none =>
      obtain ⟨value, hvalue⟩ := hleft_present
      simp [hleft] at hvalue
  | some leftValue =>
      cases hright : loopState.locals right with
      | none =>
          obtain ⟨value, hvalue⟩ := hright_present
          simp [hright] at hvalue
      | some rightValue =>
          rcases hlocals left leftValue hleft with
            ⟨leftRegister, hleft_register, hleft_value⟩
          rcases hlocals right rightValue hright with
            ⟨rightRegister, hright_register, hright_value⟩
          have hleft_value' : state.registers leftRegister = leftValue := by
            exact hleft_value
          have hright_value' : state.registers rightRegister = rightValue := by
            exact hright_value
          have hright_amount :
              RiscV.shiftAmount rightValue = rightValue.toNat := by
            simp [RiscV.shiftAmount,
              Nat.mod_eq_of_lt (hright_bounded rightValue hright)]
          have hshiftLeft (x y : RiscV.Word width) :
              ShiftLeft.shiftLeft x y = x <<< y.toNat := by
            rfl
          have hshiftRight (x y : RiscV.Word width) :
              ShiftRight.shiftRight x y = x >>> y.toNat := by
            rfl
          rcases hoperator with rfl | rfl <;>
            simp [evalLoopProg, evalLoopExp, evalLoopShift, loopToWordProg,
              wordCompileExp, 
              RiscV.evalWordProg, RiscV.wordExpToInstructions,
              RiscV.wordExpToInstruction, RiscV.executeInstructions,
              RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
              RiscV.nextPc, updateLoopLocal, hleft, hright,
              hleft_register, hright_register, 
              hleft_value', hright_value', hdestination,
              hdestination_nonzero, hright_amount,
              hshiftLeft, hshiftRight,
              ]

theorem loopToWord_load32_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address destination : Nat)
    (destinationRegister : Fin 32) (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (haddress : loopState.locals address = some addressValue)
    (hmemory : loopState.memory addressValue = some value)
    (hmachine : RiscV.readWord32 state addressValue = value)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.load32 address destination)) =
          some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination value) resultState := by
  intro resultState hresult
  rcases hlocals address addressValue haddress with
    ⟨addressRegister, haddress_register, haddress_value⟩
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  have hsource_address :
      (loopRegisterStateMappedWithMemory context state loopState.memory).locals
        address = some addressValue := by
    simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
      haddress_register, haddress_value]
  have hsource :
      (evalLoopProg 1
        (loopRegisterStateMappedWithMemory context state loopState.memory)
        (.load32 address destination)).bind (fun result =>
          match result with
          | .normal sourceState => sourceState.locals destination
          | _ => none) = some value := by
    rw [evalLoopProg_load32
      (loopRegisterStateMappedWithMemory context state loopState.memory)
      address destination addressValue value hsource_address hmemory]
    simp [updateLoopLocal]
  have hagreement := loopToWord_load32_register_agreement_mapped context state
    loopState.memory address destination addressRegister destinationRegister
    addressValue value zero haddress_register hdestination haddress_value hmemory
    hmachine hdestination_nonzero
  have hdestination_value :
      RiscV.readRegister resultState destinationRegister = value := by
    rw [hresult] at hagreement
    rw [hsource] at hagreement
    simpa using hagreement.symm
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress_register
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg,
    RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
    RiscV.nextPc, RiscV.registerOfNat, haddress_lt, hdestination_lt,
    haddress_fin, hdestination_fin, 
    hdestination_nonzero] at hresult
  subst resultState
  have hloaded :
      RiscV.readWord32 state (state.registers addressRegister) = value := by
    have haddress_register_value :
        state.registers addressRegister = addressValue := by
      exact haddress_value
    rw [haddress_register_value, hmachine]
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.readRegister, hloaded]
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.readRegister, hregister_nonalias]
    exact hregister_value

theorem loopToWord_store32_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address value : Nat)
    (addressRegister valueRegister : Fin 32)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.store32 address value)) =
          some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg, RiscV.execute,
    RiscV.writeByte, RiscV.writeWord32, RiscV.byteAddress,
    RiscV.registerOfNat, haddress_lt, hvalue_lt, haddress_fin, hvalue_fin] at hresult
  subst resultState
  intro name current hcurrent
  rcases hlocals name current hcurrent with
    ⟨register, hregister, hregister_value⟩
  refine ⟨register, hregister, ?_⟩
  exact hregister_value

theorem loopToWord_loadByte_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address destination : Nat)
    (destinationRegister : Fin 32) (addressValue : RiscV.Word width)
    (byteValue : BitVec 8)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (haddress : loopState.locals address = some addressValue)
    (hmachine : RiscV.readByte state addressValue = byteValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.loadByte address destination)) =
          some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (BitVec.ofNat width byteValue.toNat)) resultState := by
  intro resultState hresult
  rcases hlocals address addressValue haddress with
    ⟨addressRegister, haddress_register, haddress_value⟩
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress_register
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg,
    RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
    RiscV.nextPc, RiscV.registerOfNat, haddress_lt, hdestination_lt,
    haddress_fin, hdestination_fin, 
    haddress_value', hmachine, hdestination_nonzero] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : BitVec.ofNat width byteValue.toNat = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.readRegister]
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.readRegister, hregister_nonalias,
      ]
    exact hregister_value

theorem loopToWord_storeByte_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address value : Nat)
    (addressRegister valueRegister : Fin 32)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.storeByte address value)) =
          some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg, RiscV.execute,
    RiscV.writeByte, RiscV.registerOfNat,
    haddress_lt, hvalue_lt, haddress_fin, hvalue_fin] at hresult
  subst resultState
  intro name current hcurrent
  exact hlocals name current hcurrent

theorem loopToWord_shMem_load8_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address destination : Nat)
    (destinationRegister : Fin 32) (addressValue : RiscV.Word width)
    (byteValue : BitVec 8)
    (zero : RiscV.ZeroRegister state)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (haddress : loopState.locals address = some addressValue)
    (hmemory : loopState.memory addressValue =
      some (BitVec.ofNat width byteValue.toNat))
    (hmachine : RiscV.readByte state addressValue = byteValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load8 destination (.var address))) = some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (BitVec.ofNat width byteValue.toNat)) resultState := by
  intro resultState hresult
  rcases hlocals address addressValue haddress with
    ⟨addressRegister, haddress_register, haddress_value⟩
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  have haddress_eval :
      evalLoopExp
        (loopRegisterStateMappedWithMemory context state loopState.memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress_register, haddress_value]
  have hsource :
      (evalLoopProg 1
        (loopRegisterStateMappedWithMemory context state loopState.memory)
        (.shMem .load8 destination (.var address))).bind (fun result =>
          match result with
          | .normal sourceState => sourceState.locals destination
          | _ => none) =
        some (BitVec.ofNat width byteValue.toNat) := by
    rw [evalLoopProg_shMem_load
      (loopRegisterStateMappedWithMemory context state loopState.memory)
      .load8 destination (.var address) addressValue
      (BitVec.ofNat width byteValue.toNat) (by simp) haddress_eval hmemory]
    simp [updateLoopLocal]
  have hagreement := loopToWord_loadByte_register_agreement_mapped context state
    loopState.memory address destination addressRegister destinationRegister
    addressValue (BitVec.ofNat width byteValue.toNat) byteValue zero
    haddress_register hdestination haddress_value hmemory hmachine
    hdestination_nonzero
  have hdestination_value :
      RiscV.readRegister resultState destinationRegister =
        BitVec.ofNat width byteValue.toNat := by
    rw [hresult] at hagreement
    rw [hsource] at hagreement
    simpa using hagreement.symm
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress_register
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, RiscV.registerOfNat,
    haddress_lt, hdestination_lt, haddress_fin, hdestination_fin,
    haddress_value', hmachine, hdestination_nonzero] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : BitVec.ofNat width byteValue.toNat = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.readRegister]
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.readRegister, hregister_nonalias,
      ]
    exact hregister_value

theorem loopToWord_shMem_store8_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address value : Nat)
    (addressRegister valueRegister : Fin 32)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store8 value (.var address))) = some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeByte,
    RiscV.registerOfNat, haddress_lt, hvalue_lt,
    haddress_fin, hvalue_fin] at hresult
  subst resultState
  intro name current hcurrent
  exact hlocals name current hcurrent

theorem loopToWord_shMem_load16_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address destination : Nat)
    (destinationRegister : Fin 32) (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (haddress : loopState.locals address = some addressValue)
    (hmemory : loopState.memory addressValue = some value)
    (hmachine : RiscV.readWord16 state addressValue = value)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load16 destination (.var address))) = some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination value) resultState := by
  intro resultState hresult
  rcases hlocals address addressValue haddress with
    ⟨addressRegister, haddress_register, haddress_value⟩
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  have haddress_eval :
      evalLoopExp
        (loopRegisterStateMappedWithMemory context state loopState.memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress_register, haddress_value]
  have hsource :
      (evalLoopProg 1
        (loopRegisterStateMappedWithMemory context state loopState.memory)
        (.shMem .load16 destination (.var address))).bind (fun result =>
          match result with
          | .normal sourceState => sourceState.locals destination
          | _ => none) = some value := by
    rw [evalLoopProg_shMem_load
      (loopRegisterStateMappedWithMemory context state loopState.memory)
      .load16 destination (.var address) addressValue value
      (by simp) haddress_eval hmemory]
    simp [updateLoopLocal]
  have hagreement := loopToWord_load16_register_agreement_mapped context state
    loopState.memory address destination addressRegister destinationRegister
    addressValue value zero haddress_register hdestination haddress_value hmemory
    hmachine hdestination_nonzero
  have hdestination_value :
      RiscV.readRegister resultState destinationRegister = value := by
    rw [hresult] at hagreement
    rw [hsource] at hagreement
    simpa using hagreement.symm
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress_register
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, RiscV.registerOfNat,
    haddress_lt, hdestination_lt, haddress_fin, hdestination_fin,
    haddress_value', hmachine, hdestination_nonzero] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.readRegister]
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.readRegister, hregister_nonalias,
      ]
    exact hregister_value

theorem loopToWord_shMem_store16_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address value : Nat)
    (addressRegister valueRegister : Fin 32)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store16 value (.var address))) = some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeWord16,
    RiscV.writeByte, RiscV.byteAddress, RiscV.registerOfNat,
    haddress_lt, hvalue_lt, haddress_fin, hvalue_fin] at hresult
  subst resultState
  intro name current hcurrent
  exact hlocals name current hcurrent

theorem loopToWord_shMem_load_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address destination : Nat)
    (destinationRegister : Fin 32) (addressValue value : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (haddress : loopState.locals address = some addressValue)
    (hmachine : RiscV.readWordValue state addressValue = value)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load destination (.var address))) = some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination value) resultState := by
  intro resultState hresult
  rcases hlocals address addressValue haddress with
    ⟨addressRegister, haddress_register, haddress_value⟩
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress_register
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, RiscV.registerOfNat,
    haddress_lt, hdestination_lt, haddress_fin, hdestination_fin,
    haddress_value', hmachine, hdestination_nonzero] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.readRegister]
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.readRegister, hregister_nonalias,
      ]
    exact hregister_value

theorem loopToWord_shMem_store_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address value : Nat)
    (addressRegister valueRegister : Fin 32)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store value (.var address))) = some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  have haddress_lt : wordFindVar context address < 32 :=
    RiscV.registerOfNat_some_lt haddress
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue
  have haddress_fin :
      (⟨wordFindVar context address, haddress_lt⟩ : Fin 32) = addressRegister := by
    have h := haddress
    simp [RiscV.registerOfNat, haddress_lt] at h
    exact h
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  simp [loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute,
    
    RiscV.registerOfNat,
    haddress_lt, hvalue_lt, haddress_fin, hvalue_fin] at hresult
  subst resultState
  intro name current hcurrent
  rcases hlocals name current hcurrent with
    ⟨register, hregister, hregister_value⟩
  refine ⟨register, hregister, ?_⟩
  change (RiscV.writeWordValue
      { pc := RiscV.nextPc state, registers := state.registers,
        memory := state.memory, privilege := state.privilege, mode := state.mode }
      (RiscV.readRegister state addressRegister)
      (RiscV.readRegister state valueRegister)).registers register = current
  rw [RiscV.writeWordValue_registers]
  exact hregister_value

theorem loopToWord_store_const_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (address : RiscV.Word width) (value : Nat)
    (valueValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hvalue : loopState.locals value = some valueValue)
    (hscratch :
      ∀ name current, loopState.locals name = some current →
        ∀ register,
        RiscV.registerOfNat (wordFindVar context name) = some register →
          register ≠ 31) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.store (.const address) value)) =
        some resultState →
      loopLocalsMappedToRiscV context loopState.locals resultState := by
  intro resultState hresult
  rcases hlocals value valueValue hvalue with
    ⟨valueRegister, hvalue_register, hvalue_value⟩
  have hvalue_lt : wordFindVar context value < 32 :=
    RiscV.registerOfNat_some_lt hvalue_register
  have hvalue_fin :
      (⟨wordFindVar context value, hvalue_lt⟩ : Fin 32) = valueRegister := by
    have h := hvalue_register
    simp [RiscV.registerOfNat, hvalue_lt] at h
    exact h
  have hvalue_not_scratch : wordFindVar context value ≠ 31 := by
    intro h
    have hregister := hvalue_register
    simp [RiscV.registerOfNat, h] at hregister
    exact hscratch value valueValue hvalue valueRegister hvalue_register
      hregister.symm
  simp [loopToWordProg, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.execute, RiscV.writeRegister,
    RiscV.registerOfNat,
    hvalue_lt, hvalue_fin, hvalue_not_scratch] at hresult
  subst resultState
  intro name current hcurrent
  rcases hlocals name current hcurrent with
    ⟨register, hregister, hregister_value⟩
  refine ⟨register, hregister, ?_⟩
  have hregister_nonalias := hscratch name current hcurrent register hregister
  simp only [RiscV.readRegister]
  rw [RiscV.writeWordValue_registers]
  simp [hregister_nonalias]
  exact hregister_value

end Flapjack
