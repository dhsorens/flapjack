import Flapjack.Test.RiscV
import Flapjack.Pipeline

namespace Flapjack

open RiscV

def pipelineStackAddDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "add", inline := false, exported := false,
      params := [("left", .one), ("right", .one)],
      body := .return (.op .add
        [.var .local "left", .var .local "right"]), returnShape := .one }]

def pipelineStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def pipelineHandlerDeclarations : List (Decl (RiscV.Word 64)) :=
  [.exnDecl "E" .one,
   .function
    { name := "raise", inline := false, exported := false, params := [],
      body := .raise "E" (.const (BitVec.ofNat 64 7)), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true, params := [],
      body := .dec "exception" .one (.const (BitVec.ofNat 64 0))
        (.call (some (none, some ("E", "exception",
          .return (.var .local "exception")))) "raise" []),
      returnShape := .one }]

def pipelineFfiDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .extCall "sum"
        (.const (BitVec.ofNat 64 2))
        (.const (BitVec.ofNat 64 3))
        (.const (BitVec.ofNat 64 4))
        (.const (BitVec.ofNat 64 5)),
      returnShape := .one }]

def pipelineAllocatedCallDeclarations : List (Decl (RiscV.Word 64)) :=
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

example :
    (compileFlapjackRiscVViaStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineStackAddDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) [("sum", 7)]
      pipelineStackRemoveConfig pipelineFfiDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineHandlerDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineStackAddDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineAllocatedCallDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaAllocatedStackLinked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      pipelineStackRemoveConfig pipelineAllocatedCallDeclarations).isSome := by
  native_decide

def globalTestContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

example :
    globalCompileExp globalTestContext (.var .global "g") =
      .load .one (.op .sub [.topAddr, .const 8]) := by
  simp [globalCompileExp, globalTestContext, lookupInfo]

example :
    globalCompileProg globalTestContext
        (.assign .global "g" (.const 7)) =
      .store (.op .sub [.topAddr, .const 8]) (.const 7) := by
  simp [globalCompileProg, globalCompileExp, globalTestContext, lookupInfo]

example :
    let result := globalCompileTop (α := Nat) 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.context.globalsSize = 1 := by
  simp [globalCompileTop, globalCollect, globalAddress, globalCompileDecls,
    globalCompileInitializers, globalCompileProg, globalCompileExp, lookupInfo]

example :
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.const 7), returnShape := .one }]
    result.simplified.length = 1 ∧ result.structured.length = 1 ∧
      result.crepe.length = 1 ∧ result.loop.length = 1 ∧ result.word.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineExceptionCodes,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers,
    compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    compileProg, loopCompileProg, 
    
    ]

example [NeZero width] :
    pipelineRiscVFunctions
        (width := width)
        [(0, [], ((.seq (.assign 1 (.op .add [.var 2, .var 3]))
          (.return 0 [1])) : WordProg (RiscV.Word width)))] =
      [(0, [], some ([.add 1 2 3], [1]))] := by
    simp [pipelineRiscVFunctions, RiscV.wordFunctionToRiscVWithLoops,
    RiscV.wordFunctionToRiscVWithLoopsAux, RiscV.wordControlInstructions,
    RiscV.wordFunctionToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example :
    pipelineRiscVFunctionsWithFfi (width := 64) [("sum", 7)]
      [(7, [], (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6])))] =
      [(7, [], some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0,
        .addi 13 5 0, .addi 14 0 7, .ecall], [6]))] := by
  decide +kernel

example :
    let result := pipelineRiscVFunctionsWithFfi (width := 64) []
      [(7, [2], (.return 0 [2])),
       (8, [6], (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none))]
    result.length = 2 && result.all (fun (_, _, artifact) => artifact.isSome) := by
  decide +kernel

example [NeZero width] (state : RiscV.State width) (value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state) :
    RiscV.evalWordFunction state
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (RiscV.Word width)) =
      some (RiscV.execute state (.addi 1 0 value),
        [RiscV.readRegister (RiscV.execute state (.addi 1 0 value)) 1]) := by
  exact RiscV.evalWordFunction_return_const state value zero

def loopProgLongMulFingerprint : LoopProg α → Option (Nat × Nat × Nat × Nat)
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      some (destinationLeft, destinationRight, sourceLeft, sourceRight)
  | _ => none

example :
    (loopCompileExp loopContext 3 []
      (.crepOp .mul [.var 0, .var 1])).code.map loopProgLongMulFingerprint =
      [none, none, some (5, 5, 3, 4)] := by
  decide +kernel

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.panOp .mul [.const (BitVec.ofNat 64 2),
            .const (BitVec.ofNat 64 3)]), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      pipelineAddDeclarations
    result.linkedFunctions.isSome := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      pipelineAddDeclarations
    result.callLinkedFunctions.isSome := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "add", inline := false, exported := false,
          params := [("left", .one), ("right", .one)],
          body := .return (.op .add
            [.var .local "left", .var .local "right"]), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, parameters, artifact) =>
        parameters = [2, 3] && match artifact with
        | some (code, returns) =>
            returns = [5] && match code with
            | [.add destination left right] =>
                destination = 5 && left = 2 && right = 3
            | _ => false
        | none => false) := by
  native_decide

example : compiledPipelineAddRun 7 8 = some [15] := by
  native_decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.add 5 2 3] [5] [7, 8] (RiscV.zeroState 64) = some [15] := by
  exact RiscV.executeFunction_add

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.divU 5 2 3] [5] [42, 6] (RiscV.zeroState 64) = some [7] := by
  decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.remU 5 2 3] [5] [43, 6] (RiscV.zeroState 64) = some [1] := by
  decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.divU 5 2 3] [5] [42, 0] (RiscV.zeroState 64) =
        some [BitVec.ofNat 64 (2 ^ 64 - 1)] := by
  decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.remU 5 2 3] [5] [42, 0] (RiscV.zeroState 64) = some [42] := by
  decide

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.addCarry 5 6 2 3 4) =
      some [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] := by
  exact RiscV.wordArithToInstructions_addCarry

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.op .and [.var 2, .const (15 : RiscV.Word width)]) =
      some (.andi 1 2 15) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.op .sub [.var 2, .const (4 : RiscV.Word width)]) =
      some (.addi 1 2 (0 - 4)) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
        (.shift .lsr (.var 2) (.const (3 : RiscV.Word width))) =
      some (.srli 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 8) [2]
      [.andi 5 2 15, .ori 6 5 16, .xori 7 6 3] [7] [BitVec.ofNat 8 10]
      (RiscV.zeroState 8) = some [25] := by
  decide

example :
    RiscV.executeFunction 10 (0 : RiscV.Word 8) [2]
      [.slli 5 2 2, .srli 6 5 1, .srai 7 6 1] [7] [BitVec.ofNat 8 10]
      (RiscV.zeroState 8) = some [10] := by
  decide

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.longMul 1 2 3 4) =
      some [.mulHU 1 3 4, .mul 2 3 4] := by
  exact RiscV.wordArithToInstructions_longMul

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.longMul 3 2 3 4) = none := by
  exact RiscV.wordArithToInstructions_longMul_alias

example [NeZero width] :
    RiscV.wordArithToInstructions (width := width) (.addCarry 31 6 2 3 4) = none := by
  simp [RiscV.wordArithToInstructions]

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3, 4]
      [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] [5, 6]
      [BitVec.ofNat 8 255, 1, 1] (RiscV.zeroState 8) = some [1, 1] := by
  decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3]
      [.mulHU 5 2 3, .mul 6 2 3] [5, 6]
      [BitVec.ofNat 8 255, 2] (RiscV.zeroState 8) = some [1, 254] := by
  decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2, 3, 4]
      [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] [5, 6] [10, 20, 7]
      (RiscV.zeroState 8) = some [31, 0] := by
  decide

example :
    loopToWordProg ({ vars := [] } : WordContext)
      (.primitive [7, 8] .addCarry [2, 3, 4]) =
      .inst (.arith (.addCarry 7 8 2 3 4)) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo]

example [NeZero width] :
    RiscV.wordArithToInstruction (width := width) (.div 1 2 3) =
      some (.divU 1 2 3) := by
  exact RiscV.wordArithToInstruction_div

example (left right : RiscV.Word 64) :
    RiscV.executeFunction 10 (0 : RiscV.Word 64) [2, 3]
      [.add 5 2 3] [5] [left, right] (RiscV.zeroState 64) = some [left + right] := by
  exact RiscV.executeFunction_add_general left right

example :
    (pipelineEnsureMain (α := Nat) []).map (fun declaration =>
      match declaration with
      | .function function => function.name
      | _ => "not-main") = ["main"] := by
  decide +kernel

example :
    (pipelineEnsureMain (α := Nat)
      [.decl .one "global" (.const 7),
       .function
         { name := "worker", inline := false, exported := false, params := [],
           body := .return (.const 1), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .return (.const 0), returnShape := .one }]).map
        (fun declaration =>
          match declaration with
          | .function function => function.name
          | .decl _ name _ => name
          | .name name _ => name
          | .exnDecl name _ => name) =
      ["main", "global", "worker"] := by
  decide +kernel

example :
    let result := compileFlapjackRiscVTarget (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "worker", inline := false, exported := false, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]
    result.pipeline.simplified.map (fun declaration =>
      match declaration with
      | .function function => function.name
      | _ => "not-function") = ["main", "worker"] := by
  decide +kernel

end Flapjack
