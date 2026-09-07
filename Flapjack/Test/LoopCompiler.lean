import Flapjack.Test.Calls

namespace Flapjack

open RiscV
example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.while (.const (BitVec.ofNat 64 0)) .break)
            (.return (.const (BitVec.ofNat 64 7))), returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 7] := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.store (.const (BitVec.ofNat 64 100))
              (.const (BitVec.ofNat 64 42)))
            (.return (.load .one (.const (BitVec.ofNat 64 100)))),
          returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 42] := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .ite (.cmp .equal (.const (BitVec.ofNat 64 1))
            (.const (BitVec.ofNat 64 1)))
            (.return (.const (BitVec.ofNat 64 7)))
            (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  decide +kernel

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  decide +kernel

example :
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.globals.initializers.length = 1 ∧ result.crepe.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineExceptionCodes,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers,
    compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    compileProg, loopCompileProg, 
    lookupInfo,
    ]

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  decide +kernel

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.rStruct []), returnShape := .one }]) = false := by
  decide +kernel

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  decide +kernel

example :
    (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .seq (.return (.const 7)) .skip, returnShape := .one }]).2.length = 1 := by
  decide +kernel

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one },
       .function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 1), returnShape := .one }]) = false := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.decl .one "g" (.rStruct []), .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one }]) = false := by
  decide +kernel


end Flapjack
