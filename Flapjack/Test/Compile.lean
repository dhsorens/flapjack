import Flapjack.Test.Basics

namespace Flapjack

open RiscV

def crepContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 1 }

def callContext : CompileContext Nat :=
  { crepContext with functions := [("f", ([], .one))], exceptions := [("E", 9)] }

def assignmentContext : CompileContext Nat :=
  { vars := [("x", (.one, [0]))], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

def loopContext : LoopContext Nat :=
  { vars := [], functions := [("f", (64, 0))], maxVar := 2,
    target := .rv64i }

def wordContext : WordContext :=
  { vars := [(3, 2), (4, 3)] }

def identityFunction : FunDecl Nat :=
  { name := "identity", inline := false, exported := false, params := [("x", .one)],
    body := .return (.var .local "x"), returnShape := .one }

def constantFunction : FunDecl Nat :=
  { name := "constant", inline := false, exported := false, params := [],
    body := .return (.const 7), returnShape := .one }

example :
    (compileFunDecl assignmentContext identityFunction).params = [0] := by
  simp [compileFunDecl, compileParamVars, identityFunction]

example :
    (compileFunDecl assignmentContext identityFunction).body =
      .return [.var 0] := by
  simp [compileFunDecl, compileParamVars, identityFunction, compileProg, compileExp,
    lookupInfo]

example :
    (compileToCrepe assignmentContext [.function constantFunction]).head?.map
        CompiledFunction.body =
      some (.return [.const 7]) := by
  simp [compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    functionInfos, constantFunction, compileProg, compileExp]

example :
    compileExp crepContext (Exp.var .local "pair") =
      ([.var 0, .var 1], .comb [.one, .one]) := by
  simp [compileExp, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.rField 1 (Exp.var .local "pair")) =
      ([.var 1], .one) := by
  simp [compileExp, compileField, crepContext, lookupInfo]

example :
    compileExp crepContext (Exp.const (α := Nat) 7) = ([.const 7], .one) := by
  simp [compileExp]

example :
    compileExp crepContext (Exp.bytesInWord : Exp Nat) = ([.const 1], .one) := by
  simp [compileExp, crepContext]

example :
    compileProg assignmentContext
      (.assign .local "x" (.var .local "x")) =
      .dec 1 (.var 0) (.seq (.assign 0 (.var 1)) .skip) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, crepNestedSeq,
    assignmentContext, lookupInfo, distinctLists, crepExpVars]

example :
    loadShape (0 : Nat) 4 2 (.var 3) =
      [.load (.var 3), .load (.op .add [.var 3, .const 4])] := by
  simp [loadShape]

example :
    cexpHeads ([ [.var 0], [.var 1] ] : List (List (CrepExp Nat))) =
      some [.var 0, .var 1] := by
  rfl

example : compileProg crepContext .skip = (.skip : CrepProg Nat) := by
  simp [compileProg]

example :
    compileProg crepContext (.return (.const (α := Nat) 7)) =
      .return [.const 7] := by
  simp [compileProg, compileExp]

example :
    compileProg crepContext (.seq .skip (.tick : Prog Nat)) =
      .seq .skip .tick := by
  simp [compileProg]

example :
    compileProg crepContext (.call none "f" [.const (α := Nat) 1]) =
      .call none "f" [.const 1] := by
  simp [compileProg, compileArgs, compileExp]

example :
    compileProg callContext (.call (some (none, none)) "f" []) =
      .call (some ([2], none)) "f" [] := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, callContext,
    crepContext, lookupInfo]

example :
    compileProg callContext
      (.call (some (none, some ("E", "missing", .skip))) "f" []) =
      .call (some ([2], some (9, .seq .skip .skip))) "f" [] := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames, compileProg,
    callContext, crepContext, lookupInfo]

example :
    compileProg callContext (.raise "E" (.const (α := Nat) 0)) =
      .seq (.dec 2 (.const 0) (.seq (.storeGlob 0 (.var 2)) .skip)) (.raise 9) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, storeGlobals, crepNestedSeq,
    callContext, crepContext, lookupInfo]

example :
    compileProg assignmentContext
      (.primitive "x" .addCarry [.const (α := Nat) 3]) =
      .dec 1 (.const 3) (.primitive [0] .addCarry [1]) := by
  simp [compileProg, compileExp, compileArgs, freshNames, nestedDecs,
    assignmentContext, lookupInfo]

example :
    compileProg assignmentContext
      (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4)) =
      .dec 1 (.const 1)
        (.dec 2 (.const 2)
          (.dec 3 (.const 3)
            (.dec 4 (.const 4) (.extCall "ffi" 1 2 3 4)))) := by
  simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
    assignmentContext]

example :
    compileProg assignmentContext
      (.shMemLoad .op8 .local "x" (.const 10)) =
      .shMem .load8 0 (.const 10) := by
  simp [compileProg, firstCompiledExp, compileExp, loadMemOp,
    assignmentContext, lookupInfo]

example :
    compileProg assignmentContext
      (.shMemStore .op8 (.const 10) (.const 7)) =
      .dec 1 (.const 7) (.shMem .store8 1 (.const 10)) := by
  simp [compileProg, firstCompiledExp, compileExp, storeMemOp, nestedDecs,
    assignmentContext]

example :
    evalCrepProg (fun _ => none) (compileProg crepContext (.return (.const (α := Nat) 7))) =
      some [7] := by
  simp [compileProg, evalCrepProg, evalCrepExps, evalCrepExp, compileExp]

example :
    (evalCrepStateProg (fun _ => none)
        (compileProg assignmentContext
          (.seq (.assign .local "x" (.const 7))
            (.return (.var .local "x"))))).map Prod.snd =
      some [7] := by
  simp [compileProg, compileExp, crepNestedSeq, evalCrepStateProg, evalCrepExp, evalCrepExps,
    updateCrepLocal, assignmentContext,
    lookupInfo, distinctLists]

def crepAddCarryHandler : CrepPrimitiveHandler Nat
  | .addCarry, [left, right, carry] => some [left + right + carry, 0]
  | _, _ => none

example :
    (evalCrepStateProgWithPrimitive crepAddCarryHandler (fun _ => none)
      (compileProg crepContext
        (.seq
          (.primitive "pair" .addCarry
            [.const (α := Nat) 1, .const 2, .const 0])
          (.return (.var .local "pair"))))).map Prod.snd =
      some [3, 0] := by
  decide +kernel

def crepWordContext : CompileContext (RiscV.Word 64) :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], functions := [],
    exceptions := [], maxVar := 1, bytesInWord := BitVec.ofNat 64 8 }

def crepPrimitiveSource : Prog (RiscV.Word 64) :=
  .seq
    (.primitive "pair" .addCarry
      [.const 1, .const 2, .const 0])
    (.return (.var .local "pair"))

def crepPrimitiveSourceLocals : VarName → Option (PanValue (RiscV.Word 64)) :=
  fun name => if name == "pair" then
    some (.rStruct [.word 0, .word 0])
  else none

example :
    (evalCrepStateProgWithPrimitive RiscV.loopPrimitiveHandler (fun _ => none)
      (compileProg crepWordContext crepPrimitiveSource)).map Prod.snd =
      (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
        crepPrimitiveSourceLocals (fun _ => none) (fun _ => none)
        RiscV.panPrimitiveHandler crepPrimitiveSource).map
        (fun result => result.2.2.2.flatMap panValueWords) := by
  decide +kernel

example :
    evalCrepMemResultWithPrimitive
        (fun _ _ => some [6]) (fun name => if name == 1 then some 1
          else if name == 2 then some 2 else if name == 3 then some 3 else none)
        (fun _ => none)
      (.seq
        (.store (.const (α := Nat) 10) (.const 7))
        (.seq
          (.primitive [0] .addCarry [1, 2, 3])
          (.return [.load (.const 10), .var 0]))) =
      some [7, 6] := by
  decide +kernel

example :
    evalCrepMemResult (fun _ => none) (fun _ => none)
      (compileProg assignmentContext
        (.seq (.store (.const 10) (.const 7))
          (.return (.load .one (.const 10))))) =
      some [7] := by
    simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    loadShape, evalCrepMemResult, evalCrepMemProg, evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, updateMemory, updateCrepLocal, assignmentContext]

example :
    lowerLoopExp (CrepExp.cmp .equal (.var 0) (.const (α := Nat) 1)) =
      .cmp .equal (.var 0) (.const 1) := by
  simp [lowerLoopExp]

example :
    lowerLoopProg (CrepProg.seq .skip (.tick : CrepProg Nat)) =
      .seq .skip .tick := by
  simp [lowerLoopProg]

example :
    lowerLoopProg (CrepProg.store (.const (α := Nat) 0) (.const 7)) =
      (.fail : LoopProg Nat) := by
  simp [lowerLoopProg]

example :
    (loopCompileExp loopContext 3 [] (.load32 (.const (α := Nat) 8))).code =
      [.assign 3 (.const 8), .load32 3 3] := by
  simp [loopCompileExp]

example :
    loopCompileProg loopContext []
      (.return [(.const (α := Nat) 7)]) =
      .seq (.seq (.assign 3 (.const 7)) .skip) (.return [3]) := by
  simp [loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, loopContext]

example :
    loopCompileProg loopContext []
        (.store32 (.const (α := Nat) 8) (.const 255)) =
      .seq .skip
        (.seq (.assign 3 (.const 8))
          (.seq (.assign 4 (.const 255)) (.store32 3 4))) := by
  simp [loopCompileProg, loopCompileExp, loopCompileExps, loopNestedSeq,
    loopContext]

example :
    loopToWordExp (LoopExp.baseAddr : LoopExp Nat) = some (.lookup .currHeap) := by
  simp [loopToWordExp]

example :
    loopToWordProg wordContext (.assign 3 (.const (α := Nat) 7)) =
      .assign 2 (.const 7) := by
  simp [loopToWordProg, wordCompileExp, wordFindVar, lookupNatInfo, wordContext]

example :
    loopToWordProg wordContext (.seq (.load32 3 4) (.store32 3 4)) =
      .seq (.inst (.mem .load32 3 2)) (.inst (.mem .store32 3 2)) := by
  simp [loopToWordProg, wordFindVar, lookupNatInfo, wordContext]

example :
    loopVarsOfExp ((LoopExp.op .add [.var 1, .load (.var 2)]) : LoopExp Nat) =
      [1, 2] := by
  simp [loopVarsOfExp]

example :
    loopAssignedVars (LoopProg.seq (.assign 1 (.const 0)) (.load32 1 2)) = [1, 2] := by
  rfl

example :
  loopAccVars (LoopProg.assign 1 (.op .add [.var 2, .const 0])) [] = [2, 1] := by
  native_decide

end Flapjack
