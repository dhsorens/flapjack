import Flapjack.Correctness

/-!
Concrete regressions for the first Pancake-to-Loop semantic compositions.
These fixtures intentionally use empty environments: the source expression is
closed, so the test isolates expression lowering and Loop execution.
-/

namespace Flapjack

def sourceToLoopCompileContext : CompileContext (RiscV.Word 64) :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := BitVec.ofNat 64 8 }

def sourceToLoopLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := [], functions := [], maxVar := 0, target := .rv64i }

def sourceToLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopAddProgram : Prog (RiscV.Word 64) :=
  .return (.op .add
    [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 35)])

theorem sourceToLoop_add_const_simulation :
    (evalLoopProg 12 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopAddProgram))).map
        loopResultValues =
      evalPanProg (fun _ => none) sourceToLoopAddProgram := by
  exact compilePanToLoop_return_add_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (BitVec.ofNat 64 7) (BitVec.ofNat 64 35)

theorem sourceToLoop_add_const_executes :
    (evalLoopProg 12 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopAddProgram))).map
        loopResultValues = some [BitVec.ofNat 64 42] := by
  decide +kernel

def sourceToLoopMulProgram : Prog (RiscV.Word 64) :=
  .return (.panOp .mul
    [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)])

theorem sourceToLoop_mul_const_simulation :
    (evalLoopProg 16 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopMulProgram))).map
        loopResultValues =
      evalPanProg (fun _ => none) sourceToLoopMulProgram := by
  exact compilePanToLoop_return_mul_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (BitVec.ofNat 64 2) (BitVec.ofNat 64 3)

theorem sourceToLoop_mul_const_executes :
    (evalLoopProg 16 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopMulProgram))).map
        loopResultValues = some [BitVec.ofNat 64 6] := by
  decide +kernel

def sourceToLoopEqualProgram : Prog (RiscV.Word 64) :=
  .return (.cmp .equal (.const (BitVec.ofNat 64 7))
    (.const (BitVec.ofNat 64 7)))

theorem sourceToLoop_equal_const_simulation :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopEqualProgram))).map
        loopResultValues =
      evalPanProg (fun _ => none) sourceToLoopEqualProgram := by
  exact compilePanToLoop_return_equal_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (BitVec.ofNat 64 7) (BitVec.ofNat 64 7)

theorem sourceToLoop_equal_const_executes :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopEqualProgram))).map
        loopResultValues = some [BitVec.ofNat 64 1] := by
  decide +kernel

def sourceToLoopNotEqualProgram : Prog (RiscV.Word 64) :=
  .return (.cmp .equal (.const (BitVec.ofNat 64 7))
    (.const (BitVec.ofNat 64 35)))

theorem sourceToLoop_not_equal_const_executes :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopNotEqualProgram))).map
        loopResultValues = some [BitVec.ofNat 64 0] := by
  decide +kernel

def sourceToLoopConditionalProgram : Prog (RiscV.Word 64) :=
  .ite (.cmp .equal (.const (BitVec.ofNat 64 7))
      (.const (BitVec.ofNat 64 7)))
    (.return (.const (BitVec.ofNat 64 11)))
    (.return (.const (BitVec.ofNat 64 22)))

theorem sourceToLoop_conditional_simulation :
    (evalLoopProg 60 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopConditionalProgram))).map loopResultValues =
      evalPanProg (fun _ => none) sourceToLoopConditionalProgram := by
  exact compilePanToLoop_ite_equal_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (BitVec.ofNat 64 7) (BitVec.ofNat 64 7)
    (BitVec.ofNat 64 11) (BitVec.ofNat 64 22) (by decide)

theorem sourceToLoop_conditional_true_executes :
    (evalLoopProg 60 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopConditionalProgram))).map loopResultValues =
        some [BitVec.ofNat 64 11] := by
  decide +kernel

def sourceToLoopConditionalFalseProgram : Prog (RiscV.Word 64) :=
  .ite (.cmp .equal (.const (BitVec.ofNat 64 7))
      (.const (BitVec.ofNat 64 35)))
    (.return (.const (BitVec.ofNat 64 11)))
    (.return (.const (BitVec.ofNat 64 22)))

theorem sourceToLoop_conditional_false_executes :
    (evalLoopProg 60 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopConditionalFalseProgram))).map loopResultValues =
        some [BitVec.ofNat 64 22] := by
  decide +kernel

def sourceToLoopLocalCompileContext : CompileContext (RiscV.Word 64) :=
  { vars := [("x", (.one, [1]))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := BitVec.ofNat 64 8 }

def sourceToLoopLocalProgram : Prog (RiscV.Word 64) :=
  .seq (.assign .local "x" (.const (BitVec.ofNat 64 42)))
    (.return (.var .local "x"))

theorem sourceToLoop_local_assign_return_simulation :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopLocalCompileContext
          sourceToLoopLocalProgram))).map loopResultValues =
      (evalPanStateProg (fun _ => none) sourceToLoopLocalProgram).map
        Prod.snd := by
  exact compilePanToLoop_local_assign_return_const_correct
    sourceToLoopLocalCompileContext sourceToLoopLoopContext []
    sourceToLoopState "x" 1 (BitVec.ofNat 64 42)
    (by simp [sourceToLoopLocalCompileContext, lookupInfo])

theorem sourceToLoop_local_assign_return_executes :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopLocalCompileContext
          sourceToLoopLocalProgram))).map loopResultValues =
        some [BitVec.ofNat 64 42] := by
  decide +kernel

def sourceToLoopBoundLocalState : LoopState (RiscV.Word 64) :=
  { locals := fun slot =>
      if slot = 1 then some (BitVec.ofNat 64 42) else none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopBoundLocalSource : VarName → Option (RiscV.Word 64) :=
  fun name => if name == "x" then some (BitVec.ofNat 64 42) else none

theorem sourceToLoop_local_return_simulation :
    (evalLoopProg 16 sourceToLoopBoundLocalState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopLocalCompileContext
          (.return (.var .local "x"))))).map loopResultValues =
      (evalPanStateProg sourceToLoopBoundLocalSource
        (.return (.var .local "x"))).map Prod.snd := by
  exact compilePanToLoop_local_return_correct
    sourceToLoopLocalCompileContext sourceToLoopLoopContext []
    sourceToLoopBoundLocalState sourceToLoopBoundLocalSource "x" 1
    (by simp [sourceToLoopLocalCompileContext, lookupInfo])
    (by simp [sourceToLoopBoundLocalState, sourceToLoopBoundLocalSource])

theorem sourceToLoop_local_return_executes :
    (evalLoopProg 16 sourceToLoopBoundLocalState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopLocalCompileContext
          (.return (.var .local "x"))))).map loopResultValues =
        some [BitVec.ofNat 64 42] := by
  decide +kernel

def sourceToLoopDeclarationProgram : Prog (RiscV.Word 64) :=
  .dec "x" .one (.const 42)
    (.return (.var .local "x"))

theorem sourceToLoop_declaration_return_simulation :
    (evalLoopProg 16 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationProgram))).map loopResultValues =
      (evalPanStateProg (fun _ => none) sourceToLoopDeclarationProgram).map
        Prod.snd := by
  exact compilePanToLoop_dec_return_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (fun _ => none) "x" (BitVec.ofNat 64 42) (by rfl)

theorem sourceToLoop_declaration_return_executes :
    (evalLoopProg 16 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationProgram))).map loopResultValues =
        some [BitVec.ofNat 64 42] := by
  native_decide

def sourceToLoopDeclarationAddProgram : Prog (RiscV.Word 64) :=
  .dec "x" .one
    (.op .add [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 35)])
    (.return (.var .local "x"))

theorem sourceToLoop_declaration_add_return_simulation :
    (evalLoopProg 20 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationAddProgram))).map loopResultValues =
      (evalPanStateProg (fun _ => none) sourceToLoopDeclarationAddProgram).map
        Prod.snd := by
  exact compilePanToLoop_dec_return_add_const_correct
    sourceToLoopCompileContext sourceToLoopLoopContext [] sourceToLoopState
    (fun _ => none) "x" (BitVec.ofNat 64 7) (BitVec.ofNat 64 35) (by rfl)

theorem sourceToLoop_declaration_add_return_executes :
    (evalLoopProg 20 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationAddProgram))).map loopResultValues =
        some [BitVec.ofNat 64 42] := by
  native_decide

def sourceToLoopDeclarationMulProgram : Prog (RiscV.Word 64) :=
  .dec "x" .one
    (.panOp .mul [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)])
    (.return (.var .local "x"))

theorem sourceToLoop_declaration_mul_return_executes :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationMulProgram))).map loopResultValues =
        some [BitVec.ofNat 64 6] := by
  native_decide

theorem sourceToLoop_declaration_mul_return_simulation :
    (evalLoopProg 30 sourceToLoopState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          sourceToLoopDeclarationMulProgram))).map loopResultValues =
      (evalPanStateProg (fun _ => none) sourceToLoopDeclarationMulProgram).map
        Prod.snd := by
  native_decide

end Flapjack
