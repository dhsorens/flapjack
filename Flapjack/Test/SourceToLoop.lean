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

end Flapjack
