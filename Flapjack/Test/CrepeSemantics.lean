import Flapjack.CrepeSemantics
import Flapjack.CrepeCorrectness
import Flapjack.CrepeRuntime
import Flapjack.Test.CrepCalls

namespace Flapjack

/-! Small executable witnesses for every control-result constructor in the
    full Crepe evaluator. These are deliberately word-polymorphic in the
    implementation, while the regression uses Nat to keep reduction fast. -/

def crepeSemanticsState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepeSemanticsPrimitive : CrepPrimitiveHandler Nat
  | .addCarry, [left, right, carry] => some [left + right + carry, 0]
  | _, _ => none

def crepeSemanticsFfi : CrepFfiHandler Nat :=
  noCrepFfi Nat

def crepeSemanticsFfiHandler : CrepFfiHandler Nat :=
  fun function configuration configurationLength array arrayLength state =>
    if function == "sum" then
      some { state with
        memory := updateMemory state.memory 99
          (configuration + configurationLength + array + arrayLength) }
    else none

def crepeSemanticsSharedMem : CrepSharedMemHandler Nat :=
  defaultCrepSharedMemHandler

def crepeSemanticsFunctions : List (CompiledFunction Nat) :=
  [{ name := "inc"
     params := [0]
     body := .return [.op .add [.var 0, .const 1]]
     returnShape := .one }]

def crepeSemanticsCall : CrepProg Nat :=
  .seq
    (.dec 1 (.const 41)
      (.call (some ([2], none)) "inc" [.var 1]))
    (.return [.var 2])

def crepeSemanticsLoop : CrepProg Nat :=
  .seq
    (.assign 0 (.const 3))
    (.seq
      (.while (.var 0)
        (.seq
          (.assign 0 (.op .sub [.var 0, .const 1]))
          (.ite (.cmp .equal (.var 0) (.const 0)) (.break 0) .skip)))
      (.return [.var 0]))

def crepeSemanticsHandlerFunctions : List (CompiledFunction Nat) :=
  [{ name := "raise"
     params := []
     body := .raise 7
     returnShape := .one }]

def crepeSemanticsHandlerCall : CrepProg Nat :=
  .call (some ([], some (7, .return [.const 9]))) "raise" []

def crepeSemanticsMemory : CrepProg Nat :=
  .seq
    (.store (.const 10) (.const 7))
    (.seq
      (.shMem .load 0 (.const 10))
      (.return [.var 0]))

def crepeSemanticsPrimitiveProgram : CrepProg Nat :=
  .seq
    (.assign 1 (.const 1))
    (.seq
      (.assign 2 (.const 2))
      (.seq
        (.assign 3 (.const 0))
        (.seq
          (.primitive [4, 5] .addCarry [1, 2, 3])
          (.return [.var 4]))))

def crepeSemanticsFfiProgram : CrepProg Nat :=
  crepNestedSeq
    [.assign 1 (.const 10), .assign 2 (.const 1),
     .assign 3 (.const 20), .assign 4 (.const 2),
     .extCall "sum" 1 2 3 4, .return [.load (.const 99)]]

def crepeFfiContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

def crepeRuntimeState : CrepRuntimeState Nat Unit :=
  { locals := fun name =>
      match name with
      | 1 => some 10
      | 2 => some 1
      | 3 => some 20
      | 4 => some 2
      | _ => none
    globals := fun _ => none
    functions := []
    memory := fun address => if address == 10 then some 7 else none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    byteAlign := id
    clock := 10
    bigEndian := false
    ffi := ()
    baseAddress := 0
    topAddress := 100 }

def crepeRuntimeFinalHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .extCall _ _ _ _ _ => .final "halt"
    | .sharedMem _ _ _ => .returned state

def crepeRuntimeSharedHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .sharedMem .load name address =>
        match state.memory address with
        | some value =>
            .returned { state with
              locals := updateCrepLocal state.locals name value }
        | none => .returned state
    | .sharedMem _ _ _ => .returned state
    | .extCall _ _ _ _ _ => .returned state

theorem crepe_full_call_semantics :
    evalCrepFullResult crepeSemanticsFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsCall =
      some [42] := by
  decide +kernel

theorem crepe_full_loop_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 50 crepeSemanticsState crepeSemanticsLoop =
      some [0] := by
  decide +kernel

theorem crepe_full_handler_semantics :
    evalCrepFullResult crepeSemanticsHandlerFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsHandlerCall =
      some [9] := by
  decide +kernel

theorem crepe_full_memory_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsMemory =
      some [7] := by
  decide +kernel

theorem crepe_full_primitive_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsPrimitiveProgram =
      some [3] := by
  decide +kernel

theorem crepe_full_ffi_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfiHandler crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsFfiProgram =
      some [33] := by
  decide +kernel

theorem crepe_full_ffi_lowering_noop :
    evalCrepFullProg [] crepeSemanticsPrimitive
      (fun _ _ _ _ _ state => some state) crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState
      (compileProg crepeFfiContext
        (.extCall "noop" (.const 10) (.const 1) (.const 20) (.const 2))) =
      some (.normal crepeSemanticsState) := by
  exact (compile_full_extCall_const_noop_correct
    crepeFfiContext (fun _ => none) crepeSemanticsState
    crepeSemanticsPrimitive crepeSemanticsSharedMem
    0 100 10 1 20 2 "noop").1

theorem crepe_runtime_extCall_final :
    (crepRuntimeExtCall crepeRuntimeFinalHandler crepeRuntimeState
      "host" 1 2 3 4).1 = .finalFfi "halt" := by
  decide

theorem crepe_runtime_shared_load :
    (crepRuntimeSharedMem crepeRuntimeSharedHandler crepeRuntimeState
      .load 5 10).1 = .normal ∧
    (crepRuntimeSharedMem crepeRuntimeSharedHandler crepeRuntimeState
      .load 5 10).2.locals 5 = some 7 := by
  decide

theorem crepe_runtime_shared_address_error :
    (crepRuntimeSharedMem crepeRuntimeSharedHandler
      { crepeRuntimeState with shMemaddrs := fun _ => false }
      .load 5 10).1 = .error := by
  decide

def crepeRuntimeReturnProgram : CrepProg Nat :=
  .seq (.assign 5 (.const 3)) (.return [.var 5])

theorem crepe_runtime_full_return :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeState
      crepeRuntimeReturnProgram).map Prod.fst =
      some (.returned [3]) := by
  decide +kernel

theorem crepe_runtime_full_final_ffi :
    (evalCrepRuntimeResult crepeRuntimeFinalHandler
      crepeSemanticsPrimitive 20 crepeRuntimeState
      (.extCall "host" 1 2 3 4)).map Prod.fst =
      some (.finalFfi "halt") := by
  decide +kernel

theorem crepe_runtime_tick_timeout :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2 { crepeRuntimeState with clock := 0 }
      .tick).map Prod.fst =
      some (.timeout : CrepRuntimeResult Nat String) := by
  decide +kernel

theorem crepe_runtime_memory_domain_error :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2
      { crepeRuntimeState with memaddrs := fun _ => false }
      (.store (.const 10) (.const 7))).map Prod.fst =
      some (.error : CrepRuntimeResult Nat String) := by
  decide +kernel

def crepeRuntimeCallState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    functions :=
      [{ name := "inc"
         params := [0]
         body := .return [.op .add [.var 0, .const 1]]
         returnShape := .one }] }

theorem crepe_runtime_call_result :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeCallState
      (.call (some ([5], none)) "inc" [.const 41])).map
        (fun result => (result.1, result.2.locals 5)) =
      some (.normal, some 42) := by
  decide +kernel

def crepeCallFullState : CrepState (RiscV.Word 64) :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepeCallFullPrimitive : CrepPrimitiveHandler (RiscV.Word 64) :=
  fun _ _ => none

def crepeCallFullFfi : CrepFfiHandler (RiscV.Word 64) :=
  noCrepFfi _

def crepeCallFullSharedMem : CrepSharedMemHandler (RiscV.Word 64) :=
  defaultCrepSharedMemHandler

def crepeCallFullValues :
    Option (List (RiscV.Word 64)) :=
  do
    let (_, main) ← lookupCompiledFunction "main" crepCallFunctions
    let result ← evalCrepFullProg crepCallFunctions
      crepeCallFullPrimitive crepeCallFullFfi crepeCallFullSharedMem
      0 (BitVec.ofNat 64 100) 30 crepeCallFullState main
    pure (match result with
      | .returned _ values => values
      | .normal _ => []
      | .raised _ _ | .broke _ _ | .continued _ _ => [])

#guard
    crepeCallFullValues = some [BitVec.ofNat 64 41]

#guard
    crepeCallFullValues =
      (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
        pipelineCallSourceMain).map (fun result => result.2)

end Flapjack
