import Flapjack.Test.Calls

namespace Flapjack

open RiscV
def loopCallTestState : LoopState Nat :=
  { locals := fun name => if name = 1 then some 9 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopSharedMemoryTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 100 else if name = 2 then some 42 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 10 else if name = 2 then some 1
      else if name = 3 then some 20 else if name = 4 then some 2 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestHandler : FunName → Nat → Nat → Nat → Nat → LoopState Nat →
    Option (LoopState Nat) := fun function configuration configurationLength array arrayLength state =>
  if function == "sum" then
    let value := configuration + configurationLength + array + arrayLength
    some { state with locals := updateLoopLocal state.locals 5 value }
  else none

def loopNatAddCarryHandler : LoopPrimitiveHandler Nat
  | .addCarry, [left, right, carry] =>
      some [left + right + if carry == 0 then 0 else 1,
        if carry == 0 then 0 else 1]
  | _, _ => none

def loopAddCarryState : LoopState (RiscV.Word 64) :=
  { locals := fun name =>
      if name == 2 then some (BitVec.ofNat 64 1)
      else if name == 3 then some (BitVec.ofNat 64 2)
      else if name == 4 then some (BitVec.ofNat 64 0)
      else none
    globals := fun _ => none
    memory := fun _ => none }

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result => ((loopResultState result).locals 5,
          (loopResultState result).locals 6)) =
      some (some (BitVec.ofNat 64 3), some (BitVec.ofNat 64 0)) := by
  decide

def loopAddCarryMachineState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister
      (RiscV.writeRegister (RiscV.zeroState 64) 2 1) 3 2) 4 0

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result => ((loopResultState result).locals 5,
          (loopResultState result).locals 6)) =
      (RiscV.evalWordFunction loopAddCarryMachineState
        (loopToWordProg ({ vars := [] } : WordContext)
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result => (some (RiscV.readRegister result.1 5),
          some (RiscV.readRegister result.1 6))) := by
  decide +kernel

def addCarrySourceLocals : VarName → Option (PanValue (RiscV.Word 64)) :=
  fun name =>
    if name == "result" then
      some (.rStruct [.word 0, .word 0])
    else none

def addCarrySource : Prog (RiscV.Word 64) :=
  .primitive "result" .addCarry
    [.const 1, .const 2, .const 0]

def addCarryCompileContext : CompileContext (RiscV.Word 64) :=
  { vars := [("result", (.comb [.one, .one], [0, 1]))]
    functions := []
    exceptions := []
    maxVar := 1
    bytesInWord := 8 }

def addCarryLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := []
    functions := []
    maxVar := 1
    target := .rv64i }

def addCarryCompiledLoop : LoopProg (RiscV.Word 64) :=
  loopCompileProg addCarryLoopContext []
    (compileProg addCarryCompileContext addCarrySource)

example :
    (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
      addCarrySourceLocals (fun _ => none) (fun _ => none)
      RiscV.panPrimitiveHandler addCarrySource).map
        (fun result =>
          match result.1 "result" with
          | some (.rStruct [.word left, .word carry]) =>
              (some left, some carry)
          | _ => (none, none)) =
      (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 20
        { locals := fun _ => none, globals := fun _ => none,
          memory := fun _ => none } addCarryCompiledLoop).map
        (fun result => ((loopResultState result).locals 0,
          (loopResultState result).locals 1)) := by
  decide +kernel

example :
    (evalLoopProg 10 loopSharedMemoryTestState
      (.seq
        (.shMem .store 2 (.var 1))
        (.shMem .load 3 (.var 1)))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 42) := by
  decide

example :
    (evalLoopFfi loopFfiTestHandler 10 loopFfiTestState
      (.ffi "sum" 1 2 3 4 [])).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  decide +kernel

example :
    (evalLoopProgWithCallsAndFfi
      [(7, [1], (.return [1] : LoopProg Nat))]
      loopFfiTestHandler 20 loopFfiTestState
      (.seq
        (.call (some ([6], [])) (some 7) [1] none)
        (.ffi "sum" 1 2 3 4 []))).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  decide +kernel

/- The composed evaluator permits an FFI in a callee followed by a primitive
   in the caller.  The old call/FFI evaluator intentionally rejects the
   primitive at this boundary. -/
example :
    (evalLoopProgWithPrimitiveCallsAndFfi
      loopNatAddCarryHandler
      [(7, [1, 2, 3, 4],
          (.seq
            (.ffi "sum" 1 2 3 4 [])
            (.return [5]) : LoopProg Nat))]
      loopFfiTestHandler 40 loopFfiTestState
      (.seq
        (.call (some ([6], [])) (some 7) [1, 2, 3, 4] none)
        (.primitive [7, 8] .addCarry [6, 2, 3]))).map (fun result =>
      match result with
      | .normal state => (state.locals 7, state.locals 8)
      | _ => (none, none)) = some (some 35, some 1) := by
  decide +kernel

/- The same boundary also handles primitives in exception handlers. -/
example :
    (evalLoopProgWithPrimitiveCallsAndFfi
      loopNatAddCarryHandler
      [(9, [1], (.raise 1 : LoopProg Nat))]
      loopFfiTestHandler 30 loopFfiTestState
      (.call none (some 9) [1]
        (some (4,
          (.primitive [7, 8] .addCarry [1, 2, 3] : LoopProg Nat),
          .skip, [])))).map (fun result =>
      match result with
      | .normal state => (state.locals 7, state.locals 8)
      | _ => (none, none)) = some (some 12, some 1) := by
  decide +kernel

example :
    (evalLoopProgWithFunctions
      [(7, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 7) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  decide +kernel

example :
    (evalLoopProgWithFunctions
      [(8, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call none (some 8) [1] none)).map loopResultValues = some [9] := by
  decide +kernel

example :
    (evalLoopProgWithFunctions
      [(9, [1], (.raise 1 : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 9) [1]
        (some (4, .assign 3 (.var 4), .skip, [])))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  decide +kernel

example :
    (evalLoopProgWithFunctions
      [(10, [1],
          (.seq
            (.call (some ([2], [])) (some 11) [1] none)
            (.return [2]) : LoopProg Nat)),
       (11, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 10) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  decide +kernel

example :
    (evalLoopProgWithFunctions
      [(12, [1], (.return [1] : LoopProg Nat))] 20 loopCallTestState
      (.loop []
        (.seq
          (.call (some ([3], [])) (some 12) [1] none)
          (.break 0)) [])).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  decide +kernel

end Flapjack
