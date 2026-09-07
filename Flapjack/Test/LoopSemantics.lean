import Flapjack.Test.Compile

namespace Flapjack

open RiscV
def emptyLoopState : LoopState Nat :=
  { locals := fun _ => none, globals := fun _ => none, memory := fun _ => none }

def loopDivisionState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 42 else if name = 2 then some 6 else none
    globals := fun _ => none, memory := fun _ => none }

example :
    (evalLoopProg 10 loopDivisionState
      (.seq (.arith (.div 3 1 2)) (.return [3]))).map loopResultValues =
      some [7] := by
  decide

example :
    (evalLoopProg 1 loopDivisionState (.arith (.div 3 1 2))).map
      (fun result => match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 7) := by
  decide

example :
    (evalLoopProg 1
      { loopDivisionState with locals := fun name =>
          if name = 1 then some 42 else if name = 2 then some 0 else none }
      (.arith (.div 3 1 2))).isNone = true := by
  decide

example :
    evalLoopExp emptyLoopState
      (.op .add [.const 6, .crepOp .mul [.const 5, .const 6]]) = some 36 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.op .sub [.const 9, .const 4]) = some 5 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.op .and [.const 13, .const 6]) = some 4 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.op .or [.const 8, .const 3]) = some 11 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.op .xor [.const 13, .const 6]) = some 11 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsl (.const 3) (.const 2)) = some 12 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsr (.const 13) (.const 2)) = some 3 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.cmp .lower (.const 3) (.const 5)) = some 1 := by
  decide

example :
    evalLoopExp emptyLoopState
      (.cmp .notLower (.const 5) (.const 3)) = some 1 := by
  decide

example : evalLoopCondition .less (3 : Nat) 5 = some true := by
  decide

example : evalLoopCondition .notLess (5 : Nat) 3 = some true := by
  decide

example : evalLoopCondition .test (5 : Nat) 2 = some true := by
  decide

example : evalLoopCondition .notTest (5 : Nat) 1 = some true := by
  decide

example : evalLoopExp emptyLoopState (.cmp .less (.const (3 : Nat)) (.const 5)) =
    some 1 := by
  decide

example : evalLoopExp emptyLoopState (.cmp .test (.const (5 : Nat)) (.const 2)) =
    some 1 := by
  decide

example : evalLoopExp emptyLoopState (.cmp .notTest (.const (5 : Nat)) (.const 1)) =
    some 1 := by
  decide

example :
    (evalLoopProg 10 emptyLoopState
      (.seq (.assign 0 (.const 42)) (.return [0]))).map loopResultValues =
      some [42] := by
  decide

example :
    evalLoopProg 1 emptyLoopState (.break 7) =
      some (.broke emptyLoopState 7) := by
  exact evalLoopProg_break emptyLoopState 7

example :
    evalLoopProg 1 emptyLoopState (.continue 8) =
      some (.continued emptyLoopState 8) := by
  exact evalLoopProg_continue emptyLoopState 8

example :
    evalLoopProg 1 emptyLoopState (.tick) =
      some (.normal emptyLoopState) := by
  exact evalLoopProg_tick emptyLoopState

example :
    (evalLoopProg 10 emptyLoopState
      (.loop [] (.break 0) [])).map loopResultValues = some [] := by
  decide

example :
    (evalLoopProg 12 emptyLoopState
      (loopCompileProg loopContext [] (.return [(.const (α := Nat) 7)]))).map
        loopResultValues = some [7] := by
  exact evalLoopCompile_return_const loopContext [] emptyLoopState 7

example :
    Option.map loopResultValues
      (evalLoopProg 20 emptyLoopState
      (loopCompileProg loopContext []
          (.return [(.crepOp .mul [.const (α := Nat) 6, .const 7])]))) =
      some [42] := by
  decide +kernel

example :
    evalPanCondition (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.cmp .equal (.var .local "x") (.const 7)) = some true := by
  decide

example :
    evalPanProg (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.ite (.cmp .equal (.var .local "x") (.const 7))
          (.return (.const 1)) (.return (.const 0))) = some [1] := by
  decide

example :
    (evalPanMemProgFuel 4
      (fun _ => none)
      (fun address => if address == 4 then some 7 else none)
      (.ite (.cmp .equal (.load .one (.const 4)) (.const 7))
        (.return (.const 1)) (.return (.const 0)))).map
      (fun result => result.2.2) = some [1] := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .sub [.const 9, .const 4]) = some 5 := by
  decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .and [.const 5, .const 3]) = some 1 := by
  decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .xor [.const 5, .const 3]) = some 6 := by
  decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.cmp .lower (.const 3) (.const 5)) = some 1 := by
  decide

example :
    evalPanCondition (α := Nat) (fun _ => none)
      (.cmp .notLower (.const 5) (.const 3)) = some true := by
  decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.shift .lsl (.const 3) (.const 2)) = some 12 := by
  decide

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.rField 1 (.rStruct [.const 3, .const 5])) = some (.word 5) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]

example :
    (evalLoopProg 8 emptyLoopState
      (.seq (.assign 0 (.const 42)) .tick)).map
        (fun result => (loopResultState result).memory) =
      (evalLoopProg 8 emptyLoopState
        (.seq (.assign 0 (.const 42)) .tick)).map
          (fun _ => emptyLoopState.memory) := by
  apply evalLoopProg_memory_projection
  rfl

example :
    (evalLoopProg 10 emptyLoopState
      (.loop [] (.seq .tick (.break 0)) [])).map
        (fun result => (loopResultState result).memory) =
      (evalLoopProg 10 emptyLoopState
        (.loop [] (.seq .tick (.break 0)) [])).map
          (fun _ => emptyLoopState.memory) := by
  apply evalLoopProg_memory_projection
  rfl

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 emptyLoopState
      (.seq (.assign 0 (.const 42)) (.return [0])) = some result) :
    (loopResultState result).locals 1 = emptyLoopState.locals 1 := by
  apply evalLoopProg_result_local 1 20 emptyLoopState
    (.seq (.assign 0 (.const 42)) (.return [0])) result
  · rfl
  · exact heval

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 emptyLoopState
      (.loop [] (.seq (.assign 0 (.const 42)) (.break 0)) []) = some result) :
    (loopResultState result).locals 1 = emptyLoopState.locals 1 := by
  apply evalLoopProg_result_local 1 20 emptyLoopState
    (.loop [] (.seq (.assign 0 (.const 42)) (.break 0)) []) result
  · rfl
  · exact heval

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 emptyLoopState
      (.seq .tick (.return [])) = some result) :
    loopResultState result = emptyLoopState := by
  apply evalLoopProg_result_state 20 emptyLoopState
    (.seq .tick (.return []))
  · intro name
    rfl
  · rfl
  · rfl
  · exact heval

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 emptyLoopState
      (.loop [] (.seq .tick (.break 0)) []) = some result) :
    loopResultState result = emptyLoopState := by
  apply evalLoopProg_result_state 20 emptyLoopState
    (.loop [] (.seq .tick (.break 0)) [])
  · intro name
    rfl
  · rfl
  · rfl
  · exact heval

def populatedLoopState : LoopState Nat :=
  { locals := fun name => if name == 7 then some 42 else none
    globals := fun address => if address == 3 then some 9 else none
    memory := fun address => if address == 11 then some 13 else none }

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 populatedLoopState (.continue 4) = some result) :
    loopResultState result = populatedLoopState := by
  apply evalLoopProg_result_state 20 populatedLoopState (.continue 4)
  · intro name
    rfl
  · rfl
  · rfl
  · exact heval

example (result : LoopResult Nat)
    (heval : evalLoopProg 20 populatedLoopState (.raise 7) = some result) :
    loopResultState result = populatedLoopState := by
  apply evalLoopProg_result_state 20 populatedLoopState (.raise 7)
  · intro name
    rfl
  · rfl
  · rfl
  · exact heval


end Flapjack
