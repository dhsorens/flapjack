import Flapjack.PanSteppedSemantics

namespace Flapjack

def steppedTestLocals : VarName → Option (PanValue Nat) := fun _ => none
def steppedTestGlobals : VarName → Option (PanValue Nat) := fun _ => none
def steppedTestMemory : Nat → Option (PanValue Nat) := fun _ => none

def steppedTestPrimitive : PanPrimitiveHandler Nat := fun _ _ => none
def steppedTestFfi : PanValueFfiHandler Nat := fun _ _ _ _ _ locals => some locals

def steppedReturnedValues : PanValueControlResult Nat → List Nat
  | .returned _ _ _ values => values.map (fun value => match value with
      | .word value => value
      | _ => 0)
  | _ => []

def steppedTestProgram : Prog Nat :=
  .seq
    (.assign .local "x" (.const 7))
    (.seq (.while (.const 0) .skip) (.return (.var .local "x")))

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    steppedTestLocals steppedTestGlobals steppedTestMemory steppedTestProgram).map Prod.snd =
    some 8

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    steppedTestLocals steppedTestGlobals steppedTestMemory steppedTestProgram).map
      (fun (result, _) => steppedReturnedValues result) =
    (evalPanValueProgWithPrimitiveCallsAndFfi steppedTestPrimitive steppedTestFfi [] []
      0 100 1 20 steppedTestLocals steppedTestGlobals steppedTestMemory
      steppedTestProgram).map steppedReturnedValues

def steppedTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

#guard
  (evalPanValueExpCounted [] steppedTestLocals steppedTestGlobals steppedTestMemory
    0 100 1 (.op .add [.const 1, .const 2])).map Prod.snd = some 3

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedTestFunctions
    0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call none "id" [.const 41])).map Prod.snd = some 4

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedTestFunctions
    0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call none "id" [.const 41])).map
      (fun (result, _) => steppedReturnedValues result) =
    (evalPanValueProgWithPrimitiveCallsAndFfi steppedTestPrimitive steppedTestFfi []
      steppedTestFunctions 0 100 1 20 steppedTestLocals steppedTestGlobals
      steppedTestMemory (.call none "id" [.const 41])).map steppedReturnedValues

def steppedTestInitial : PanValueProgramState Nat :=
  { structs := []
    globals := steppedTestGlobals
    functions := []
    returnShapes := []
    exceptions := []
    memory := steppedTestMemory
    baseAddress := 0
    topAddress := 100
    bytesInWord := 8 }

#guard
  (evalPanValueSteppedProgram steppedTestInitial steppedTestPrimitive steppedTestFfi 20
    [.function
      { name := "id", inline := false, exported := true,
        params := [("x", .one)], body := .return (.var .local "x"),
        returnShape := .one }]
    "id" [.const 41]).map Prod.snd = some 4

end Flapjack
