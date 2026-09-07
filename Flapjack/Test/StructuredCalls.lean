import Flapjack.Test.StructuredValues

namespace Flapjack

def structuredCallTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

def structuredNoFfi : PanValueFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

def flatCallTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

def flatNoFfi : PanFlatFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

example :
    (evalPanFlatProgWithCallsAndFfi (α := Nat) [] flatCallTestFunctions flatNoFfi
      0 100 1 20 (fun _ => none) (fun _ => none) (fun _ => true) (fun _ => none)
      (.call (some (some (.local, "result"), none)) "id" [.const 7])).map
      (fun result => match result with
        | .normal locals _ _ => locals "result"
        | _ => none) = some (some (.word 7)) := by
  simp [evalPanFlatProgWithCallsAndFfi,
    evalPanFlatProgWithPrimitiveAndFfi, evalPanFlatProgFuelWithPrimitiveAndFfi,
    evalPanFlatCallWithPrimitiveAndFfi, evalPanFlatExps,
    evalPanFlatExp, evalPanFlatExp.evalPanFlatExps, flatCallTestFunctions,
    bindPanValueParameters, assignPanValueCallResult,
    updatePanValueMap, lookupPanFunction]

def flatFailFunctions : List (FunName × List VarName × Prog Nat) :=
  [("fail", [], .raise "E" (.const 9))]

example :
    (evalPanFlatProgWithCallsAndFfi (α := Nat) [] flatFailFunctions flatNoFfi
      0 100 1 20 (fun _ => none) (fun _ => none) (fun _ => true) (fun _ => none)
      (.call (some (none, some ("E", "caught",
        .return (.var .local "caught")))) "fail" [])).map
      (fun result => match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some 9) := by
  simp [evalPanFlatProgWithCallsAndFfi,
    evalPanFlatProgWithPrimitiveAndFfi, evalPanFlatProgFuelWithPrimitiveAndFfi,
    evalPanFlatCallWithPrimitiveAndFfi, evalPanFlatExp, evalPanFlatExps,
    evalPanFlatExp.evalPanFlatExps, flatFailFunctions, 
    bindPanValueParameters, updatePanValueMap, lookupPanFunction]

example :
    (evalPanFlatProgWithCallsAndFfi (α := Nat) [] flatCallTestFunctions flatNoFfi
      0 100 1 20 (fun name => if name == "result" then some (.word 99) else none)
      (fun _ => none) (fun _ => true) (fun _ => none)
      (.decCall "result" .one "id" [.const 7]
        (.return (.var .local "result")))).map
      (fun result => match result with
        | .returned locals _ _ [PanValue.word value] => (locals "result", value)
        | _ => (none, 0)) = some (some (.word 99), 7) := by
  simp [evalPanFlatProgWithCallsAndFfi,
    evalPanFlatProgWithPrimitiveAndFfi, evalPanFlatProgFuelWithPrimitiveAndFfi,
    evalPanFlatCallWithPrimitiveAndFfi, evalPanFlatExp, evalPanFlatExps,
    evalPanFlatExp.evalPanFlatExps, flatCallTestFunctions, 
    bindPanValueParameters, assignPanValueCallResult, updatePanValueMap,
    restorePanFlatControlLocal, restorePanValueLocal,
    lookupPanFunction, panValueShape, panShapeMatches]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) []
      structuredCallTestFunctions structuredNoFfi 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.call (some (some (.local, "result"), none)) "id" [.const 7])).map
      (fun result => match result with
        | .normal locals _ _ => locals "result"
        | _ => none) = some (some (.word 7)) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueCallWithCallsAndFfi,
    evalPanValueExp, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    structuredCallTestFunctions, bindPanValueParameters,
    assignPanValueCallResult, updatePanValueMap, lookupPanFunction]

example :
    (evalPanValueProgWithCallsAndFfi (α := Nat) []
      [("fail", [], .raise "E" (.const 9))] structuredNoFfi 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.call (some (none, some ("E", "caught",
        .return (.var .local "caught")))) "fail" [])).map
      (fun result => match result with
        | .returned _ _ _ [PanValue.word value] => some value
        | _ => none) = some (some 9) := by
  simp [evalPanValueProgWithCallsAndFfi, evalPanValueCallWithCallsAndFfi,
    evalPanValueExp, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    bindPanValueParameters, assignPanValueCallResult,
    updatePanValueMap, lookupPanFunction]

end Flapjack
