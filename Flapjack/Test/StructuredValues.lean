import Flapjack.Test.Loops

namespace Flapjack

open RiscV

def structuredValueTestContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def flatPairDomain : PanMemoryDomain Nat :=
  fun address => address == 10 || address == 11

def flatPairMemory : PanFlatMemory Nat :=
  fun address => if address == 10 then some 3
    else if address == 11 then some 5 else none

example : panValueWords (.rStruct [.word (3 : Nat), .word 5]) = [3, 5] := by
  rfl

example :
    panFlatLoad structuredValueTestContext flatPairDomain flatPairMemory 1 10
      (.comb [.one, .one]) =
      some (.rStruct [.word 3, .word 5]) := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    flatPairDomain, flatPairMemory,
    panFlatReadWord, panOffset, panStructContextFuel, panShapeFieldsFuel,
    panShapeFuel, panShapeFuel.panShapeListFuel, shapeSizeWithContext,
    isWfShape, isWfShape.isWfShapeList, structuredValueTestContext]

example :
    panFlatLoad structuredValueTestContext flatPairDomain flatPairMemory 1 10
      (.named "Pair") =
      some (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) := by
  simp [panFlatLoad, panFlatLoadFuel, 
    panFlatLoadFuel.panFlatLoadFieldsFuel, flatPairDomain, flatPairMemory,
    panFlatReadWord, panOffset, panStructContextFuel, panShapeFieldsFuel,
    panShapeFuel, shapeSizeWithContext,
    isWfShape, lookupInfo, structuredValueTestContext]

example :
    panFlatLoad structuredValueTestContext
      (fun address => address == 10) flatPairMemory 1 10
      (.comb [.one, .one]) = none := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    flatPairMemory, panFlatReadWord,
    panOffset, panShapeFuel,
    panShapeFuel.panShapeListFuel, shapeSizeWithContext, isWfShape,
    isWfShape.isWfShapeList]

example :
    (panFlatStore flatPairDomain (fun _ => none) 1 10
      (.rStruct [.word (3 : Nat), .word 5])).bind
      (fun memory => panFlatLoad structuredValueTestContext flatPairDomain memory
        1 10 (.comb [.one, .one])) =
      some (.rStruct [.word 3, .word 5]) := by
  simp [panFlatStore, panFlatStoreWords, panFlatStoreWord, panValueWords,
    panValueFuel, panValueFuel.panValueListFuel, panValueWordsFuel,
    panValueWordsFuel.panValueWordsListFuel,
    panOffset, panFlatLoad, panFlatLoadFuel,
    panFlatLoadFuel.panFlatLoadListFuel, 
    flatPairDomain, panFlatReadWord, 
    panShapeFuel, panShapeFuel.panShapeListFuel, shapeSizeWithContext,
    isWfShape, isWfShape.isWfShapeList, updatePanValueMap]

example :
    (evalPanFlatProg (α := Nat) structuredValueTestContext 0 100 1
      (fun _ => none) (fun _ => none) flatPairDomain (fun _ => none)
      (.seq (.store (.const 10)
        (.rStruct [.const 3, .const 5]))
        (.return (.load (.comb [.one, .one]) (.const 10))))).map
      (fun result => result.2.2.2) =
      some [PanValue.rStruct [.word 3, .word 5]] := by
  simp [evalPanFlatProg, evalPanFlatProgWithPrimitive, evalPanFlatExp,
    evalPanFlatExp.evalPanFlatExps, panFlatStore,
    panFlatStoreWords, panFlatStoreWord, panValueWords, panValueWordsFuel,
    panValueFuel, panValueFuel.panValueListFuel, panValueWordsFuel,
    panValueWordsFuel.panValueWordsListFuel, panOffset, panFlatLoad,
    panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    flatPairDomain, panFlatReadWord,
    panShapeFuel,
    panShapeFuel.panShapeListFuel, shapeSizeWithContext, isWfShape,
    isWfShape.isWfShapeList, updatePanValueMap]

example :
    evalPanValueExp (α := Nat) structuredValueTestContext
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.nField "right"
        (.nStruct "Pair" [("left", .const 3), ("right", .const 5)])) =
      some (.word 5) := by
  simp [evalPanValueExp, 
    evalPanValueExp.evalPanValueFields, structuredValueTestContext,
    panValueFieldsHaveShapes, panValueShape, panShapeMatches,
    lookupInfo, lookupPanValueField]

example :
    evalPanValueExp (α := Nat) structuredValueTestContext
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.nStruct "Pair" [("left", .const 3),
        ("right", .rStruct [.const 4, .const 5])]) = none := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueFields,
    evalPanValueExp.evalPanValueExps, structuredValueTestContext,
    panValueFieldsHaveShapes, panValueShape, panShapeMatches,
    lookupInfo]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun name => if name == "g" then some (.word 11) else none)
      (fun _ => none) 0 100 8 (.var .global "g") = some (.word 11) := by
  simp [evalPanValueExp]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none)
      (fun address => if address == 4 then
        some (.rStruct [.word 1, .word 2]) else none)
      0 100 8 (.load (.comb [.one, .one]) (.const 4)) =
      some (.rStruct [.word 1, .word 2]) := by
  simp [evalPanValueExp, isWfShape, isWfShape.isWfShapeList,
    panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches]

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none)
      (fun address => if address == 4 then some (.word 2) else none)
      0 100 8 (.load (.named "Unknown") (.const 4)) = none := by
  simp [evalPanValueExp, isWfShape, panValueShape, panShapeMatches]

example :
    (evalPanValueProg (α := Nat) [] 0 100 8
      (fun _ => none) (fun _ => none) (fun _ => none)
      (.seq (.assign .local "x" (.const 9))
        (.return (.var .local "x")))).map
      (fun result => result.2.2.2) = some [PanValue.word 9] := by
  simp [evalPanValueProg, evalPanValueProgWithPrimitive,
    evalPanValueExp, updatePanValueMap]

def flatWordDomain : PanMemoryDomain Nat := fun address => address == 20

def flatWordMemory : PanFlatMemory Nat :=
  fun address => if address == 20 then some 99 else none

example :
    evalPanFlatExp (α := Nat) []
      (fun _ => none) (fun _ => none) flatWordDomain flatWordMemory 0 100 1
      (.load32 (.const 20)) = some (.word 99) := by
  simp [evalPanFlatExp, flatWordDomain, flatWordMemory, panFlatReadWord]

example :
    evalPanFlatExp (α := Nat) []
      (fun _ => none) (fun _ => none) flatWordDomain flatWordMemory 0 100 1
      (.loadByte (.const 20)) = some (.word 99) := by
  simp [evalPanFlatExp, flatWordDomain, flatWordMemory, panFlatReadWord]

end Flapjack
