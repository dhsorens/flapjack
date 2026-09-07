import Flapjack.Semantics
import Flapjack.PanMemory

/-!
Small correctness bridges for the CakeML-faithful flat source memory model.

The first bridge deliberately targets the structured store/load fragment.  It
connects the existing `pan_to_crep` lowering and Crepe memory evaluator to
the flat Pancake evaluator, whose memory cells contain words rather than
whole structured values.
-/

namespace Flapjack

def flatCorrectnessContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

def flatCorrectnessStructs : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def flatCorrectnessDomain : PanMemoryDomain Nat :=
  fun address => address == 10 || address == 11

def flatCorrectnessMemory : PanFlatMemory Nat :=
  fun address => if address == 10 then some 3
    else if address == 11 then some 5 else none

def flatCorrectnessProgram (left right : Nat) : Prog Nat :=
  .seq (.store (.const 10) (.rStruct [.const left, .const right]))
    (.return (.load (.comb [.one, .one]) (.const 10)))

theorem compile_flat_store_load_pair_correct (left right : Nat) :
    evalCrepMemResult (fun _ => none) (fun _ => none)
        (compileProg flatCorrectnessContext (flatCorrectnessProgram left right)) =
      (evalPanFlatProg flatCorrectnessStructs 0 100 1
        (fun _ => none) (fun _ => none) flatCorrectnessDomain
        (fun _ => none) (flatCorrectnessProgram left right)).map
        (fun result => result.2.2.2.flatMap panValueWords) := by
  have compiled_shape :
      compileProg flatCorrectnessContext (flatCorrectnessProgram left right) =
        .seq
          (.dec 1 (.const 10)
            (.dec 2 (.const left)
              (.dec 3 (.const right)
                (.seq (.store (.var 1) (.var 2))
                  (.seq (.store (.op .add [.var 1, .const 1]) (.var 3))
                    .skip)))))
      (.return [.load (.const 10),
            .load (.op .add [.const 10, .const 1])]) := by
    simp [flatCorrectnessProgram, flatCorrectnessContext, compileProg,
      compileExp, compileExp.compileExpList, Shape.shapeSize, freshNames,
      nestedDecs, stores, crepNestedSeq, loadShape, List.range, List.range.loop,
      ]
  rw [compiled_shape]
  simp [flatCorrectnessProgram, flatCorrectnessStructs,
    flatCorrectnessDomain, 
    
    
    evalCrepMemResult, evalCrepMemProg, evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, updateMemory, updateCrepLocal,
    evalPanFlatProg, evalPanFlatProgWithPrimitive, evalPanFlatExp,
    evalPanFlatExp.evalPanFlatExps, panFlatStore,
    panFlatStoreWords, panFlatStoreWord, panValueWords, panValueWordsFuel,
    panValueFuel, panValueFuel.panValueListFuel,
    panValueWordsFuel.panValueWordsListFuel, panOffset, panFlatLoad,
    panFlatLoadFuel, panFlatLoadFuel.panFlatLoadListFuel,
    panFlatReadWord,
    panStructContextFuel, panShapeFieldsFuel, panShapeFuel,
    panShapeFuel.panShapeListFuel, shapeSizeWithContext, isWfShape,
    isWfShape.isWfShapeList, updatePanValueMap]

end Flapjack
