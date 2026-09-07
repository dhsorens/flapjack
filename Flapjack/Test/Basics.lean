import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Pipeline
import Flapjack.Static
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.PanValues
import Flapjack.PanMemory
import Flapjack.RiscV.Model
import Flapjack.RiscV.PanSemantics
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.LoopSemantics
import Flapjack.Word
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Calls
import Flapjack.RiscV.Link
import Flapjack.Correctness
import Flapjack.WordSemantics

namespace Flapjack

open RiscV

example : RiscV.Architecture.width .rv32i = 32 := by
  rfl

example :
    (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
      (fun name => if name == "result" then
        some (.rStruct [.word (BitVec.ofNat 64 0), .word (BitVec.ofNat 64 0)])
        else none)
      (fun _ => none) (fun _ => none) RiscV.panPrimitiveHandler
      (.primitive "result" .addCarry
        [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
          .const (BitVec.ofNat 64 0)])).map
      (fun result => result.1 "result") =
      some (some (.rStruct [
        .word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 0)])) := by
  simp [evalPanValueProgWithPrimitive, evalPanValueExp,
    evalPanValueExp.evalPanValueExps, evalPanValueExps,
    RiscV.panPrimitiveHandler, RiscV.addCarryWords,
    updatePanValueMap, panValueShape, panShapeMatches,
    panShapeMatches.panShapeListMatches]

example : RiscV.accessAligned .read (0 : RiscV.Word 32) 4 = none := by
  native_decide

example : RiscV.writeRegister (RiscV.zeroState 32) 0 (7 : RiscV.Word 32) =
    RiscV.zeroState 32 := by
  simp [RiscV.writeRegister]

example (state : RiscV.State 32) (source : Fin 32) (immediate : RiscV.Word 32) :
    (RiscV.execute state (.addi 0 source immediate)).pc = state.pc + 4 := by
  simp [RiscV.execute, RiscV.nextPc, RiscV.writeRegister]

def sampleShape : Shape := .comb [.one, .comb [.one, .one]]

example : Shape.shapeSize sampleShape = 3 := by
  simp [sampleShape, Shape.shapeSize]

example : nestedSeq ([] : List (Prog Nat)) = .skip := by
  rfl

example :
    expLocalVars (.op .add [.var .local "x", .var .global "g", .const 1]) = ["x"] := by
  native_decide

example :
    expGlobalVars (Exp.nStruct (α := Nat) "Pair"
      [("left", .var .local "x"), ("right", .var .global "g")]) = ["g"] := by
  native_decide

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

example : isWfShape pairContext (.named "Pair") = true := by
  native_decide

example : isWfShape pairContext (.comb [.one, .named "Pair"]) = true := by
  native_decide

example : isWfShape pairContext (.named "Missing") = false := by
  native_decide

example : isWfContext pairContext = true := by
  native_decide

example : shapeSizeWithContext pairContext (.named "Pair") = 2 := by
  native_decide

def duplicateContext : StructContext :=
  [("Pair", { fields := [], size := 0 }), ("Pair", { fields := [], size := 0 })]

example : isWfContext duplicateContext = false := by
  native_decide

example : validateDecl pairContext (.decl .one "answer" (.const 42)) = true := by
  native_decide

example : validateDecl pairContext (.decl (.named "Missing") "bad" (.const 0)) = false := by
  native_decide

def checkerContext : Context :=
  { locals := [("x", { shapedBased := .word .trusted }),
      ("pair", { shapedBased := .struct [.word .trusted, .word .trusted] })],
    globals := [("g", { shape := .one })], functions := [], exceptions := [],
    expectedReturn := none,
    structs := pairContext, scope := .topLevel, inLoop := false, reachable := .isReach,
    last := .otherLast, location := "" }

def checkerCallContext : Context :=
  { checkerContext with
    functions := [("f", { returnShape := .one, params := [] })] }

def checkerArgContext : Context :=
  { checkerContext with
    functions := [("f", { returnShape := .one, params := [("arg", .one)] })] }

def checkerPrimitiveContext : Context :=
  { checkerContext with
    locals := ("carry", { shapedBased := .struct [.word .notBased, .word .notBased] }) ::
      checkerContext.locals }

def checkerHandlerContext : Context :=
  { checkerCallContext with
    locals := ("exceptionValue", { shapedBased := .word .trusted }) ::
      checkerCallContext.locals,
    exceptions := [("E", .one)] }

example :
    checkExp (α := Nat) checkerContext (.var .local "x") =
      staticOk { shapedBased := .word .trusted } := by
  simp [checkExp, staticOk, checkerContext, pairContext, lookupInfo]

example :
    checkExp (α := Nat) checkerContext (Exp.rField 1 (Exp.var .local "pair")) =
      staticOk { shapedBased := .word .trusted } := by
  simp [checkExp, staticOk, staticBind, shapedBasedFieldAt,
    shapedBasedFieldAt.shapedBasedFieldAtList,
    checkerContext, pairContext, lookupInfo]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1, .const 2]) =
      staticOk { shapedBased := .word .notBased } := by
  simp [checkExp, checkExp.checkExps, staticOk, staticBind,
    shapedBasedIsWord, checkerContext, pairContext]

example :
    checkExp (α := Nat) checkerContext (Exp.op .add [.const 1]) =
      staticError (.general "invalid binary operator arity") := by
  simp [checkExp, checkExp.checkExps, staticOk, staticBind,
    checkerContext, pairContext]

example :
    checkProg (α := Nat) checkerContext (.return (.const 7)) =
      progOk .retLast true false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext]

example :
    checkProg (α := Nat) checkerContext
      (.assign .local "x" (.const 7)) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, checkerContext, lookupInfo,
    shapedBasedSameShape]

example :
    checkProg (α := Nat) checkerContext
      (.assign .local "missing" (.const 7)) =
      staticError (.scope "unknown local variable: missing") := by
  simp [checkProg, staticError, checkerContext, lookupInfo]

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext
      (.seq (.annot "location" "body")
        (.assign .local "missing" (.const 7)))) =
      some "unknown local variable: missing" := by
  native_decide

example :
    staticResultLocation (checkProg (α := Nat) checkerContext
      (.seq (.annot "location" "body") (.skip))) = some "AT body: " := by
  native_decide

example :
    staticResultErrorMessage (checkProg (α := Nat) checkerContext
      (.ite (.const 1) (.annot "location" "then")
        (.assign .local "missing" (.const 7)))) =
      some "unknown local variable: missing" := by
  native_decide

example :
    checkProg (α := Nat) checkerContext
      (.break) =
      staticError (.general "break used outside a loop") := by
  simp [checkProg, staticError, checkerContext]

example :
    checkProg (α := Nat) checkerContext
      (.dec "y" .one (.const 7) (.return (.var .local "y"))) =
      progOk .retLast true false "" := by
  simp [checkProg, checkExp, staticOk, staticBind, isWfShape,
    shapedBasedMatchesShape,
    shapedBasedFromShape, shapedBasedSameShape, checkerContext, pairContext,
    lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext (.call none "f" []) =
      progOk .tailLast true false "" := by
  simp [checkProg, checkProg.checkCallArgs,
    staticOk, staticBind,
    functionArgumentsMatch, checkerCallContext, checkerContext, lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext
      (.call (some (none, none)) "f" []) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkCallDestination,
    staticOk, staticBind,
    functionArgumentsMatch, checkerCallContext, checkerContext, lookupInfo]

example :
    checkProg (α := Nat) checkerCallContext
      (.call (some (some (.local, "x"), none)) "f" []) =
      progOk .otherLast false false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkCallDestination,
    staticOk, staticBind, functionArgumentsMatch, checkerCallContext, checkerContext,
    lookupInfo, shapedBasedMatchesShape, shapedBasedFromShape, shapedBasedSameShape]

example :
    checkProg (α := Nat) checkerCallContext (.call none "missing" []) =
      staticError (.scope "unknown function: missing") := by
  simp [checkProg, checkerCallContext, checkerContext, lookupInfo, staticError]

example :
    checkProg (α := Nat) checkerArgContext
      (.call none "f" [.const 1]) =
      progOk .tailLast true false "" := by
  simp [checkProg, checkProg.checkCallArgs, checkExp, staticOk, staticBind,
    functionArgumentsMatch, shapedBasedMatchesShape, shapedBasedFromShape,
    shapedBasedSameShape, checkerArgContext, checkerContext, lookupInfo]

example :
    staticResultOk (checkProg (α := Nat) checkerPrimitiveContext
      (.primitive "carry" .addCarry [.const 1, .const 2, .const 0])) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerHandlerContext
      (.call (some (none, some ("E", "exceptionValue", .skip))) "f" [])) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerCallContext
      (.decCall "result" .one "f" [] .skip)) =
      true := by
  native_decide

example :
    staticResultOk (checkProg (α := Nat) checkerContext
      (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4))) =
      true := by
  native_decide

example :
    checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1), ("right", .const 2)]) =
      staticOk { shapedBased := (.named "Pair"
        [("left", .word .notBased), ("right", .word .notBased)]) } := by
  simp [checkExp, checkExp.checkNamedExps, staticOk, staticBind,
    shapedBasedFieldsMatch, shapedBasedFromShape, shapedBasedSameShape,
    checkerContext, pairContext, lookupInfo]

example :
    (checkExp (α := Nat)
      checkerContext
      (Exp.nStruct "Pair" [("left", .const 1)])) =
      staticError (.shape "named struct fields do not match") := by
  simp [checkExp, checkExp.checkNamedExps, staticOk, staticBind,
    shapedBasedFieldsMatch, shapedBasedFromShape, shapedBasedSameShape,
    checkerContext, pairContext, lookupInfo]

end Flapjack
