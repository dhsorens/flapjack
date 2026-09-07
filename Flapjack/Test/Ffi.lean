import Flapjack.RiscV.Link
import Flapjack.Ffi

namespace Flapjack

def identityFfiOracle : FfiOracle Unit :=
  fun _ state _ bytes => .returned state bytes

def identityFfiState : FfiState Unit :=
  { oracle := identityFfiOracle, state := (), ioEvents := [] }

example :
    match callFfi identityFfiState (.extCall "echo") [1, 2] [3, 4] with
    | .returned state bytes =>
        bytes = [3, 4] ∧ state.state = () ∧
          state.ioEvents =
            [{ name := .extCall "echo", configuration := [1, 2],
               bytes := [(3, 3), (4, 4)] }]
    | .final _ => False := by
  simp [callFfi, identityFfiState, identityFfiOracle]

def shortFfiOracle : FfiOracle Unit :=
  fun _ state _ _ => .returned state [7]

example :
    match callFfi { identityFfiState with oracle := shortFfiOracle }
      (.extCall "echo") [1, 2] [3, 4] with
    | .final event =>
        event =
          { name := .extCall "echo", configuration := [1, 2], bytes := [3, 4],
            outcome := .failed }
    | .returned _ _ => False := by
  simp [callFfi, identityFfiState, shortFfiOracle]

def finalFfiOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .diverged

example :
    match callFfi { identityFfiState with oracle := finalFfiOracle }
      (.extCall "echo") [1] [2] with
    | .final event =>
        event =
          { name := .extCall "echo", configuration := [1], bytes := [2],
            outcome := .diverged }
    | .returned _ _ => False := by
  simp [callFfi, finalFfiOracle]

example :
    match callFfi identityFfiState (.extCall "") [1] [2, 3] with
    | .returned state bytes => bytes = [2, 3] ∧ state.ioEvents = []
    | .final _ => False := by
  simp [callFfi, identityFfiState]

open RiscV

def ffiAbiState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 2 10) 3 1) 4 20) 5 2

def ffiAbiHost : WordFfiHost 64 :=
  fun service configuration configurationLength array arrayLength state =>
    if service = 7 then
      some (writeRegister state 6
        (configuration + configurationLength + array + arrayLength))
    else none

def ffiWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun function configuration configurationLength array arrayLength state =>
    if function == "sum" then
      some (writeRegister state 6
        (configuration + configurationLength + array + arrayLength))
    else none

example :
    ((wordFfiToRiscV { services := [("sum", 7)] } "sum" 2 3 4 5).bind
        (executeInstructionsWithFfi ffiAbiHost ffiAbiState)).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

example [NeZero width] :
    wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext width)
      (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6])) =
      some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 (BitVec.ofNat width 7), .ecall], [6]) := by
  simp [wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, wordFunctionToRiscVWithCalls,
    registerOfNat]

example :
    ((wordFunctionToRiscVWithCallsAndFfi
        ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext 64)
        (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6]))).bind
      (fun result => executeInstructionsWithFfi ffiAbiHost ffiAbiState result.1)).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

example :
    (evalWordFunctionWithCallsAndFfi [] ffiWordHandler 10 ffiAbiState
        (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6]))).map
        (fun result => result.2) = some [33] := by
  native_decide

example :
    evalWordFunctionWithCallsAndFfi [] ffiWordHandler 2 ffiAbiState
        (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6])) =
      some (writeRegister ffiAbiState 6 33, [33]) := by
  apply evalWordFunctionWithCallsAndFfi_seq_normal
    (middle := writeRegister ffiAbiState 6 33)
    (final := writeRegister ffiAbiState 6 33)
  · simp [evalWordFunctionWithCallsAndFfi, evalWordFfi, ffiWordHandler,
      ffiAbiState, writeRegister, readRegister, registerOfNat]
  · simp [evalWordFunctionWithCallsAndFfi, evalWordFunction,
      ffiAbiState, writeRegister, readRegister, registerOfNat]

example :
    evalWordFunctionWithCallsAndFfi [] ffiWordHandler 2 ffiAbiState
        (.seq (.return 0 [2]) (.ffi "sum" 2 3 4 5 ([], []))) =
      some (ffiAbiState, [10]) := by
  apply evalWordFunctionWithCallsAndFfi_seq_terminal
    (middle := ffiAbiState) (values := [10])
  · simp [evalWordFunctionWithCallsAndFfi, evalWordFunction,
      ffiAbiState, writeRegister, readRegister, registerOfNat]
  · simp

example :
    evalWordFunctionWithCallsAndFfi [] ffiWordHandler 2 ffiAbiState
        (.ite .equal 2 (.imm (10 : Word 64))
          (.ffi "sum" 2 3 4 5 ([], [])) .skip) =
      some (writeRegister ffiAbiState 6 33, []) := by
  apply evalWordFunctionWithCallsAndFfi_ite_true
  · native_decide
  · simp [evalWordFunctionWithCallsAndFfi, evalWordFfi, ffiWordHandler,
      ffiAbiState, writeRegister, readRegister, registerOfNat]

example :
    evalWordFunctionWithCallsAndFfi [] ffiWordHandler 2 ffiAbiState
        (.ite .notEqual 2 (.imm (10 : Word 64))
          .skip (.return 0 [2])) =
      some (ffiAbiState, [10]) := by
  apply evalWordFunctionWithCallsAndFfi_ite_false
  · native_decide
  · simp [evalWordFunctionWithCallsAndFfi, evalWordFunction,
      ffiAbiState, writeRegister, readRegister, registerOfNat]

example :
    wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext 64)
      (.loop [] (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.break 0)) []) =
      some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 7, .ecall, .jal 0 8, .jal 0 (0 - BitVec.ofNat 64 28)], []) := by
  native_decide

example :
    linkWordFunctionsWithFfi (0 : Word 64) [("sum", 7)]
      [(7, [], (.seq (.ffi "sum" 2 3 4 5 ([], [])) (.return 0 [6])))] =
      some [(7, 0, [],
        [.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
          .addi 14 0 7, .ecall, .jalr 0 1 0], [6])] := by
  simp [linkWordFunctionsWithFfi, wordFunctionTargetSignaturesWithCalls,
    wordFunctionTargetSignaturesAux, wordFunctionReturnNamesWithCalls,
    compileLinkedWordFunctionWithFfi,
    wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
    wordControlInstructions, 
    wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, wordFunctionToRiscVWithCalls,
    registerOfNat, linkRiscVFunctions,
    linkRiscVFunctionsAt]

def combinedFfiHost : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some (writeRegister state 2 (configuration + 1))
    else none

def combinedFfiFunctions : List (Nat × List Nat × WordProg (Word 64)) :=
  [(7, [2], .seq
    (.ffi "inc" 2 3 4 5 ([], []))
    (.return 0 [2]))]

example :
    (evalWordFunctionWithHandlersAndFfi combinedFfiFunctions combinedFfiHost 10
      (writeRegister (zeroState 64) 1 41)
      (.call (some ([6], ([], []), .skip, 0, 0)) (some 7) [1] none)).map
        (fun result => match result with
        | .normal state => readRegister state 6
        | _ => 0) = some 42 := by
  native_decide

def combinedHandlerFunctions : List (Nat × List Nat × WordProg (Word 64)) :=
  [(8, [3], .raise 3)]

example :
    (evalWordFunctionWithHandlersAndFfi combinedHandlerFunctions combinedFfiHost 10
      (writeRegister (zeroState 64) 3 9)
      (.call (some ([], ([], []), .skip, 0, 0)) (some 8) [3]
        (some (8, .assign 7 (.var 8), 0, 0)))).map
        (fun result => match result with
        | .normal state => readRegister state 7
        | _ => 0) = some 9 := by
  native_decide

example :
    (executeWithFfi ffiAbiHost
        (writeRegister
          (writeRegister
            (writeRegister
              (writeRegister (writeRegister (zeroState 64) 10 10) 11 1)
                12 20) 13 2) 14 7) .ecall).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

def ffiRunnerHost : WordFfiHost 64 :=
  fun service configuration configurationLength array arrayLength state =>
    if service = 7 then
      some { (writeRegister state 6
        (configuration + configurationLength + array + arrayLength)) with
        pc := state.pc + 4 }
    else none

example :
    executeFunctionAtWithFfi ffiRunnerHost 20 0 0 28 []
      [.addi 10 0 10, .addi 11 0 1, .addi 12 0 20, .addi 13 0 2,
        .addi 14 0 7, .ecall, .jalr 0 1 0]
      [6] [] (writeRegister (zeroState 64) 1 28) = some [33] := by
  native_decide

def loopFfiBreakProgram : WordProg (Word 64) :=
  .seq
    (.loop []
      (.seq (.ffi "inc" 2 3 4 5 ([], [])) (.break 0)) [])
    (.return 0 [2])

def loopFfiLinkedCode : Option (List (Instruction 64)) := do
  let (_, _, artifact) ← compileLinkedWordFunctionWithFfi
    ({ targets := [], services := [("inc", 7)] } : WordCallFfiContext 64)
    (0, [], loopFfiBreakProgram)
  let (code, _) ← artifact
  pure code

def loopFfiIncrementHost : WordFfiHost 64 :=
  fun service configuration _ _ _ state =>
    if service = 7 then
      some { (writeRegister state 2 (configuration + 1)) with
        pc := state.pc + 4 }
    else none

def loopFfiExecution : Option (List (Word 64)) := do
  let code ← loopFfiLinkedCode
  executeFunctionAtWithFfi loopFfiIncrementHost 100 0 0 100 [] code [2] []
    (writeRegister (writeRegister (zeroState 64) 1 100) 2 41)

example : loopFfiLinkedCode.isSome := by
  native_decide

example : loopFfiExecution = some [42] := by
  native_decide

end Flapjack
