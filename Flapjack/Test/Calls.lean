import Flapjack.Test.Pipeline

namespace Flapjack

open RiscV

def linkedCallCode : List (RiscV.Instruction 64) :=
  [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0,
    .addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
    .addi 10 2 1, .jalr 0 1 0]

example :
    RiscV.wordCallToRiscV (32 : RiscV.Word 64) [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0] := by
  exact RiscV.wordCallToRiscV_shape 32

example :
    (RiscV.executeCodeUntil 30 (0 : RiscV.Word 64) 16 linkedCallCode
      (RiscV.writeRegister (RiscV.zeroState 64) 6 41)).map
        (fun state => RiscV.readRegister state 4) = some 42 := by
  native_decide

example :
    RiscV.linkRiscVFunctions (0 : RiscV.Word 64)
      [(7, [2], some ([.addi 10 2 1, .jalr 0 1 0], [10]))] =
      some [(7, 0, [2], [.addi 10 2 1, .jalr 0 1 0], [10])] := by
  rfl

example :
    RiscV.wordCallToRiscVLabel
      [(7, (32 : RiscV.Word 64), [2], [], [10])] 7 [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 32, .jalr 1 31 0, .addi 4 10 0] := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.seq
        (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)
        (.return 0 [4])) =
      some ([.addi 2 6 0, .addi 30 30 (0 - BitVec.ofNat width (width / 8)),
        .storeWord 1 30, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 1 31 0, .addi 4 10 0, .loadWord 1 30,
        .addi 30 30 (BitVec.ofNat width (width / 8))], [4]) := by
  exact RiscV.wordFunctionToRiscVWithCalls_shape

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.shareInst .load 1 (.var 2)) : WordProg (RiscV.Word width)) =
      some ([.loadWord 1 2], []) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load32 5 (.var 6)) : WordProg (RiscV.Word width)) =
      some ([.load32 5 6], []) := by
  exact RiscV.wordFunctionToRiscVWithCalls_shareInst

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load16 5 (.var 6)) : WordProg (RiscV.Word width)) =
      some ([.loadHalf 5 6], []) := by
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordShareInstToInstructions, RiscV.wordInstToInstruction,
    RiscV.registerOfNat]

def halfwordRoundTripState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister (RiscV.zeroState 64) 2 16) 3
      (BitVec.ofNat 64 0xBEEF)

example :
    (RiscV.evalWordFunction halfwordRoundTripState
      (.seq (.inst (.mem .store16 3 2)) (.inst (.mem .load16 1 2)))).map
        (fun result => RiscV.readRegister result.1 1) =
      some (BitVec.ofNat 64 0xBEEF) := by
  native_decide

example :
    RiscV.wordFunctionToRiscVWithCalls (width := 8)
        ({ targets := [] } : RiscV.WordCallContext 8)
        ((.seq
          (.ite .equal 1 (.imm 7)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word 8)) =
      some ([.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2], [3]) := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscVWithCalls
        ({ targets := [] } : RiscV.WordCallContext width)
        ((.shareInst .load32 5
          (.op .add [.var 6, .const (4 : RiscV.Word width)])) :
          WordProg (RiscV.Word width)) =
      some ([.addi 31 6 4, .load32 5 31], []) := by
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordShareInstToInstructions, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.wordInstToInstruction,
    RiscV.registerOfNat]

def selectedLinkedCallCode : List (RiscV.Instruction 64) :=
  match RiscV.wordFunctionToRiscVWithCalls
      { targets := [(7, (32 : RiscV.Word 64), [2], [10])] }
      (.seq
        (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)
        (.return 0 [4])) with
  | some (code, _) => code ++
      [.addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
        .addi 10 2 1, .jalr 0 1 0]
  | none => []

example :
    (RiscV.executeCodeUntil 40 (0 : RiscV.Word 64) 24 selectedLinkedCallCode
      (RiscV.writeRegister (RiscV.zeroState 64) 6 41)).map
        (fun state => RiscV.readRegister state 4) = some 42 := by
  native_decide

def linkedWordCallFunctions :
    List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
  [(7, [2], .return 0 [2]),
   (8, [6], .seq
      (.call (some ([4], ([], []), .skip, 0, 0)) (some 7) [6] none)
      (.return 0 [4]))]

example :
    RiscV.linkWordFunctions (0 : RiscV.Word 64) linkedWordCallFunctions =
      some [
        (7, 0, [2], [.jalr 0 1 0], [2]),
        (8, 4, [6],
          [.addi 2 6 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
            .storeWord 1 30, .addi 31 0 0, .jalr 1 31 0,
            .addi 4 2 0, .loadWord 1 30, .addi 30 30 (BitVec.ofNat 64 8),
            .jalr 0 1 0], [4])] := by
  simp [RiscV.linkWordFunctions, 
    RiscV.wordFunctionTargetSignaturesWithCalls,
    RiscV.wordFunctionTargetSignaturesAux,
    RiscV.wordFunctionReturnNamesWithCalls, 
    RiscV.compileLinkedWordFunction, 
    RiscV.wordFunctionToRiscVWithCallsAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndLoopsAux,
    RiscV.wordControlInstructions, 
    
    RiscV.wordFunctionToRiscVWithCalls, RiscV.wordCallToRiscVWithStack,
    
    RiscV.wordRegisterMoves, RiscV.lookupWordCallTarget,
    RiscV.registerOfNat, RiscV.linkRiscVFunctions,
    RiscV.linkRiscVFunctionsAt, linkedWordCallFunctions]

def linkedWordLoopFunctions :
    List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
  [(7, [], (.loop [] (.break 0) []))]

example :
    RiscV.linkWordFunctions (0 : RiscV.Word 64) linkedWordLoopFunctions =
      some [(7, 0, [],
        [.jal 0 (BitVec.ofNat 64 8),
         .jal 0 (0 - BitVec.ofNat 64 4), .jalr 0 1 0], [])] := by
  simp [RiscV.linkWordFunctions, 
    RiscV.wordFunctionTargetSignaturesWithCalls,
    RiscV.wordFunctionTargetSignaturesAux,
    RiscV.wordFunctionReturnNamesWithCalls, 
    RiscV.compileLinkedWordFunction, 
    RiscV.wordFunctionToRiscVWithCallsAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndLoopsAux,
    RiscV.wordControlInstructions, RiscV.resolveWordLoopBody,
    RiscV.resolveWordLoopBodyAux, 
    
    
    RiscV.linkRiscVFunctions,
    RiscV.linkRiscVFunctionsAt, linkedWordLoopFunctions]

def linkedWordCallImage : List (RiscV.Instruction 64) :=
  [.jalr 0 1 0, .addi 2 6 0,
    .addi 30 30 (0 - BitVec.ofNat 64 8), .storeWord 1 30,
    .addi 31 0 0, .jalr 1 31 0, .addi 4 2 0,
    .loadWord 1 30, .addi 30 30 (BitVec.ofNat 64 8), .jalr 0 1 0]

example :
    RiscV.executeFunctionAt 80 (0 : RiscV.Word 64) 4 36 [6]
      linkedWordCallImage [4] [41] (RiscV.zeroState 64) = some [41] := by
  native_decide

example :
    (RiscV.evalWordFunctionWithCalls
      [(7, [2], (.return 0 [2] : WordProg (RiscV.Word 64)))] 10
      (RiscV.writeRegister (RiscV.zeroState 64) 2 9)
      (.call (some ([3], ([], []), .skip, 0, 0)) (some 7) [2] none)).map (fun result =>
        result.1.registers 3) = some 9 := by
  native_decide

example :
    (RiscV.evalWordFunctionWithHandlers
      [(7, [2], (.seq (.assign 4 (.const (9 : RiscV.Word 64)))
        (.raise 4) : WordProg (RiscV.Word 64)))] 10
      (RiscV.zeroState 64)
      (.call (some ([3], ([], []), .skip, 0, 0)) (some 7) [2]
        (some (5, (.return 0 [5] : WordProg (RiscV.Word 64)), 0, 0)))).map
        (fun result =>
          match result with
          | .returned state values => (RiscV.readRegister state 5, values)
          | _ => (0, [])) = some (9, [9]) := by
  native_decide

def wordFfiTestState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister
      (RiscV.writeRegister
        (RiscV.writeRegister (RiscV.zeroState 64) 1 10) 2 1) 3 20) 4 2

def wordFfiTestHandler : FunName → RiscV.Word 64 → RiscV.Word 64 →
    RiscV.Word 64 → RiscV.Word 64 → RiscV.State 64 →
    Option (RiscV.State 64) := fun function configuration configurationLength array
    arrayLength state =>
  if function == "sum" then
    some (RiscV.writeRegister state 5
      (configuration + configurationLength + array + arrayLength))
  else none

example :
    (RiscV.evalWordFfi wordFfiTestHandler 10 wordFfiTestState
      (.ffi "sum" 1 2 3 4 ([], []))).map (fun result =>
        RiscV.readRegister result.1 5) = some 33 := by
  native_decide

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq (.assign 1 (.const (BitVec.ofNat width 100)))
          (.seq (.assign 2 (.const (BitVec.ofNat width 42)))
            (.seq (.store (.var 1) 2) (.seq (.inst (.mem .load 3 1))
              (.return 0 [3]))))) : WordProg (RiscV.Word width)) =
      some ([.addi 1 0 (BitVec.ofNat width 100),
        .addi 2 0 (BitVec.ofNat width 42), .storeWord 2 1, .loadWord 3 1], [3]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordStoreToInstructions,
    RiscV.wordShareInstToInstructions, RiscV.wordExpToInstruction,
    RiscV.wordInstToInstruction, RiscV.registerOfNat]

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 64) []
      [.addi 1 0 100, .addi 2 0 42, .storeWord 2 1, .loadWord 3 1]
      [3] [] (RiscV.zeroState 64) = some [42] := by
  exact RiscV.executeFunction_storeLoad

example [NeZero width] (state : RiscV.State width)
    (offset : RiscV.Word width) :
    (RiscV.execute state (.jal 1 offset)).pc = state.pc + offset := by
  exact RiscV.execute_jal_pc state 1 offset

example [NeZero width] (state : RiscV.State width) (source : Fin 32)
    (offset : RiscV.Word width) :
    (RiscV.execute state (.jalr 1 source offset)).pc =
      RiscV.jalrTarget (RiscV.readRegister state source) offset := by
  exact RiscV.execute_jalr_pc state 1 source offset

example :
    (RiscV.execute
      (RiscV.writeRegister (RiscV.zeroState 64) 2 (100 : RiscV.Word 64))
      (.jalr 1 2 3)).pc = 102 := by
  native_decide

example :
    RiscV.executeFunctionAt 20 (0 : RiscV.Word 64) 16 4 []
      [.addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
        .addi 10 0 42, .jalr 0 1 0] [10] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 4) = some [42] := by
  exact RiscV.executeFunctionAt_jalr_return

end Flapjack
