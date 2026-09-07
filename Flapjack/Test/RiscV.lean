import Flapjack.Test.Compile
import Flapjack.RiscV.PanMemory

namespace Flapjack

open RiscV

def alignedMemoryState : RiscV.State 64 :=
  { (RiscV.zeroState 64) with
    registers := fun register =>
      if register = 1 then BitVec.ofNat 64 8 else 0 }

def misalignedMemoryState : RiscV.State 64 :=
  { (RiscV.zeroState 64) with
    registers := fun register =>
      if register = 1 then BitVec.ofNat 64 2 else 0 }

example :
    (RiscV.executeChecked alignedMemoryState (.loadHalf 2 1)).isSome := by
  decide

example :
    RiscV.executeChecked misalignedMemoryState (.load32 2 1) = none := by
  simp [RiscV.executeChecked, RiscV.executeTrap, RiscV.accessAligned,
    RiscV.aligned, RiscV.readRegister, misalignedMemoryState, RiscV.zeroState]

example :
    RiscV.accessAligned .read (BitVec.ofNat 64 2) 4 =
      some .loadFault := by
  decide

example :
    RiscV.executeTrap (RiscV.zeroState 64) .ecall =
      some .mModeEnvCall := by
  decide

example :
    RiscV.executeChecked (RiscV.zeroState 64) .ecall = none := by
  decide

def signedOrderState : RiscV.State 8 :=
  { (RiscV.zeroState 8) with
    registers := fun register =>
      if register = 1 then BitVec.ofNat 8 255
      else if register = 2 then BitVec.ofNat 8 1 else 0 }

example :
    RiscV.readRegister
      (RiscV.execute signedOrderState (.slt 3 1 2)) 3 =
      BitVec.ofNat 8 1 := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute signedOrderState (.slt 3 2 1)) 3 =
      BitVec.ofNat 8 0 := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute signedOrderState (.sltiu 3 1 (BitVec.ofNat 8 2))) 3 =
      BitVec.ofNat 8 0 := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute (RiscV.zeroState 64)
        (.lui 3 (BitVec.ofNat 64 1))) 3 =
      BitVec.ofNat 64 4096 := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute (RiscV.zeroState 64)
        (.auipc 3 (BitVec.ofNat 64 1))) 3 =
      BitVec.ofNat 64 4096 := by
  decide

def wordArithmeticState : RiscV.State 64 :=
  { (RiscV.zeroState 64) with
    registers := fun register =>
      if register = 1 then BitVec.ofNat 64 (2 ^ 31 - 1)
      else if register = 2 then 1 else 0 }

def wordShiftState : RiscV.State 64 :=
  { (RiscV.zeroState 64) with
    registers := fun register =>
      if register = 1 then BitVec.ofNat 64 (2 ^ 32 - 1)
      else if register = 2 then 4 else 0 }

example :
    RiscV.readRegister
      (RiscV.execute wordArithmeticState (.addW 3 1 2)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 31)) := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute wordArithmeticState (.addiW 3 1 1)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 31)) := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute wordArithmeticState (.mulW 3 1 2)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 31 - 1)) := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute wordShiftState (.sllW 3 2 2)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 6)) := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute wordShiftState (.srlW 3 1 2)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 28 - 1)) := by
  decide

example :
    RiscV.readRegister
      (RiscV.execute wordShiftState (.sraW 3 1 2)) 3 =
      BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 32 - 1)) := by
  decide

example :
    (RiscV.execute signedOrderState
      (.branchLt 1 2 (BitVec.ofNat 8 12))).pc =
      BitVec.ofNat 8 12 := by
  decide

example [NeZero width] :
    Flapjack.RiscV.compileWordAdd (width := width) 1 2 3 =
      some [.add 1 2 3] := by
  simp [Flapjack.RiscV.compileWordAdd, Flapjack.RiscV.wordProgToRiscV,
    Flapjack.RiscV.wordExpToInstruction, Flapjack.RiscV.registerOfNat]

example [NeZero width] (state : Flapjack.RiscV.State width)
    (zero : Flapjack.RiscV.readRegister state 0 = 0) :
    Flapjack.RiscV.evalWordProg state
        (.assign 1 (.const (7 : Flapjack.RiscV.Word width))) =
      some (Flapjack.RiscV.execute state (.addi 1 0 7)) := by
  simp [Flapjack.RiscV.evalWordProg, Flapjack.RiscV.wordExpToInstructions,
    Flapjack.RiscV.wordExpToInstruction, 
    Flapjack.RiscV.registerOfNat, Flapjack.RiscV.executeInstructions,
    Flapjack.RiscV.execute,
    Flapjack.RiscV.writeRegister, Flapjack.RiscV.nextPc, zero]

example [NeZero width] :
    Flapjack.RiscV.ZeroRegister (Flapjack.RiscV.zeroState width) := by
  exact Flapjack.RiscV.zeroState_zeroRegister

example [NeZero width] (state : Flapjack.RiscV.State width)
    (operator : BinOp) :
    Flapjack.RiscV.evalWordProg state
        (.assign 1 (.op operator [.var 2, .var 3])) =
      some (Flapjack.RiscV.execute state (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3)) := by
  exact Flapjack.RiscV.compileWordBinOp_sound state operator

example [NeZero width] :
    Flapjack.RiscV.wordFunctionToRiscV
        ((.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) :
          WordProg (Flapjack.RiscV.Word width)) =
      some ([.add 1 2 3], [1]) := by
  exact Flapjack.RiscV.wordFunctionToRiscV_return_add

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notEqual 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchEq 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notEqual 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchEq 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .equal 1 (.imm 7)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) =
      some [.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2] := by
  decide +kernel

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .test 1 (.imm 3)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) =
      some [.andi 31 1 3, .branchNe 31 0 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2] := by
  decide +kernel

example :
    RiscV.wordProgToRiscV (width := 8)
        ((.ite .equal 31 (.imm 7)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word 8)) = none := by
  decide +kernel

example :
    RiscV.wordFunctionToRiscV (width := 8)
        ((.seq
          (.ite .equal 1 (.imm 7)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word 8)) =
      some ([.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2], [3]) := by
  decide

example :
    (RiscV.executeCode 20 (0 : RiscV.Word 8)
      [.ori 31 0 7, .branchNe 1 31 12,
        .addi 3 0 1, .branchEq 0 0 8, .addi 3 0 2]
      (RiscV.writeRegister (RiscV.zeroState 8) 1 7)).map
        (fun state => RiscV.readRegister state 3) = some 1 := by
  decide

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .lower 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGeU 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLower 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLtU 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .test 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.and 1 1 2, .branchNe 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notTest 1 (.imm 0)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.and 1 1 0, .branchEq 1 0 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .less 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLess 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLt 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .less 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchGe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordProgToRiscV
        ((.ite .notLess 1 (.reg 2)
          (.assign 3 (.const 1)) (.assign 3 (.const 2))) :
          WordProg (RiscV.Word width)) =
      some [.branchLt 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] := by
  simp [RiscV.wordProgToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq
          (.ite .equal 1 (.reg 2)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.return 0 [3])) : WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2], [3]) := by
  simp [RiscV.wordFunctionToRiscV, 
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq (.return 0 [1]) (.assign 2 (.const 9))) :
          WordProg (RiscV.Word width)) =
      some ([], [1]) := by
  simp [RiscV.wordFunctionToRiscV, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordFunction state
        ((.seq (.return 0 [1]) (.assign 2 (.const 9))) :
          WordProg (RiscV.Word width)) =
      some (state, [RiscV.readRegister state 1]) := by
  simp [RiscV.evalWordFunction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.seq (.assign 3 (.const 1)) (.return 0 [3]))
          (.seq (.assign 3 (.const 2)) (.return 0 [3]))) :
          WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8),
        .addi 3 0 2], [3]) := by
  simp [RiscV.wordFunctionToRiscV, 
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordFunctionToRiscV
        ((.seq
          (.ite .equal 1 (.reg 2)
            (.assign 3 (.const 1)) (.assign 3 (.const 2)))
          (.seq .tick (.return 0 [3]))) : WordProg (RiscV.Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat width 8),
        .addi 3 0 2, .addi 0 0 0], [3]) := by
  simp [RiscV.wordFunctionToRiscV, 
    RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    (RiscV.executeCode 10 (0 : RiscV.Word 32)
      [.branchNe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (RiscV.zeroState 32)).map (fun state => RiscV.readRegister state 3) =
      some 1 := by
  decide

example :
    (RiscV.executeCode 10 (0 : RiscV.Word 32)
      [.branchEq 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (RiscV.zeroState 32)).map
        (fun state => RiscV.readRegister state 3) =
      some 2 := by
  decide

example :
    panSimpProg (.seq (.skip : Prog Nat) (.return (.const 7))) =
      .return (.const 7) := by
  simp [panSimpProg, seqAssoc, retToTail, smartSeq]

example :
    panSimpProg
        ((.seq
          (.call (some (some (.local, "result"), none)) "f" [])
          (.return (.var .local "result"))) : Prog Nat) =
      (.call none "f" [] : Prog Nat) := by
  simp [panSimpProg, seqAssoc, retToTail, seqCallRet, smartSeq]

example :
    structCompileShape
        [("pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
        (.named "pair") = .comb [.one, .one] := by
  simp [structCompileShape, structCompileShapeFuel, lookupInfo]

example :
    structCompileExp
        { structs := [("pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
          locals := [("p", .named "pair")]
          globals := [] }
        (.nField "right" (.nStruct "pair" [("right", .const 7), ("left", .const 3)])) =
      .rField 1 (.rStruct [.const 3, .const 7]) := by
  simp [structCompileExp, structCompileExp.structCompileFields,
    structOldExpShape, structFindFieldIndex,
    structSelectFields, lookupInfo]

end Flapjack
