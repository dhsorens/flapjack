import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

def stackRemoveRiscVConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def wordStackRiscVConfig : WordStackConfig :=
  { locations := [(0, .register 4)], scratch := 31, stackBase := 21 }

example :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.addi 14 0 (BitVec.ofNat 64 7), .ecall] := by
  decide

example :
    labLineInstructionCount
        (.labAsm (.jump ⟨2, 4⟩) [] 0 : LabLine (Word 64)) = 1 := by
  rfl

example :
    labOffset (width := 64) 12 20 = 0 - BitVec.ofNat 64 8 := by
  rfl

example :
    compileLabProgram (width := 64) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
      some [.jal 0 (BitVec.ofNat 64 4),
        .addi 1 0 (BitVec.ofNat 64 7)] := by
  decide

example :
    compileStackProgramNatListToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.call none (.label 2) none : StackProg Nat)),
       (2, .const 1 7)] =
      some [.jal 0 (BitVec.ofNat 64 4),
        .addi 1 0 (BitVec.ofNat 64 7)] := by
  decide +kernel

example :
    compileStackProgramNatListLinkedToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 0 0
      [(1, (.const 1 7 : StackProg Nat))] =
      some [(1, BitVec.ofNat 64 0, [.addi 1 0 (BitVec.ofNat 64 7)])] := by
  decide +kernel

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.arith .add 4 5 6) [] 0]⟩ =
      some [.add 4 5 6] := by
  decide

def haltLabProgram : LabProgram (Word 64) :=
  [⟨1, [.labAsm (.halt : LabAsm (Word 64)) [] 0]⟩]

example :
    (executeLabProgramWithHalt 10 { services := [] } haltLabProgram
      (zeroState 64)).map (fun state => state.pc) =
      some (BitVec.ofNat 64 4) := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shift .lsl 4 5 6) [] 0]⟩ =
      some [.sll 4 5 6] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.longMul 4 5 6 7))) [] 0]⟩ =
      some [.mulHU 4 6 7, .mul 5 6 7] := by
  decide

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.word (.arith (.addCarry 4 5 6 7 8))) [] 0]⟩ =
      some [.sltu 31 0 8, .add 4 6 7, .sltu 5 4 7,
        .add 4 4 31, .sltu 31 4 31, .or 5 5 31] := by
  decide

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.get 4 .heapLength : StackProg (Word 64)) =
      some [
        .addi 29 0 (BitVec.ofNat 64 24),
        .sub 29 10 29,
        .loadWord 4 29] := by
  decide +kernel

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.dataBufferWrite 7 6 : StackProg (Word 64)) =
      some [.storeWord 6 7] := by
  decide +kernel

example :
    (compileStackProgramToRiscV (width := 64) { services := [] }
      stackRemoveRiscVConfig 2 3
      (.storeConsts 6 7 none : StackProg (Word 64))).isSome := by
  decide +kernel

example :
    compileWordProgramNatToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const 42) : WordProg Nat) =
      some [.addi 4 0 (BitVec.ofNat 64 42)] := by
  decide +kernel

example :
    compileWordProgramToRiscV (width := 64) { services := [] }
      wordStackRiscVConfig stackRemoveRiscVConfig 2 3
      (.assign 0 (.const (BitVec.ofNat 64 42)) : WordProg (Word 64)) =
      some [.addi 4 0 (BitVec.ofNat 64 42)] := by
  decide +kernel

example :
    labLineInstructionCount
        (.asm (.shift .ror 4 5 6) [] 0 : LabLine (Word 64)) = 5 := by
  rfl

example :
    compileLabSection (width := 64) { services := [] }
      ⟨3, [.asm (.shift .ror 4 5 6) [] 0]⟩ =
      some [
        .ori 31 0 (BitVec.ofNat 64 64),
        .sub 31 31 6,
        .sll 31 5 31,
        .srl 4 5 6,
        .or 4 4 31] := by
  decide

end Flapjack.RiscV
