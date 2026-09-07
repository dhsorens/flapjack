import Flapjack.Test.Compile

namespace Flapjack

open RiscV
example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsl (.var 2) (.var 3)) =
      some (.sll 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsr (.var 2) (.var 3)) =
      some (.srl 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .asr (.var 2) (.var 3)) =
      some (.sra 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .ror (.var 2) (.var 3)) = none := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) =
      some [.srli 31 2 3, .slli 1 2 5, .or 1 1 31] := by
  decide

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.var 3)) =
      some [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] := by
  decide

example :
    RiscV.wordExpToInstructions (width := 8) 31
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) = none := by
  decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2]
      [.srli 31 2 1, .slli 1 2 7, .or 1 1 31] [1]
      [129] (RiscV.zeroState 8) = some [192] := by
  decide

example :
    RiscV.executeFunction 30 (0 : RiscV.Word 8) [2, 3]
      [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] [1]
      [129, 1] (RiscV.zeroState 8) = some [192] := by
  decide

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.var 3))) =
      some (RiscV.execute state (.sll 1 2 3)) := by
  exact RiscV.compileWordShiftLsl_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.var 3))) =
      some (RiscV.execute state (.srl 1 2 3)) := by
  exact RiscV.compileWordShiftLsr_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.var 3))) =
      some (RiscV.execute state (.sra 1 2 3)) := by
  exact RiscV.compileWordShiftAsr_sound state

example :
    RiscV.shiftAmount (BitVec.ofNat 64 65) = 1 := by
  decide

example :
    evalPanExp (fun _ => none)
      (.panOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  decide

example :
    evalCrepExp (fun _ => none)
      (.crepOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  decide

example :
    evalCrepProg (fun _ => none)
        (compileProg crepContext
          (.return (.panOp .mul [.const (α := Nat) 6, .const 7]))) =
      evalPanProg (fun _ => none)
        (.return (.panOp .mul [.const (α := Nat) 6, .const 7])) := by
  exact compile_pan_mul_const_preserves_semantics crepContext 6 7
    (fun _ => none) (fun _ => none)


end Flapjack
