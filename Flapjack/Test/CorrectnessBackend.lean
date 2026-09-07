import Flapjack.RiscV.CorrectnessBackend

/-! Regression for the compositional straight-line Word/RISC-V theorem. -/

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (program : WordProg (Word width))
    (code : List (Instruction width))
    (hstraight : WordRiscVStraightLine program)
    (hcompile : wordProgToRiscV program = some code) :
    evalWordProg state program = some (executeInstructions state code) := by
  exact wordProgToRiscV_sound_of_straightLine state program hstraight code hcompile

example [NeZero width] (state : State width) :
    (readRegister (executeInstructions state
      [.mulHU 5 2 3, .mul 6 2 3]) 5,
      readRegister (executeInstructions state
        [.mulHU 5 2 3, .mul 6 2 3]) 6) =
      (BitVec.ofNat width
        ((readRegister state 2).toNat * (readRegister state 3).toNat / 2 ^ width),
       readRegister state 2 * readRegister state 3) := by
  exact executeInstructions_longMul_result state

end Flapjack.RiscV
