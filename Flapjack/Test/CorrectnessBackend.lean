import Flapjack.RiscV.CorrectnessBackend

/-! Regression for the compositional straight-line Word/RISC-V theorem. -/

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (program : WordProg (Word width))
    (code : List (Instruction width))
    (hstraight : WordRiscVStraightLine program)
    (hcompile : wordProgToRiscV program = some code) :
    evalWordProg state program = some (executeInstructions state code) := by
  exact wordProgToRiscV_sound_of_straightLine state program hstraight code hcompile

end Flapjack.RiscV
