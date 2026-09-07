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

example [NeZero width] (state : State width)
    (destinationLeft destinationRight sourceLeft sourceRight : Fin 32)
    (hdestinationLeft_nonzero : destinationLeft ≠ 0)
    (hdestinationRight_nonzero : destinationRight ≠ 0)
    (hdestination_distinct : destinationLeft ≠ destinationRight)
    (hdestinationLeft_sourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeft_sourceRight : destinationLeft ≠ sourceRight) :
    (readRegister (executeInstructions state
      [.mulHU destinationLeft sourceLeft sourceRight,
       .mul destinationRight sourceLeft sourceRight]) destinationLeft,
      readRegister (executeInstructions state
        [.mulHU destinationLeft sourceLeft sourceRight,
         .mul destinationRight sourceLeft sourceRight]) destinationRight) =
      (BitVec.ofNat width
        ((readRegister state sourceLeft).toNat *
          (readRegister state sourceRight).toNat / 2 ^ width),
       readRegister state sourceLeft * readRegister state sourceRight) := by
  exact executeInstructions_longMul_general state destinationLeft destinationRight
    sourceLeft sourceRight hdestinationLeft_nonzero hdestinationRight_nonzero
    hdestination_distinct hdestinationLeft_sourceLeft hdestinationLeft_sourceRight

end Flapjack.RiscV
