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

example [NeZero width] (state : State width)
    (zero : readRegister state 0 = 0) :
    (readRegister (executeInstructions state
      [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3,
        .add 5 5 31, .sltu 31 5 31, .or 6 6 31]) 5,
      readRegister (executeInstructions state
        [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3,
          .add 5 5 31, .sltu 31 5 31, .or 6 6 31]) 6) =
      addCarryWords (readRegister state 2) (readRegister state 3)
        (readRegister state 4) := by
  exact wordFunctionToRiscVWithCalls_addCarry_result
    ({ targets := [] } : WordCallContext width) state _ zero (by
      simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
        registerOfNat])

example [NeZero width] (state : State width) :
    (readRegister (executeInstructions state
      [.mulHU 5 2 3, .mul 6 2 3]) 5,
      readRegister (executeInstructions state
        [.mulHU 5 2 3, .mul 6 2 3]) 6) =
      (BitVec.ofNat width
        ((readRegister state 2).toNat * (readRegister state 3).toNat / 2 ^ width),
       readRegister state 2 * readRegister state 3) := by
  exact wordFunctionToRiscVWithCalls_longMul_result
    ({ targets := [] } : WordCallContext width) state _ (by
      simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
        registerOfNat])


example [NeZero width] (state : State width)
    (hdivisor : readRegister state 3 ≠ 0) :
    readRegister (executeInstructions state [.divU 5 2 3]) 5 =
      (BitVec.ofNat width
        ((readRegister state 2).toNat / (readRegister state 3).toNat)) := by
  exact wordFunctionToRiscVWithCalls_div_result
    ({ targets := [] } : WordCallContext width) state _ hdivisor (by
      simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
        wordArithToInstruction, registerOfNat])


example [NeZero width] (state : State width)
    (returns : List (Fin 32))
    (hcompile : wordFunctionToRiscVWithCalls
      ({ targets := [] } : WordCallContext width)
      ((.return 0 [2, 3]) : WordProg (Word width)) =
      some ([], returns)) :
    evalWordFunction state ((.return 0 [2, 3]) : WordProg (Word width)) =
      Option.map (fun returned => (executeInstructions state [], returned))
        (([2, 3] : List Nat).mapM (fun name => do
          let register ← registerOfNat name
          pure (readRegister state register))) := by
  exact wordFunctionToRiscVWithCalls_return_sound
    ({ targets := [] } : WordCallContext width) state 0 [2, 3] [] returns hcompile

end Flapjack.RiscV
