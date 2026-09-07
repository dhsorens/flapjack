import Flapjack.RiscV.Correctness

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (register : Fin 32)
    (hregister_destination : register ≠ 5)
    (hregister_carry : register ≠ 6)
    (hregister_scratch : register ≠ 31) :
    readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) register =
      readRegister state register := by
  exact executeInstructions_addCarry_register_preserved state register
    hregister_destination hregister_carry hregister_scratch

example :
    (readRegister
        (executeInstructions (zeroState 64)
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) 7) =
      readRegister (zeroState 64) 7 := by
  decide

example [NeZero width] (state : State width)
    (zero : readRegister state 0 = 0) :
    (readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) 5,
      readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) 6) =
      addCarryWords (readRegister state 2) (readRegister state 3)
        (readRegister state 4) := by
  apply executeInstructions_addCarry_general state 5 6 2 3 4 zero
  all_goals decide

end Flapjack.RiscV
