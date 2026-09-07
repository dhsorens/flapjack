import Flapjack.RiscV.Backend
import Flapjack.RiscV.PanSemantics

/-!
Register-level correctness for the RISC-V lowering of Pancake's `AddCarry`
primitive.  This is the first backend theorem that connects the emitted
instruction sequence to the source-level word operation.
-/

namespace Flapjack.RiscV

theorem executeInstructions_addCarry [NeZero width] (state : State width)
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
  have zero' : state.registers 0 = 0 := by
    simpa [readRegister] using zero
  by_cases firstCarry : state.registers 2 + state.registers 3 < state.registers 3
  · by_cases secondCarry :
        state.registers 2 + state.registers 3 +
            (if 0#width < state.registers 4 then 1#width else 0#width) <
          (if 0#width < state.registers 4 then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
  · by_cases secondCarry :
        state.registers 2 + state.registers 3 +
            (if 0#width < state.registers 4 then 1#width else 0#width) <
          (if 0#width < state.registers 4 then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]

theorem executeInstructions_addCarry_register_preserved [NeZero width]
    (state : State width) (register : Fin 32)
    (hregister_destination : register ≠ 5)
    (hregister_carry : register ≠ 6)
    (hregister_scratch : register ≠ 31) :
    readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) register =
      readRegister state register := by
  simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
    hregister_destination, hregister_carry, hregister_scratch]

theorem executeInstructions_addCarry_general [NeZero width]
    (state : State width) (destination resultCarry sourceLeft sourceRight carryIn : Fin 32)
    (zero : readRegister state 0 = 0)
    (destination_nonzero : destination ≠ 0)
    (resultCarry_nonzero : resultCarry ≠ 0)
    (destination_resultCarry : destination ≠ resultCarry)
    (destination_sourceRight : destination ≠ sourceRight)
    (destination_scratch : destination ≠ 31)
    (resultCarry_scratch : resultCarry ≠ 31)
    (sourceLeft_scratch : sourceLeft ≠ 31)
    (sourceRight_scratch : sourceRight ≠ 31)
    (carryIn_scratch : carryIn ≠ 31) :
    (readRegister
        (executeInstructions state
          [.sltu 31 0 carryIn, .add destination sourceLeft sourceRight,
            .sltu resultCarry destination sourceRight,
            .add destination destination 31, .sltu 31 destination 31,
            .or resultCarry resultCarry 31]) destination,
      readRegister
        (executeInstructions state
          [.sltu 31 0 carryIn, .add destination sourceLeft sourceRight,
            .sltu resultCarry destination sourceRight,
            .add destination destination 31, .sltu 31 destination 31,
            .or resultCarry resultCarry 31]) resultCarry) =
      addCarryWords (readRegister state sourceLeft)
        (readRegister state sourceRight) (readRegister state carryIn) := by
  have zero' : state.registers 0 = 0 := by
    simpa [readRegister] using zero
  have resultCarry_destination : resultCarry ≠ destination :=
    Ne.symm destination_resultCarry
  have sourceRight_destination : sourceRight ≠ destination :=
    Ne.symm destination_sourceRight
  have scratch_destination : 31 ≠ destination :=
    Ne.symm destination_scratch
  have scratch_resultCarry : 31 ≠ resultCarry :=
    Ne.symm resultCarry_scratch
  have scratch_sourceLeft : 31 ≠ sourceLeft :=
    Ne.symm sourceLeft_scratch
  have scratch_sourceRight : 31 ≠ sourceRight :=
    Ne.symm sourceRight_scratch
  have scratch_carryIn : 31 ≠ carryIn :=
    Ne.symm carryIn_scratch
  by_cases firstCarry :
      state.registers sourceLeft + state.registers sourceRight <
        state.registers sourceRight
  · by_cases secondCarry :
        state.registers sourceLeft + state.registers sourceRight +
            (if 0#width < state.registers carryIn then 1#width else 0#width) <
          (if 0#width < state.registers carryIn then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, destination_nonzero,
        resultCarry_nonzero, destination_resultCarry,
        destination_scratch, resultCarry_scratch,
        sourceLeft_scratch, sourceRight_scratch, 
        resultCarry_destination, sourceRight_destination, scratch_destination,
        scratch_resultCarry, 
        
        addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, destination_nonzero,
        resultCarry_nonzero, destination_resultCarry,
        destination_scratch, resultCarry_scratch,
        sourceLeft_scratch, sourceRight_scratch, 
        resultCarry_destination, sourceRight_destination, scratch_destination,
        scratch_resultCarry, 
        
        addCarryWords_riscv_formula]
  · by_cases secondCarry :
        state.registers sourceLeft + state.registers sourceRight +
            (if 0#width < state.registers carryIn then 1#width else 0#width) <
          (if 0#width < state.registers carryIn then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, destination_nonzero,
        resultCarry_nonzero, destination_resultCarry,
        destination_scratch, resultCarry_scratch,
        sourceLeft_scratch, sourceRight_scratch, 
        resultCarry_destination, sourceRight_destination, scratch_destination,
        scratch_resultCarry, 
        
        addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, destination_nonzero,
        resultCarry_nonzero, destination_resultCarry,
        destination_scratch, resultCarry_scratch,
        sourceLeft_scratch, sourceRight_scratch, 
        resultCarry_destination, sourceRight_destination, scratch_destination,
        scratch_resultCarry, 
        
        addCarryWords_riscv_formula]

end Flapjack.RiscV
