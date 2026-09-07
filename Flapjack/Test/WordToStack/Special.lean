import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness

namespace Flapjack.RiscV
example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      some (.inst (.arith (.longMul 4 5 6 7)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongMulInst, wordStackLongMulLocationsSafe,
    wordStackLongMulLocationSafe, 
    wordStackLocation, 
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      some (.inst (.arith (.addCarry 4 5 6 7 8)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackAddCarryInst, wordStackAddCarryLocationSafe,
    
    wordStackLocation, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 4), (1, .register 5),
            (2, .register 4), (3, .register 7)],
          scratch := 31, stackBase := 10 } (.longMul 0 1 2 3) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .register 6)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      some (.inst (.arith (.longDiv 0 3 3 0 6)) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .stack 2)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      some (.seq (.stackLoad 31 12)
        (.inst (.arith (.longDiv 0 3 3 0 31))) : StackProg Nat) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(4, .register 3)],
          scratch := 31, stackBase := 10 } (.longDiv 0 3 3 0 4) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    wordStackLongDivInst, wordStackLocation,
    lookupNatInfo]

example :
    wordStackArithInst
        { locations := [(0, .register 31), (1, .register 5),
            (2, .register 6), (3, .register 7), (4, .register 8)],
          scratch := 31, stackBase := 10 } (.addCarry 0 1 2 3 4) =
      (none : Option (StackProg Nat)) := by
  simp [wordStackArithInst, wordSpecialArithLocationsSafe,
    lookupNatInfo]

example :
    wordToStackProgNat
        { locations := [(0, .register 10), (1, .register 2),
            (2, .register 3), (3, .register 4)],
          scratch := 31, stackBase := 10 }
        ((.ffi "sum" 0 1 2 3 ([], [])) : WordProg Nat) = none := by
  native_decide

end Flapjack.RiscV
