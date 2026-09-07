import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.ParallelMoveCorrectness

namespace Flapjack.RiscV

example :
    wordStackMoveList
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 } [(0, 1), (1, 0)] =
      some (.seq (.arith .or 29 5 5)
        (.seq (.arith .or 5 4 4) (.arith .or 4 29 29)) : StackProg Nat) := by
  simp [wordStackMoveList, wordStackParallelMove, wordStackParallelMoveAux,
    wordMoveDestinations, wordMoveReady, wordMoveRemoveDestination,
    wordStackMoveToScratch, wordStackMoveFromScratch, wordStackMove,
    wordStackLocation, wordStackOffset, wordStackJoin, lookupNatInfo]

example :
    wordMoveToInstructions (width := 8) [(1, 2), (2, 1)] =
      some [.addi 31 2 0, .addi 2 1 0, .addi 1 31 0] := by
  decide +kernel

example :
    wordMoveToInstructions (width := 8) [(5, 2), (9, 3)] =
      some [.addi 5 2 0, .addi 9 3 0] := by
  have h := wordMoveToInstructions_of_no_source_destination
    (width := 8) [(5, 2), (9, 3)] (by decide) (by decide) (by decide)
  simpa [wordMoveInstructionList, wordExpToInstructions,
    wordExpToInstruction, registerOfNat] using h

example [NeZero 8] (state : State 8) :
    let moves := [(5, 2), (9, 3)]
    let final := executeInstructions state
      (moves.flatMap (wordMoveInstructionList (width := 8)))
    readRegister final 5 = readRegister state 2 ∧
      readRegister final 9 = readRegister state 3 := by
  dsimp
  have h := executeWordMoves_preserves_sources state [(5, 2), (9, 3)]
    (by decide) (by decide) (by decide) (by decide)
  constructor
  · simpa using h (5, 2) (by simp)
  · simpa using h (9, 3) (by simp)

example :
    wordStackMoveList
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10, addressScratch := 29 }
        [(0, 1), (1, 0)] =
      some (.seq (.arith .or 29 5 5)
        (.seq (.seq (.stackLoad 31 12) (.arith .or 5 31 31))
          (.stackStore 29 12)) : StackProg Nat) := by
  simp [wordStackMoveList, wordStackParallelMove, wordStackParallelMoveAux,
    wordMoveDestinations, wordMoveReady, wordMoveRemoveDestination,
    wordStackMoveToScratch, wordStackMoveFromScratch, wordStackMove,
    wordStackLocation, wordStackOffset, wordStackJoin, lookupNatInfo]

example :
    let state : State 8 :=
      writeRegister (writeRegister (zeroState 8) 1 10) 2 20
    let final := executeInstructions state
      [.addi 31 2 0, .addi 2 1 0, .addi 1 31 0]
    (readRegister final 1, readRegister final 2) =
      (BitVec.ofNat 8 20, BitVec.ofNat 8 10) := by
  decide

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .register 5)],
        scratch := 31, stackBase := 10, addressScratch := 29 }
    let state : WordStackMachineState 8 :=
      { registers := fun register =>
          if register = 5 then BitVec.ofNat 8 10 else 0,
        stack := fun offset =>
          if offset = 12 then BitVec.ofNat 8 20 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    let final := (wordStackMoveList config [(0, 1), (1, 0)]).bind
      (evalWordStackMachine state) |>.getD state
    (wordStackMachineValue config final 0,
      wordStackMachineValue config final 1) =
      (some (BitVec.ofNat 8 10), some (BitVec.ofNat 8 20)) := by
  decide +kernel

example :
    let config : WordStackConfig :=
      { locations := [(0, .stack 2), (1, .stack 3)],
        scratch := 31, stackBase := 10, addressScratch := 29 }
    let state : WordStackMachineState 8 :=
      { registers := fun _ => 0,
        stack := fun offset =>
          if offset = 12 then BitVec.ofNat 8 10
          else if offset = 13 then BitVec.ofNat 8 20 else 0,
        stores := fun _ => 0,
        memory := fun _ => 0,
        sharedMemory := fun _ => 0 }
    let final := (wordStackMoveList config [(0, 1), (1, 0)]).bind
      (evalWordStackMachine state) |>.getD state
    (wordStackMachineValue config final 0,
      wordStackMachineValue config final 1) =
      (some (BitVec.ofNat 8 20), some (BitVec.ofNat 8 10)) := by
  decide +kernel

end Flapjack.RiscV
