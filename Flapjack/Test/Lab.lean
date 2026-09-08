import Flapjack.Lab

namespace Flapjack

def labStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    labFlatten false 20 7 [] []
      (.ffi "sum" 1 2 3 4 9 : StackProg Nat) =
      { lines := [
          .labAsm (.locValue 9 ⟨20, 7⟩) [] 0,
          .labAsm (.callFfi "sum") [] 0,
          .label 20 7 0],
        terminal := false,
        nextLabel := 8 } := by
  simp [labFlatten, labLabel]

example :
    labFlatten false 3 4 [] []
      (.loop (.seq (.tick) (.break 0)) : StackProg Nat) =
      { lines := [
          .label 3 4 0,
          .asm .tick [] 0,
          .labAsm (.jump ⟨3, 5⟩) [] 0,
          .labAsm (.jump ⟨3, 4⟩) [] 0,
          .label 3 5 0],
        terminal := false,
        nextLabel := 6 } := by
  simp [labFlatten, labLabel, labJump, labFindLabel]

example :
    labProgramToSection 2 3
      (.seq (.tick) (.return 4) : StackProg Nat) =
      ⟨2, [
        .asm .tick [] 0,
        .label 2 1 0,
        .labAsm .return [] 0,
        .label 2 3 0]⟩ := by
  simp [labProgramToSection, labFlatten, labIsSequence, labLabel]

example :
    labFlatten false 2 3 [] []
      (.seq (.arith .add 4 5 6) (.shift .lsl 7 8 9) : StackProg Nat) =
      { lines := [
          .asm (.arith .add 4 5 6) [] 0,
          .asm (.shift .lsl 7 8 9) [] 0],
        terminal := false,
        nextLabel := 3 } := by
  simp [labFlatten]

example :
    labProgramToSectionAfterStackRemove labStackRemoveConfig 2 3
      (.get 4 .heapLength : StackProg Nat) =
      ⟨2, [
        .asm (.const 29 24) [] 0,
        .asm (.arith .sub 29 10 29) [] 0,
        .label 2 1 0,
        .asm (.word (.mem .load 4 29)) [] 0,
        .label 2 3 0]⟩ := by
  simp [labProgramToSectionAfterStackRemove, labProgramToSection,
    stackRemoveComplete, stackRemoveFuel, stackProgDepth, stackRemoveGet,
    stackRemoveAddress,
    stackRemoveJoin, stackStorePosition, labFlatten, labLabel,
    labIsSequence, labStackRemoveConfig]

end Flapjack
