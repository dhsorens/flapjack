import Flapjack.RiscV.Lab

namespace Flapjack

open RiscV

def heapAllocTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example :
    labFlatten false 1 2 [] [] (.alloc 3 : StackProg Nat) =
      { lines := [.labAsm (.heapAlloc 3) [] 0],
        terminal := false, nextLabel := 2 } := by
  simp [labFlatten]

example :
    compileStackProgramToRiscV (width := 64) { services := [] }
      heapAllocTestConfig 0 0 (.alloc 1 : StackProg (Word 64)) = none := by
  native_decide

end Flapjack
