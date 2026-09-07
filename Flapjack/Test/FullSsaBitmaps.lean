import Flapjack.Pipeline

namespace Flapjack

open RiscV

def fullSsaBitmapRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def fullSsaBitmapDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

def fullSsaBitmapMain :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction 64)) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmaps .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaBitmapRemoveConfig fullSsaBitmapDeclarations

/-! The full-SSA state-threaded pipeline remains executable for a function
    whose body does not allocate; heap-producing bodies use the same entrypoint
    and expose their bitmap table in the returned artifact. -/

#guard fullSsaBitmapMain.isSome

example :
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (wordStackInitialBitmaps false)
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some ([], wordStackInitialBitmaps false) := by
  rfl

theorem fullSsaBitmapAppend_empty_right
    (functions : List (Nat × List Nat × LoopProg (RiscV.Word 64))) :
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
        (wordStackInitialBitmaps false) (functions ++ []) =
      match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
        (wordStackInitialBitmaps false) functions with
      | none => none
      | some (compiled, bitmaps) => some (compiled ++ [], bitmaps) := by
  exact pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps_append _ _ _

end Flapjack
