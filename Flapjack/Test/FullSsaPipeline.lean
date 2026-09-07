import Flapjack.Pipeline

namespace Flapjack

open RiscV

def fullSsaPipelineRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

/-! Regression for the full-SSA entry sequence through graph allocation and
    Word-to-Stack lowering. -/

#guard
    (pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

#guard
    (pipelineWordFunctionsAllocatedWithSpillsAndFullSsa
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

example :
    pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) = some [] := by
  rfl

#guard
    (compileFlapjackRiscVViaAllocatedStackWithFullSsa (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      fullSsaPipelineRemoveConfig
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]).isSome

#guard
    (compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      fullSsaPipelineRemoveConfig
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]).isSome

end Flapjack
