import Flapjack.Pipeline

namespace Flapjack

open RiscV

def fullSsaPipelineRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def fullSsaMainDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

def fullSsaMainLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaPipelineRemoveConfig fullSsaMainDeclarations

def fullSsaMainImage : Option (List (RiscV.Instruction 64)) :=
  fullSsaMainLinked.map (List.flatMap (fun (_, _, code) => code))

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
    fullSsaMainLinked.isSome

theorem fullSsaMain_compiled_execution :
    (do
      let image ← fullSsaMainImage
      RiscV.executeFunctionAt 100 0 76 6 [] image [2] []
        (RiscV.zeroState 64)) = some [BitVec.ofNat 64 7] := by
  native_decide

end Flapjack
