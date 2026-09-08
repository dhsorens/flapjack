import Flapjack.Pipeline
import Flapjack.Semantics

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

def fullSsaMainGraphImage : Option (List (RiscV.Instruction 64)) :=
  compileFlapjackRiscVViaGraphStackWithFullSsa .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaPipelineRemoveConfig fullSsaMainDeclarations

/-! Regression for the full-SSA entry sequence through graph allocation and
    Word-to-Stack lowering. -/

#guard
    (pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

#guard
    (wordAllocateGraphFunctionWithEntryPrefreezeRenamed [2]
      (.assign 3 (.var 2) : WordProg (RiscV.Word 64)) [2] 13 14).isSome

#guard
    (pipelineWordFunctionsAllocatedWithSpillsAndFullSsa
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

example :
    pipelineWordFunctionsAllocatedWithGraphAndFullSsa
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) = some [] := by
  rfl

#guard
    fullSsaMainLinked.isSome

#guard
    fullSsaMainGraphImage.isSome

theorem fullSsaMain_compiled_execution :
    (do
      let image ← fullSsaMainImage
      RiscV.executeFunctionAt 100 0 76 6 [] image [2] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 6))) =
      some [BitVec.ofNat 64 7] := by
  native_decide

theorem fullSsaMain_graph_compiled_execution :
    (do
      let image ← fullSsaMainGraphImage
      RiscV.executeFunctionAt 100 0 76 6 [] image [2] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 6))) =
      some [BitVec.ofNat 64 7] := by
  native_decide

def fullSsaFfiMainBody : Prog (RiscV.Word 64) :=
  .dec "result" .one (.const 0)
    (.seq
      (.extCall "inc" (.const 41) (.const 0) (.const 0) (.const 0))
      (.return (.var .local "result")))

def fullSsaFfiDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := fullSsaFfiMainBody, returnShape := .one }]

def fullSsaFfiSourceHandler : PanFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + 1))
    else none

def fullSsaFfiLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) [("inc", 7)]
    fullSsaPipelineRemoveConfig fullSsaFfiDeclarations

def fullSsaFfiImage : Option (List (RiscV.Instruction 64)) :=
  fullSsaFfiLinked.map (List.flatMap (fun (_, _, code) => code))

def fullSsaFfiHost : RiscV.WordFfiHost 64 :=
  fun service configuration _ _ _ state =>
    if service = 7 then
      some { (RiscV.writeRegister state 11 (configuration + 1)) with
        pc := state.pc + 4 }
    else none

theorem fullSsaFfi_compiled_execution :
    (do
      let image ← fullSsaFfiImage
      RiscV.executeFunctionAtWithFfi fullSsaFfiHost 100 0 76 42 [] image [2] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 42))) =
      some [BitVec.ofNat 64 42] := by
  native_decide

theorem fullSsaFfi_source_execution :
    (evalPanProgWithCallsAndFfi [] fullSsaFfiSourceHandler 20
      (fun _ => none) fullSsaFfiMainBody).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42] := by
  decide +kernel

theorem fullSsaFfi_source_machine_agreement :
    (evalPanProgWithCallsAndFfi [] fullSsaFfiSourceHandler 20
      (fun _ => none) fullSsaFfiMainBody).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42] ∧
      (do
        let image ← fullSsaFfiImage
        RiscV.executeFunctionAtWithFfi fullSsaFfiHost 100 0 76 42 [] image [2] []
          (RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 42))) =
        some [BitVec.ofNat 64 42] :=
  ⟨fullSsaFfi_source_execution, fullSsaFfi_compiled_execution⟩

end Flapjack
