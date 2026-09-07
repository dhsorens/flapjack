import Flapjack.RiscV.AllocatorCorrectness

namespace Flapjack

open RiscV

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory) :
    evalWordExp source
        (.shift .ror (.op .add [.var 2, .var 3]) (.const 4)) =
      evalWordExp target
        (wordSsaRenameExp ssa
          (.shift .ror (.op .add [.var 2, .var 3]) (.const 4))) := by
  apply evalWordExp_ssaRename
  · exact hregister
  · exact hmemory

example [NeZero 64]
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory) :
    evalWordExp source
        (.shift .ror (.op .add [.var 2, .var 3]) (.const 4)) =
      evalWordExp target
        (wordApplyColourExp colour
          (.shift .ror (.op .add [.var 2, .var 3]) (.const 4))) := by
  apply evalWordExp_applyColour
  · exact hregister
  · exact hmemory

example [NeZero 64]
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register))) :
    evalWordCondition source .equal 2 (.reg 3) =
      evalWordCondition target .equal (colour 2)
        (wordApplyColourRegImm colour (.reg 3)) := by
  apply evalWordCondition_applyColour
  exact hregister

example [NeZero 64]
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.return 0 [2, 3])).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.return 0 ([2, 3].map colour))).map wordControlResultValues := by
  exact evalWordReturn_applyColour colour source target hregister 3 0 [2, 3]

example [NeZero 64]
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.raise 2)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.raise (colour 2))).map wordControlResultException := by
  exact evalWordRaise_applyColour colour source target hregister 3 2

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    evalWordCondition source .equal 2 (.reg 3) =
      evalWordCondition target .equal (wordSsaRead ssa 2)
        (wordSsaRenameRegImm ssa (.reg 3)) := by
  apply evalWordCondition_ssaRename
  exact hregister

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.return 0 [2, 3])).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.return 0 ([2, 3].map (wordSsaRead ssa)))).map
        wordControlResultValues := by
  exact evalWordReturn_ssaRename ssa source target hregister 3 0 [2, 3]

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.raise 2)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.raise (wordSsaRead ssa 2))).map wordControlResultException := by
  exact evalWordRaise_ssaRename ssa source target hregister 3 2

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (htarget : wordSsaRead ssa 2 < 32)
    (htargetScratch : wordSsaRead ssa 2 ≠ 31) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.raise 2)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 5 target
        (wordSsaRenameProgram ssa (.raise 2)).2).map
        wordControlResultException := by
  exact evalWordSsaRenameProgram_raise ssa source target hregister 3 2
    (by decide) htarget htargetScratch

example [NeZero 64] (state : State 64) (name sourceName : Nat)
    (hname : name < 32) (hsource : sourceName < 32) :
    evalWordProg state (.assign name (.var sourceName)) =
      some (execute state (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0)) := by
  exact compileWordAssignVar_sound state name sourceName hname hsource

example [NeZero 64] (state : State 64)
    (handler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
      State 64 → Option (State 64))
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat) :
    (evalWordFfi handler 1 state
      (.ffi function configuration configurationLength array arrayLength live)).map Prod.fst =
    (evalWordFfi handler 1 state
      (.ffi function configuration configurationLength array arrayLength
        (live.1.map (fun name => name), live.2.map (fun name => name)))).map Prod.fst := by
  exact evalWordFfi_applyColour (fun name => name) state state handler handler
    (by intro name; rfl) function configuration configurationLength array arrayLength live
    (by rfl)

/-! The full-SSA graph boundary must retain an allocation node for an unused
    formal: the entry move is part of the allocated function even when the
    body is `skip`. -/

example :
    (wordAllocateGraphFunctionWithEntry
      [2] (.skip : WordProg (RiscV.Word 64)) [2] 13 0).isSome := by
  decide +kernel

example
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true := by
  have hsound := wordAllocateGraphFunctionWithEntryRenamed_sound
    parameters program fixedSources colours stackStart state renamedParameters
    allocation renamedProgram halloc
  exact ⟨hsound.1, hsound.2.1⟩

example
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  exact wordAllocateGraphFunctionWithEntryRenamed_maps_parameters
    parameters program fixedSources colours stackStart state renamedParameters
    allocation renamedProgram halloc

end Flapjack
