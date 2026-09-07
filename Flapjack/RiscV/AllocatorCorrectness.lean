import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.RiscV.RegAlloc
import Flapjack.WordSemantics

/-!
Semantic foundations for the SSA and colouring stages of the Word allocator.
The register correspondence is deliberately expressed as an `Option`-valued
equation: it covers both valid RISC-V register names and the evaluator's
failure result for out-of-range virtual names.
-/

namespace Flapjack

open RiscV

theorem wordListRemap_lookup_preserves
    (sources : List Nat) (bijection : WordBijection)
    (source node : Nat)
    (hlookup : lookupNatInfo source bijection.toNode = some node) :
    lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      simpa [wordListRemap] using hlookup
  | cons head tail ih =>
      simp only [wordListRemap]
      split <;> rename_i hhead
      · exact ih bijection hlookup
      · by_cases heq : head = source
        · subst head
          simp [hlookup] at hhead
        · apply ih
          simp [lookupNatInfo, heq, hlookup]

theorem wordListRemap_lookup_of_mem
    (sources : List Nat) (bijection : WordBijection)
    (source : Nat) (hsource : source ∈ sources) :
    ∃ node, lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      cases hsource
  | cons head tail ih =>
      rcases List.mem_cons.mp hsource with hsource_head | htail
      · simp only [wordListRemap]
        have hsource_eq : source = head := hsource_head
        subst source
        split <;> rename_i hhead
        · exact ⟨_, wordListRemap_lookup_preserves tail bijection head _ hhead⟩
        · have hinsert : lookupNatInfo head
              ((head, bijection.next) :: bijection.toNode) = some bijection.next := by
            simp [lookupNatInfo]
          exact ⟨_, wordListRemap_lookup_preserves tail
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } head bijection.next hinsert⟩
      · simp only [wordListRemap]
        split <;> rename_i hhead
        · exact ih bijection htail
        · exact ih
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } htail

theorem wordAllocateGraphFunctionWithStackOnlyRenamed_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithStackOnlyRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithStackOnlyRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨_, rfl⟩
  intro name hname
  have hnode := wordListRemap_lookup_of_mem
    (wordSsaRenameFunction parameters program).2.fst
    (wordClashTreeBijection
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
      { toNode := [], fromNode := [], next := 0 }) name hname
  simpa [wordInitRegAlloc, wordMkBijection,
    wordAllocateGraphFunctionWithStackOnlyRenamed, wordClashTreeBijection] using hnode

theorem wordAllocateGraphFunctionWithStackOnlyRenamed_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithStackOnlyRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithStackOnlyRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

/-! The full-SSA entry variant has the same graph witness, but its clash tree
    starts with the explicit fresh-parameter setup.  Keep this theorem next to
    the ordinary graph contract so downstream callers can use either function
    boundary without unfolding the allocator. -/

theorem wordAllocateGraphFunctionWithEntryRenamed_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

theorem wordAllocateGraphFunctionWithEntryRenamed_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨_, rfl⟩
  intro name hname
  have hnode := wordListRemap_lookup_of_mem
    (wordSsaRenameFunctionWithEntry parameters program).2.fst
    (wordClashTreeBijection
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
      { toNode := [], fromNode := [], next := 0 }) name hname
  simpa [wordInitRegAlloc, wordMkBijection,
    wordAllocateGraphFunctionWithEntryRenamed, wordClashTreeBijection] using hnode

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_sound
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunction parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclash := wordAllocateVarsWithSpillsAndPreferences_sound _ _ _
    inner hinner
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_maps_variables
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpillsAndPreferences_maps_slots
    ((wordSsaRenameFunction parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunction parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []) []).snd
    (wordProgPreferenceEdges (wordSsaRenameFunction parameters program).2.snd)
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_sound
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclash := wordAllocateVarsWithFixedSources_sound _ _ _ _ inner hinner
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_maps_variables
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithFixedSources_maps_slots
    ((wordSsaRenameFunctionWithEntry parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunctionWithEntry parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []) []).snd
    (wordProgPreferenceEdges
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    parameters alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

def wordControlResultValues [NeZero width] :
    WordControlResult width → List (Word width)
  | .returned _ values => values
  | _ => []

def wordControlResultException [NeZero width] :
    WordControlResult width → Option (Word width)
  | .raised _ exception => some exception
  | _ => none

theorem evalWordExp_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (expression : WordExp (Word width)) :
    evalWordExp source expression =
      evalWordExp target (wordSsaRenameExp ssa expression) := by
  cases expression with
  | const value => simp [evalWordExp, wordSsaRenameExp]
  | var name =>
      simpa [wordSsaRenameExp, evalWordExp] using hregister name
  | lookup store => simp [evalWordExp, wordSsaRenameExp]
  | load address =>
      simp only [evalWordExp, wordSsaRenameExp]
      rw [show evalWordExp source address =
          evalWordExp target (wordSsaRenameExp ssa address) from
            evalWordExp_ssaRename ssa source target hregister hmemory address]
      have hword : ∀ value, readWordValue source value =
          readWordValue target value := by
        intro value
        simp [readWordValue, readByte, hmemory]
      simp [hword]
  | op operator arguments =>
      cases arguments with
      | nil => simp [evalWordExp, wordSsaRenameExp]
      | cons left rest =>
          cases rest with
          | nil => simp [evalWordExp, wordSsaRenameExp]
          | cons right rest =>
              cases rest with
              | nil =>
                  cases left with
                  | var left =>
                      cases right with
                      | var right =>
                          simp only [wordSsaRenameExp]
                          simp only [evalWordExp]
                          cases hleft : registerOfNat left <;>
                            cases hleft' : registerOfNat (wordSsaRead ssa left) <;>
                            cases hright : registerOfNat right <;>
                            cases hright' : registerOfNat (wordSsaRead ssa right) <;>
                            all_goals
                              have hleftValue := hregister left
                              have hrightValue := hregister right
                              simp_all [
                                wordSsaRenameExp,
                                evalWordExp]
                      | _ => simp [evalWordExp, wordSsaRenameExp]
                  | _ => simp [evalWordExp, wordSsaRenameExp]
              | cons _ _ => simp [evalWordExp, wordSsaRenameExp]
  | shift operator left right =>
      cases left with
      | var leftName =>
          cases right with
          | var rightName =>
              simp only [wordSsaRenameExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (wordSsaRead ssa leftName) <;>
                cases hright : registerOfNat rightName <;>
                cases hright' : registerOfNat (wordSsaRead ssa rightName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  have hrightValue := hregister rightName
                  simp_all [
                    ]
          | const amount =>
              simp only [wordSsaRenameExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (wordSsaRead ssa leftName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  simp_all [
                    ]
          | _ => simp [evalWordExp, wordSsaRenameExp]
      | _ => simp [evalWordExp, wordSsaRenameExp]

theorem evalWordExp_applyColour [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (expression : WordExp (Word width)) :
    evalWordExp source expression =
      evalWordExp target (wordApplyColourExp colour expression) := by
  cases expression with
  | const value => simp [evalWordExp, wordApplyColourExp]
  | var name =>
      simpa [wordApplyColourExp, evalWordExp] using hregister name
  | lookup store => simp [evalWordExp, wordApplyColourExp]
  | load address =>
      simp only [evalWordExp, wordApplyColourExp]
      rw [show evalWordExp source address =
          evalWordExp target (wordApplyColourExp colour address) from
            evalWordExp_applyColour colour source target hregister hmemory address]
      have hword : ∀ value, readWordValue source value =
          readWordValue target value := by
        intro value
        simp [readWordValue, readByte, hmemory]
      simp [hword]
  | op operator arguments =>
      cases arguments with
      | nil => simp [evalWordExp, wordApplyColourExp]
      | cons left rest =>
          cases rest with
          | nil => simp [evalWordExp, wordApplyColourExp]
          | cons right rest =>
              cases rest with
              | nil =>
                  cases left with
                  | var left =>
                      cases right with
                      | var right =>
                          simp only [wordApplyColourExp]
                          simp only [evalWordExp]
                          cases hleft : registerOfNat left <;>
                            cases hleft' : registerOfNat (colour left) <;>
                            cases hright : registerOfNat right <;>
                            cases hright' : registerOfNat (colour right) <;>
                            all_goals
                              have hleftValue := hregister left
                              have hrightValue := hregister right
                              simp_all [
                                
                                wordApplyColourExp, evalWordExp]
                      | _ => simp [evalWordExp, wordApplyColourExp]
                  | _ => simp [evalWordExp, wordApplyColourExp]
              | cons _ _ => simp [evalWordExp, wordApplyColourExp]
  | shift operator left right =>
      cases left with
      | var leftName =>
          cases right with
          | var rightName =>
              simp only [wordApplyColourExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (colour leftName) <;>
                cases hright : registerOfNat rightName <;>
                cases hright' : registerOfNat (colour rightName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  have hrightValue := hregister rightName
                  simp_all [
                    
                    ]
          | const amount =>
              simp only [wordApplyColourExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (colour leftName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  simp_all [
                    ]
          | _ => simp [evalWordExp, wordApplyColourExp]
      | _ => simp [evalWordExp, wordApplyColourExp]

/-! The first executable assignment correctness lemma.  Keeping the register
    bounds explicit mirrors the allocator invariant: after allocation, every
    virtual name used by this instruction denotes an architectural register. -/

theorem compileWordAssignVar_sound [NeZero width] (state : State width)
    (name sourceName : Nat) (hname : name < 32)
    (hsource : sourceName < 32) :
    evalWordProg state (.assign name (.var sourceName)) =
      some (execute state (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, hname, hsource, executeInstructions]

theorem evalWordCondition_applyColour [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width)) :
    evalWordCondition source operator condition rightValue =
      evalWordCondition target operator (colour condition)
        (wordApplyColourRegImm colour rightValue) := by
  cases rightValue with
  | imm value =>
      simp only [evalWordCondition, wordApplyColourRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (colour condition) <;>
        all_goals
          have hconditionValue := hregister condition
          simp_all [
            ]
  | reg right =>
      simp only [evalWordCondition, wordApplyColourRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (colour condition) <;>
        cases hright : registerOfNat right <;>
        cases hright' : registerOfNat (colour right) <;>
        all_goals
          have hconditionValue := hregister condition
          have hrightValue := hregister right
          simp_all [
            
            ]

theorem evalWordCondition_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width)) :
    evalWordCondition source operator condition rightValue =
      evalWordCondition target operator (wordSsaRead ssa condition)
        (wordSsaRenameRegImm ssa rightValue) := by
  cases rightValue with
  | imm value =>
      simp only [evalWordCondition, wordSsaRenameRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (wordSsaRead ssa condition) <;>
        all_goals
          have hconditionValue := hregister condition
          simp_all [
            ]
  | reg right =>
      simp only [evalWordCondition, wordSsaRenameRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (wordSsaRead ssa condition) <;>
        cases hright : registerOfNat right <;>
        cases hright' : registerOfNat (wordSsaRead ssa right) <;>
        all_goals
          have hconditionValue := hregister condition
          have hrightValue := hregister right
          simp_all [
            
            ]

theorem evalWordReturn_applyColour [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (fuel label : Nat) (values : List Nat) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) source
        (.return label values)).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) target
        (.return label (values.map colour))).map
        wordControlResultValues := by
  have hvalues :
      values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (values.map colour).mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister target register)) := by
    induction values with
    | nil => rfl
    | cons name values ih =>
        simp only [List.map, List.mapM_cons]
        rw [hregister name, ih]
  simp only [evalWordFunctionWithHandlersAndFfi, Option.map]
  rw [hvalues]
  cases hresult : List.mapM (fun name => do
      let register ← registerOfNat name
      pure (readRegister target register)) (List.map colour values) with
  | none => simp []
  | some returnedValues => simp [wordControlResultValues]

theorem evalWordRaise_applyColour [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (fuel exception : Nat) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) source
        (.raise exception)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) target
        (.raise (colour exception))).map wordControlResultException := by
  simp only [evalWordFunctionWithHandlersAndFfi, Option.map]
  cases hsource : registerOfNat exception <;>
    cases htarget : registerOfNat (colour exception) <;>
    all_goals
      have hexceptionValue := hregister exception
      simp_all [
        wordControlResultException]

theorem evalWordReturn_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (fuel label : Nat) (values : List Nat) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) source
        (.return label values)).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) target
        (.return label (values.map (wordSsaRead ssa)))).map
        wordControlResultValues := by
  have hvalues :
      values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (values.map (wordSsaRead ssa)).mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister target register)) := by
    induction values with
    | nil => rfl
    | cons name values ih =>
        simp only [List.map, List.mapM_cons]
        rw [hregister name, ih]
  simp only [evalWordFunctionWithHandlersAndFfi, Option.map]
  rw [hvalues]
  cases hresult : List.mapM (fun name => do
      let register ← registerOfNat name
      pure (readRegister target register)) (List.map (wordSsaRead ssa) values) with
  | none => simp []
  | some returnedValues => simp [wordControlResultValues]

theorem evalWordRaise_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (fuel exception : Nat) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) source
        (.raise exception)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) target
        (.raise (wordSsaRead ssa exception))).map
        wordControlResultException := by
  simp only [evalWordFunctionWithHandlersAndFfi, Option.map]
  cases hsource : registerOfNat exception <;>
    cases htarget : registerOfNat (wordSsaRead ssa exception) <;>
    all_goals
      have hexceptionValue := hregister exception
      simp_all [
        wordControlResultException]

/-! FFI is an explicit semantic environment at the Word boundary.  This
    lemma records the exact compatibility condition required when a completed
    colouring changes the four ABI argument registers: the host transition on
    the source state must agree with the host transition on the coloured state. -/

theorem evalWordFfi_applyColour [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (sourceHandler targetHandler : FunName → Word width → Word width →
      Word width → Word width → State width → Option (State width))
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat)
    (hhandler :
      (do
        let configuration ← registerOfNat configuration
        let configurationLength ← registerOfNat configurationLength
        let array ← registerOfNat array
        let arrayLength ← registerOfNat arrayLength
        sourceHandler function (readRegister source configuration)
          (readRegister source configurationLength) (readRegister source array)
          (readRegister source arrayLength) source) =
      (do
        let configuration ← registerOfNat (colour configuration)
        let configurationLength ← registerOfNat (colour configurationLength)
        let array ← registerOfNat (colour array)
        let arrayLength ← registerOfNat (colour arrayLength)
        targetHandler function (readRegister target configuration)
          (readRegister target configurationLength) (readRegister target array)
          (readRegister target arrayLength) target)) :
    (evalWordFfi sourceHandler 1 source
      (.ffi function configuration configurationLength array arrayLength live)).map Prod.fst =
    (evalWordFfi targetHandler 1 target
      (.ffi function (colour configuration) (colour configurationLength)
        (colour array) (colour arrayLength)
        (live.1.map colour, live.2.map colour))).map Prod.fst := by
  simp only [evalWordFfi, Option.map]
  cases hconfiguration : registerOfNat configuration <;>
    cases hconfigurationLength : registerOfNat configurationLength <;>
    cases harray : registerOfNat array <;>
    cases harrayLength : registerOfNat arrayLength <;>
    cases hconfiguration' : registerOfNat (colour configuration) <;>
    cases hconfigurationLength' : registerOfNat (colour configurationLength) <;>
    cases harray' : registerOfNat (colour array) <;>
    cases harrayLength' : registerOfNat (colour arrayLength) <;>
    all_goals
      have hconfigurationValue := hregister configuration
      have hconfigurationLengthValue := hregister configurationLength
      have harrayValue := hregister array
      have harrayLengthValue := hregister arrayLength
      simp_all [
        ]

end Flapjack
