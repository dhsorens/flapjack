import Flapjack.CorrectnessPrimitive
import Flapjack.Test.LoopCalls

/-!
Concrete regression for the first Loop-to-Word primitive correctness bridge.
The source locals and target registers intentionally use the same small
allocation, making the required non-alias contracts executable.
-/

namespace Flapjack

def primitiveLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := []
    functions := []
    maxVar := 0
    target := .rv64i }

def primitiveMappedContext : WordContext :=
  { vars := [(31, 0)] }

def primitiveMappedLocals : Nat → Option (RiscV.Word 64) :=
  fun name =>
    if name == 2 then some (BitVec.ofNat 64 1)
    else if name == 3 then some (BitVec.ofNat 64 2)
    else if name == 4 then some (BitVec.ofNat 64 0)
    else none

def primitiveMappedState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister
      (RiscV.writeRegister (RiscV.zeroState 64) 2 1) 3 2) 4 0

def primitiveMappedLoopState : LoopState (RiscV.Word 64) :=
  { locals := primitiveMappedLocals
    globals := fun _ => none
    memory := fun _ => none }

theorem primitiveMappedLocals_relation :
    loopLocalsMappedToRiscV primitiveMappedContext primitiveMappedLocals
      primitiveMappedState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    simp [primitiveMappedLocals] at hvalue
    subst value
    refine ⟨2, by decide, ?_⟩
    simp [primitiveMappedState, RiscV.writeRegister, RiscV.readRegister]
  · by_cases hname_three : name = 3
    · subst name
      simp [primitiveMappedLocals] at hvalue
      subst value
      refine ⟨3, by decide, ?_⟩
      simp [primitiveMappedState, RiscV.writeRegister, RiscV.readRegister]
    · by_cases hname_four : name = 4
      · subst name
        simp [primitiveMappedLocals] at hvalue
        subst value
        refine ⟨4, by decide, ?_⟩
        simp [primitiveMappedState, RiscV.writeRegister, RiscV.readRegister]
      · simp [primitiveMappedLocals, hname, hname_three, hname_four] at hvalue

theorem primitiveMapped_noalias :
    ∀ name, name ≠ 5 → name ≠ 6 →
      ∀ register,
        RiscV.registerOfNat (wordFindVar primitiveMappedContext name) =
          some register →
        register ≠ 5 ∧ register ≠ 6 ∧ register ≠ 31 := by
  intro name hname_five hname_six register hregister
  by_cases hname_thirtyOne : name = 31
  · subst name
    simp [primitiveMappedContext, wordFindVar, lookupNatInfo,
      RiscV.registerOfNat] at hregister
    subst register
    decide
  · have hregister' : RiscV.registerOfNat name = some register := by
      simpa [primitiveMappedContext, wordFindVar, lookupNatInfo,
        hname_thirtyOne, Ne.symm hname_thirtyOne] using hregister
    have hfive : RiscV.registerOfNat 5 = some (5 : Fin 32) := by
      decide
    have hsix : RiscV.registerOfNat 6 = some (6 : Fin 32) := by
      decide
    have hthirtyOne : RiscV.registerOfNat 31 = some (31 : Fin 32) := by
      decide
    constructor
    · intro heq
      have hname : name = 5 :=
        RiscV.registerOfNat_injective hregister' hfive heq
      exact hname_five hname
    constructor
    · intro heq
      have hname : name = 6 :=
        RiscV.registerOfNat_injective hregister' hsix heq
      exact hname_six hname
    · intro heq
      have hname : name = 31 :=
        RiscV.registerOfNat_injective hregister' hthirtyOne heq
      exact hname_thirtyOne hname

theorem primitiveMapped_addCarry_preserves_mapped_locals :
    ∀ loopResult resultState,
      evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
          primitiveMappedLoopState
          (.primitive [5, 6] .addCarry [2, 3, 4]) = some loopResult →
      RiscV.evalWordProg primitiveMappedState
          (loopToWordProg primitiveMappedContext
            (.primitive [5, 6] .addCarry [2, 3, 4])) = some resultState →
      loopLocalsMappedToRiscV primitiveMappedContext
        (loopResultState loopResult).locals resultState := by
  apply loopToWord_primitive_addCarry_preserves_mapped_locals
    (context := primitiveMappedContext)
    (loopState := primitiveMappedLoopState)
    (state := primitiveMappedState)
    (destination := 5) (resultCarry := 6) (left := 2) (right := 3) (carry := 4)
    (destinationRegister := 5) (resultCarryRegister := 6)
    (leftRegister := 2) (rightRegister := 3) (carryRegister := 4)
    (leftValue := BitVec.ofNat 64 1) (rightValue := BitVec.ofNat 64 2)
    (carryValue := BitVec.ofNat 64 0)
    (hlocals := primitiveMappedLocals_relation)
    (hleft := by decide)
    (hright := by decide)
    (hcarry := by decide)
    (hdestination := by decide)
    (hresultCarry := by decide)
    (hleft_register := by decide)
    (hright_register := by decide)
    (hcarry_register := by decide)
    (hleft_state := by decide)
    (hright_state := by decide)
    (hcarry_state := by decide)
    (hzero := by simp [primitiveMappedState, RiscV.writeRegister,
      RiscV.readRegister, RiscV.zeroState])
    (hdestination_nonzero := by decide)
    (hresultCarry_nonzero := by decide)
    (hdestination_resultCarry := by decide)
    (hdestination_sourceRight := by decide)
    (hdestination_scratch := by decide)
    (hresultCarry_scratch := by decide)
    (hleft_scratch := by decide)
    (hright_scratch := by decide)
    (hcarry_scratch := by decide)
    (hdestination_name_resultCarry := by decide)
    (hdestination_name_scratch := by decide)
    (hresultCarry_name_scratch := by decide)
    (hleft_name_scratch := by decide)
    (hright_name_scratch := by decide)
    (hcarry_name_scratch := by decide)
    (hnoalias := primitiveMapped_noalias)

example :
    ∀ loopResult resultState,
      evalLoopProgWithPrimitiveCallsAndFfi RiscV.loopPrimitiveHandler []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedLoopState
          (.primitive [5, 6] .addCarry [2, 3, 4]) = some (.normal loopResult) →
      RiscV.evalWordFunctionWithHandlersAndFfi []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedState
          (loopToWordProg primitiveMappedContext
            (.primitive [5, 6] .addCarry [2, 3, 4])) =
        some (.normal resultState) →
      loopLocalsMappedToRiscV primitiveMappedContext loopResult.locals resultState := by
  intro loopResult resultState hloop hword
  apply loopToWord_primitive_addCarry_combined_simulation
    (context := primitiveMappedContext)
    (functions := [])
    (ffiHandler := fun _ _ _ _ _ _ => none)
    (wordFunctions := [])
    (wordHandler := fun _ _ _ _ _ _ => none)
    (loopState := primitiveMappedLoopState)
    (state := primitiveMappedState)
    (destination := 5) (resultCarry := 6) (left := 2) (right := 3) (carry := 4)
    (hprimitive := primitiveMapped_addCarry_preserves_mapped_locals)
  · exact hloop
  · exact hword

theorem primitiveMapped_longMul_noalias :
    ∀ name, name ≠ 5 →
      ∀ register,
        RiscV.registerOfNat (wordFindVar primitiveMappedContext name) =
          some register → register ≠ 5 := by
  intro name hname register hregister heq
  have hfive :
      RiscV.registerOfNat (wordFindVar primitiveMappedContext 5) =
        some (5 : Fin 32) := by
    decide
  have hname' := RiscV.registerOfNat_injective hregister hfive heq
  by_cases hthirtyOne : name = 31
  · subst name
    simp [primitiveMappedContext, wordFindVar, lookupNatInfo] at hname'
  · apply hname
    simpa [primitiveMappedContext, wordFindVar, lookupNatInfo,
      hthirtyOne, Ne.symm hthirtyOne] using hname'

example :
    ∀ loopResult resultState,
      evalLoopProgWithPrimitiveCallsAndFfi RiscV.loopPrimitiveHandler []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedLoopState
          (.arith (.longMul 5 5 2 3)) = some (.normal loopResult) →
      RiscV.evalWordFunctionWithHandlersAndFfi []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedState
          (loopToWordProg primitiveMappedContext
            (.arith (.longMul 5 5 2 3))) =
        some (.normal resultState) →
      loopLocalsMappedToRiscV primitiveMappedContext loopResult.locals resultState := by
  intro loopResult resultState hloop hword
  apply loopToWord_longMul_combined_simulation
    (context := primitiveMappedContext)
    (functions := [])
    (ffiHandler := fun _ _ _ _ _ _ => none)
    (wordFunctions := [])
    (wordHandler := fun _ _ _ _ _ _ => none)
    (loopState := primitiveMappedLoopState)
    (state := primitiveMappedState)
    (destinationLeft := 5) (destinationRight := 5)
    (sourceLeft := 2) (sourceRight := 3)
    (hatomic := by
      intro atomicResult atomicState hsource htarget
      have hsource' : atomicResult = .normal
          { primitiveMappedLoopState with
            locals := updateLoopLocal primitiveMappedLoopState.locals 5
              (BitVec.ofNat 64 1 * BitVec.ofNat 64 2) } := by
        simpa [evalLoopProg, primitiveMappedLoopState, primitiveMappedLocals,
          updateLoopLocal] using hsource.symm
      subst atomicResult
      apply loopToWord_longMul_preserves_mapped_locals
        (context := primitiveMappedContext)
        (loopState := primitiveMappedLoopState)
        (state := primitiveMappedState)
        (destination := 5) (sourceLeft := 2) (sourceRight := 3)
        (destinationRegister := 5)
        (leftValue := BitVec.ofNat 64 1)
        (rightValue := BitVec.ofNat 64 2)
        (hlocals := primitiveMappedLocals_relation)
        (hleft := by decide)
        (hright := by decide)
        (hdestination := by decide)
        (hdestination_nonzero := by decide)
        (hnoalias := primitiveMapped_longMul_noalias)
        atomicState htarget)
  · exact hloop
  · exact hword

example :
    ∀ loopResult resultState,
      evalLoopProgWithPrimitiveCallsAndFfi RiscV.loopPrimitiveHandler []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedLoopState
          (.arith (.div 5 2 3)) = some (.normal loopResult) →
      RiscV.evalWordFunctionWithHandlersAndFfi []
          (fun _ _ _ _ _ _ => none) 1 primitiveMappedState
          (loopToWordProg primitiveMappedContext
            (.arith (.div 5 2 3))) =
        some (.normal resultState) →
      loopLocalsMappedToRiscV primitiveMappedContext loopResult.locals resultState := by
  intro loopResult resultState hloop hword
  apply loopToWord_div_combined_simulation
    (context := primitiveMappedContext)
    (functions := [])
    (ffiHandler := fun _ _ _ _ _ _ => none)
    (wordFunctions := [])
    (wordHandler := fun _ _ _ _ _ _ => none)
    (loopState := primitiveMappedLoopState)
    (state := primitiveMappedState)
    (destination := 5) (dividend := 2) (divisor := 3)
    (hatomic := by
      intro atomicResult atomicState hsource htarget
      have hsource' : atomicResult = .normal
          { primitiveMappedLoopState with
            locals := updateLoopLocal primitiveMappedLoopState.locals 5
              (BitVec.ofNat 64 1 / BitVec.ofNat 64 2) } := by
        simpa [evalLoopProg, primitiveMappedLoopState, primitiveMappedLocals,
          updateLoopLocal] using hsource.symm
      subst atomicResult
      apply loopToWord_div_assign_preserves_mapped_locals
        (context := primitiveMappedContext)
        (loopState := primitiveMappedLoopState)
        (state := primitiveMappedState)
        (destination := 5) (dividend := 2) (divisor := 3)
        (destinationRegister := 5)
        (dividendValue := BitVec.ofNat 64 1)
        (divisorValue := BitVec.ofNat 64 2)
        (hlocals := primitiveMappedLocals_relation)
        (hdividend := by decide)
        (hdivisor := by decide)
        (hdivisor_nonzero := by decide)
        (hdestination := by decide)
        (hdestination_nonzero := by decide)
        (hnoalias := primitiveMapped_longMul_noalias)
        atomicState htarget)
  · exact hloop
  · exact hword

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result =>
          ((loopResultState result).locals 5,
            (loopResultState result).locals 6)) =
      (RiscV.evalWordProg loopAddCarryMachineState
        (loopToWordProg ({ vars := [] } : WordContext)
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result =>
          (some (RiscV.readRegister result 5),
            some (RiscV.readRegister result 6))) := by
  apply loopToWord_primitive_addCarry_agreement
    ({ vars := [] } : WordContext) loopAddCarryState loopAddCarryMachineState
    5 6 2 3 4 5 6 2 3 4
    (BitVec.ofNat 64 1) (BitVec.ofNat 64 2) (BitVec.ofNat 64 0)
  all_goals decide

example :
    (evalCrepStateProgWithPrimitive RiscV.loopPrimitiveHandler
      (fun name => if name == 2 then some (BitVec.ofNat 64 1)
        else if name == 3 then some (BitVec.ofNat 64 2)
        else if name == 4 then some (BitVec.ofNat 64 0)
        else none)
      (.primitive [5, 6] .addCarry [2, 3, 4])).map id =
      (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
        (loopStateOfCrepLocals (fun name => if name == 2 then
          some (BitVec.ofNat 64 1)
        else if name == 3 then some (BitVec.ofNat 64 2)
        else if name == 4 then some (BitVec.ofNat 64 0)
        else none))
        (loopCompileProg primitiveLoopContext []
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result =>
          ((loopResultState result).locals, loopResultValues result)) := by
  apply crepToLoop_primitive_agreement

end Flapjack
