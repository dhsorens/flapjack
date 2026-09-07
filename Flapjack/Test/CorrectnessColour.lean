import Flapjack.RiscV.CorrectnessColour

/-! Regression tests for the executable colouring simulation theorem. -/

namespace Flapjack.RiscV

def testColour (name : Nat) : Nat :=
  if name = 1 then 2 else if name = 2 then 1 else name

theorem testColourValidFn : wordColourValid testColour := by
  intro name hname
  by_cases hone : name = 1
  · simp [testColour, hone]
  · by_cases htwo : name = 2
    · simp [testColour, htwo]
    · simpa [testColour, hone, htwo] using hname

theorem testColour_valid : wordColourValid testColour := testColourValidFn

theorem testColour_injective : Function.Injective testColour := by
  intro left right h
  by_cases hleftOne : left = 1 <;> by_cases hleftTwo : left = 2 <;>
    by_cases hrightOne : right = 1 <;> by_cases hrightTwo : right = 2 <;>
      simp [testColour, hleftOne, hleftTwo, hrightOne, hrightTwo] at h ⊢ <;>
        omega

theorem testColour_zero : testColour 0 = 0 := by
  simp [testColour]

def testRelation [NeZero width] (source target : State width) : Prop :=
  WordColourStateRelation testColour source target

def testTargetState [NeZero width] (state : State width) : State width :=
  { state with registers := fun register =>
      if register = 1 then state.registers 2
      else if register = 2 then state.registers 1
      else state.registers register }

theorem testRelation_target [NeZero width] (state : State width) :
    testRelation state (testTargetState state) := by
  unfold testRelation
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  intro name hname
  intro hcolour
  by_cases hone : name = 1
  · subst name
    change state.registers 1 = state.registers 1
    rfl
  · by_cases htwo : name = 2
    · subst name
      change state.registers 2 = state.registers 2
      rfl
    · have hone' : (⟨name, hname⟩ : Fin 32) ≠ 1 := by
        intro h
        apply hone
        exact congrArg Fin.val h
      have htwo' : (⟨name, hname⟩ : Fin 32) ≠ 2 := by
        intro h
        apply htwo
        exact congrArg Fin.val h
      simp [readRegister, testTargetState, testColour, hone, htwo, hone', htwo']

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.seq (.assign 1 (.var 2)) (.assign 2 (.var 1))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.seq (.assign 1 (.var 2)) (.assign 2 (.var 1)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .seq (.assign 1 2 (by omega) (by omega))
      (.assign 2 1 (by omega) (by omega))

example [NeZero width] (state : State width) (value : Word width) :
    ∃ source' target',
      evalWordProg state
          (.seq (.assign 1 (.const value)) (.assign 2 (.var 1))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.seq (.assign 1 (.const value)) (.assign 2 (.var 1)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .seq (.assignConst 1 value (by omega))
      (.assign 2 1 (by omega) (by omega))

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.op .add [.var 1, .var 2])) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.op .add [.var 1, .var 2]))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .assignBinary .add 3 1 2 (by omega) (by omega) (by omega)

example [NeZero width] (state : State width) (value : Word width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.op .and [.var 1, .const value])) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.op .and [.var 1, .const value]))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .assignImmediate .and 3 1 value (by omega) (by omega)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .asr (.var 1) (.var 2))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .asr (.var 1) (.var 2)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .assignShift .asr 3 1 2 (by decide) (by omega) (by omega) (by omega)

example [NeZero width] (state : State width) (amount : Word width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .lsr (.var 1) (.const amount))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .lsr (.var 1) (.const amount)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero state (testTargetState state)
  · exact testRelation_target state
  · exact .assignShiftImmediate .lsr 3 1 amount (by decide) (by omega) (by omega)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .ror (.var 1) (.var 2))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .ror (.var 1) (.var 2)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_assignRotateRight_applyColour testColour
    testColourValidFn testColour_injective testColour_zero (by simp [testColour])
    state (testTargetState state)
  · exact testRelation_target state
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end Flapjack.RiscV
