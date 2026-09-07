import Flapjack.Correctness

namespace Flapjack

def longMulCorrectnessContext : WordContext :=
  { vars := [(1, 3), (2, 2)] }

def longMulCorrectnessLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun name =>
      if name = 1 then some (BitVec.ofNat 64 7)
      else if name = 4 then some (BitVec.ofNat 64 9)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def longMulCorrectnessWordState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister (RiscV.zeroState 64) 3 (BitVec.ofNat 64 7)) 4
    (BitVec.ofNat 64 9)

theorem longMulCorrectness_mappedLocals :
    loopLocalsMappedToRiscV longMulCorrectnessContext
      longMulCorrectnessLoopState.locals longMulCorrectnessWordState := by
  intro name value hvalue
  by_cases hname : name = 1
  · subst name
    simp [longMulCorrectnessLoopState] at hvalue
    subst value
    refine ⟨3, ?_, ?_⟩
    · decide
    · simp [longMulCorrectnessWordState, RiscV.writeRegister,
        RiscV.readRegister]
  · by_cases hname_four : name = 4
    · subst name
      simp [longMulCorrectnessLoopState] at hvalue
      subst value
      refine ⟨4, ?_, ?_⟩
      · decide
      · simp [longMulCorrectnessWordState, RiscV.writeRegister,
          RiscV.readRegister]
    · simp [longMulCorrectnessLoopState, hname, hname_four] at hvalue

theorem longMulCorrectness_noalias :
    ∀ name, name ≠ 2 →
      ∀ register,
        RiscV.registerOfNat (wordFindVar longMulCorrectnessContext name) =
          some register → register ≠ 2 := by
  intro name hname register hregister heq
  have htwo : RiscV.registerOfNat 2 = some (2 : Fin 32) := by
    decide
  have hfind := RiscV.registerOfNat_injective hregister htwo heq
  by_cases hname_one : name = 1
  · subst name
    simp [longMulCorrectnessContext, wordFindVar, lookupNatInfo] at hfind
  · by_cases hname_two : name = 2
    · exact (hname hname_two).elim
    · simp [longMulCorrectnessContext, wordFindVar, lookupNatInfo,
        hname_one, hname_two, Ne.symm hname_one, Ne.symm hname_two] at hfind

example :
    ∀ resultState,
      RiscV.evalWordProg longMulCorrectnessWordState
        (loopToWordProg longMulCorrectnessContext
          (.arith (.longMul 2 2 1 4))) = some resultState →
      loopLocalsMappedToRiscV longMulCorrectnessContext
        (updateLoopLocal longMulCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 7 * BitVec.ofNat 64 9)) resultState := by
  apply loopToWord_longMul_preserves_mapped_locals
    (context := longMulCorrectnessContext)
    (loopState := longMulCorrectnessLoopState)
    (state := longMulCorrectnessWordState)
    (destination := 2) (sourceLeft := 1) (sourceRight := 4)
    (destinationRegister := 2)
    (leftValue := BitVec.ofNat 64 7)
    (rightValue := BitVec.ofNat 64 9)
    (hlocals := longMulCorrectness_mappedLocals)
    (hleft := by simp [longMulCorrectnessLoopState])
    (hright := by simp [longMulCorrectnessLoopState])
    (hdestination := by decide)
    (hdestination_nonzero := by decide)
    (hnoalias := longMulCorrectness_noalias)

example :
    ∀ resultState,
      RiscV.evalWordProg longMulCorrectnessWordState
        (loopToWordProg longMulCorrectnessContext
          (.assign 2 (.var 1))) = some resultState →
      loopLocalsMappedToRiscV longMulCorrectnessContext
        (updateLoopLocal longMulCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 7)) resultState := by
  apply loopToWord_assign_var_preserves_mapped_locals
    (context := longMulCorrectnessContext)
    (loopState := longMulCorrectnessLoopState)
    (state := longMulCorrectnessWordState)
    (destination := 2) (source := 1)
    (destinationRegister := 2) (sourceRegister := 3)
    (sourceValue := BitVec.ofNat 64 7)
    (hlocals := longMulCorrectness_mappedLocals)
    (hsource := by simp [longMulCorrectnessLoopState])
    (hdestination := by decide)
    (hsource_register := by decide)
    (hdestination_nonzero := by decide)
    (hnoalias := longMulCorrectness_noalias)

end Flapjack
