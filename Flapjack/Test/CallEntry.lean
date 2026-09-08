import Flapjack.RiscV.CorrectnessCallEntry

/-! Regression coverage for the list-level Loop-to-Word call-entry bridge. -/

namespace Flapjack

def callEntryContext : WordContext :=
  { vars := [(10, 2), (11, 3)] }

def callEntryState : RiscV.State 8 :=
  RiscV.writeRegister
    (RiscV.writeRegister (RiscV.zeroState 8) 2 (BitVec.ofNat 8 17))
    3 (BitVec.ofNat 8 29)

def callEntryLocals : Nat → Option (RiscV.Word 8)
  | 10 => some (BitVec.ofNat 8 17)
  | 11 => some (BitVec.ofNat 8 29)
  | _ => none

example :
    loopLocalsMappedToRiscV callEntryContext callEntryLocals callEntryState := by
  intro name value hvalue
  by_cases h10 : name = 10
  · subst name
    simp [callEntryLocals] at hvalue
    subst value
    exact ⟨2, by simp [callEntryContext, wordFindVar, lookupNatInfo,
      RiscV.registerOfNat], by
      simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
  · by_cases h11 : name = 11
    · subst name
      simp [callEntryLocals] at hvalue
      subst value
      exact ⟨3, by simp [callEntryContext, wordFindVar, lookupNatInfo,
        RiscV.registerOfNat], by
        simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
    · have hnone : callEntryLocals name = none := by
        simp [callEntryLocals]
      simp [hnone] at hvalue

example :
    loopReadLocals callEntryLocals [10, 11] =
      some [BitVec.ofNat 8 17, BitVec.ofNat 8 29] := by
  simp [loopReadLocals, callEntryLocals]

example :
    (wordMapVars callEntryContext [10, 11]).mapM (fun name => do
      let register ← RiscV.registerOfNat name
      pure (RiscV.readRegister callEntryState register)) =
        some [BitVec.ofNat 8 17, BitVec.ofNat 8 29] := by
  apply loopReadLocals_wordMapVars_agreement callEntryContext
    { locals := callEntryLocals, globals := fun _ => none, memory := fun _ => none }
    callEntryState [10, 11] [BitVec.ofNat 8 17, BitVec.ofNat 8 29]
  · intro name value hvalue
    by_cases h10 : name = 10
    · subst name
      simp [callEntryLocals] at hvalue
      subst value
      exact ⟨2, by simp [callEntryContext, wordFindVar, lookupNatInfo,
        RiscV.registerOfNat], by
        simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
    · by_cases h11 : name = 11
      · subst name
        simp [callEntryLocals] at hvalue
        subst value
        exact ⟨3, by simp [callEntryContext, wordFindVar, lookupNatInfo,
          RiscV.registerOfNat], by
          simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
      · have hnone : callEntryLocals name = none := by
          simp [callEntryLocals]
        simp [hnone] at hvalue
  · simp [loopReadLocals, callEntryLocals]

end Flapjack
