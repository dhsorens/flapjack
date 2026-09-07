import Flapjack.RiscV.CorrectnessBackend

/-!
Correctness of the register-based condition prelude used by the branch-aware
RISC-V lowering.  Immediate conditions are handled in a follow-up theorem;
this first boundary covers register comparisons and bit tests.
-/

namespace Flapjack.RiscV

def riscVCondition [NeZero width] (state : State width) (operator : Cmp)
    (left right : Fin 32) : Bool :=
  match operator with
  | .equal => readRegister state left == readRegister state right
  | .notEqual => readRegister state left != readRegister state right
  | .less => signedLess (readRegister state left) (readRegister state right)
  | .notLess => !signedLess (readRegister state left) (readRegister state right)
  | .lower => decide (readRegister state left < readRegister state right)
  | .notLower => decide (¬ readRegister state left < readRegister state right)
  | .test => readRegister state left == readRegister state right
  | .notTest => readRegister state left != readRegister state right

theorem wordConditionOperands_register_sound [NeZero width] (state : State width)
    (operator : Cmp) (condition source : Nat) (hzero : ZeroRegister state) :
    ∀ branchLeft right prelude,
      wordConditionOperands operator condition (.reg source) =
        some (branchLeft, right, prelude) →
      evalWordCondition state operator condition (.reg source) =
        riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  intro branchLeft right prelude hoperands
  cases hcondition : registerOfNat condition with
  | none => simp [wordConditionOperands, hcondition] at hoperands
  | some conditionRegister =>
      cases hsource : registerOfNat source with
      | none => simp [wordConditionOperands, hcondition, hsource] at hoperands
      | some sourceRegister =>
          cases operator with
          | equal =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource] <;> rfl
          | notEqual =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource] <;> rfl
          | less =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource]
          | notLess =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource]
          | lower =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource] <;> rfl
          | notLower =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                hcondition, hsource]
          | test =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              have hzero' : state.registers 0 = 0 := hzero
              by_cases hconditionZero : conditionRegister = 0
              · simp [evalWordCondition, riscVCondition, executeInstructions,
                  execute, writeRegister, readRegister, hcondition, hsource, hzero',
                  hconditionZero]
              · simp [evalWordCondition, riscVCondition, executeInstructions,
                  execute, writeRegister, readRegister, hcondition, hsource, hzero',
                  hconditionZero, eq_comm]
          | notTest =>
              simp [wordConditionOperands, hcondition, hsource] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              have hzero' : state.registers 0 = 0 := hzero
              by_cases hconditionZero : conditionRegister = 0
              · simp [evalWordCondition, riscVCondition, executeInstructions,
                  execute, writeRegister, readRegister, hcondition, hsource, hzero',
                  hconditionZero]
              · simp [evalWordCondition, riscVCondition, executeInstructions,
                  execute, writeRegister, readRegister, hcondition, hsource, hzero',
                  hconditionZero, eq_comm]

theorem wordConditionOperands_immediate_zero_sound [NeZero width]
    (state : State width) (operator : Cmp) (condition : Nat)
    (hzero : ZeroRegister state) :
    ∀ branchLeft right prelude,
      wordConditionOperands operator condition (.imm 0) =
        some (branchLeft, right, prelude) →
      evalWordCondition state operator condition (.imm 0) =
        riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  intro branchLeft right prelude hoperands
  have hregister : wordConditionOperands operator condition (.reg 0) =
      some (branchLeft, right, prelude) := by
    simpa [wordConditionOperands] using hoperands
  have heval : evalWordCondition state operator condition (.imm 0) =
      evalWordCondition state operator condition (.reg 0) := by
    change state.registers 0 = 0 at hzero
    cases hcondition : registerOfNat condition <;>
      cases operator <;>
      simp [evalWordCondition, readRegister, hzero, hcondition]
  rw [heval]
  exact wordConditionOperands_register_sound state operator condition 0 hzero
    branchLeft right prelude hregister

theorem wordConditionOperands_immediate_sound [NeZero width]
    (state : State width) (operator : Cmp) (condition : Nat)
    (value : Word width) (hzero : ZeroRegister state) :
    ∀ branchLeft right prelude,
      wordConditionOperands operator condition (.imm value) =
        some (branchLeft, right, prelude) →
      evalWordCondition state operator condition (.imm value) =
        riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  intro branchLeft right prelude hoperands
  by_cases hvalue : value == 0
  · have hvalueEq : value = 0 := eq_of_beq hvalue
    subst value
    exact wordConditionOperands_immediate_zero_sound state operator condition hzero
      branchLeft right prelude hoperands
  · have hvalueNe : value ≠ 0 := by
      intro h
      subst value
      simp at hvalue
    cases hcondition : registerOfNat condition with
    | none => simp [wordConditionOperands, hcondition] at hoperands
    | some conditionRegister =>
        have hzero' : state.registers 0 = 0 := hzero
        simp only [wordConditionOperands, hcondition] at hoperands
        split at hoperands
        · simp_all
        · by_cases hscratch : conditionRegister = 31
          · simp [hscratch] at hoperands
          · cases operator with
          | equal =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero']
          | notEqual =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero']
          | less =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero']
          | notLess =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero']
          | lower =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero'] <;> rfl
          | notLower =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hscratch, hzero']
          | test =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hzero']
          | notTest =>
              simp [hscratch] at hoperands
              rcases hoperands with ⟨hleft, hright, hprelude⟩
              subst branchLeft
              subst right
              subst prelude
              simp [evalWordCondition, riscVCondition, executeInstructions,
                execute, writeRegister, readRegister, hcondition, hzero']

end Flapjack.RiscV
