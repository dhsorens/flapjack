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

end Flapjack.RiscV
