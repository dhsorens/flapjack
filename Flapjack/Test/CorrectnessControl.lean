import Flapjack.Correctness

/-!
Regression tests for the control-neutral Loop-to-Word cases.  These remain in
their own file so the arithmetic and primitive correctness fixtures do not
become a catch-all test module.
-/

namespace Flapjack

def controlTestContext : WordContext :=
  { vars := [] }

def controlTestLocals : Nat → Option (RiscV.Word 64) :=
  fun name => if name == 2 then some (BitVec.ofNat 64 7) else none

def controlTestState : RiscV.State 64 :=
  RiscV.writeRegister (RiscV.zeroState 64) 2 7

def controlTestLoopState : LoopState (RiscV.Word 64) :=
  { locals := controlTestLocals
    globals := fun _ => none
    memory := fun _ => none }

theorem controlTestLocals_relation :
    loopLocalsMappedToRiscV controlTestContext controlTestLocals
      controlTestState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    simp [controlTestLocals] at hvalue
    subst value
    refine ⟨2, by decide, ?_⟩
    simp [controlTestState, RiscV.writeRegister, RiscV.readRegister]
  · simp [controlTestLocals, hname] at hvalue

example :
    ∀ finalLoop finalWord,
      evalLoopProg 1 controlTestLoopState (.skip) = some (.normal finalLoop) →
      RiscV.evalWordProg controlTestState
        (loopToWordProg controlTestContext (.skip)) = some finalWord →
      loopLocalsMappedToRiscV controlTestContext finalLoop.locals finalWord := by
  apply loopToWord_skip_preserves_mapped_locals
    (context := controlTestContext)
    (loopState := controlTestLoopState)
    (state := controlTestState)
    (hlocals := controlTestLocals_relation)

end Flapjack
