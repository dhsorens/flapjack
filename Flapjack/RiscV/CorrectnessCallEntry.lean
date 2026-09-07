import Flapjack.Correctness

/-!
# Loop-to-Word call-entry contracts

The Loop evaluator reads a list of local names before entering a callee.  The
Word evaluator performs the same operation after mapping those names to
registers.  This file exposes that list-level agreement independently of any
particular callee body, so later call proofs can reuse it without duplicating
the recursive option reasoning.
-/

namespace Flapjack

theorem loopReadLocals_wordMapVars_agreement [NeZero width]
    (context : WordContext)
    (loopState : LoopState (RiscV.Word width))
    (wordState : RiscV.State width)
    (names : List Nat) (values : List (RiscV.Word width))
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hread : loopReadLocals loopState.locals names = some values) :
    (wordMapVars context names).mapM (fun name => do
      let register ← RiscV.registerOfNat name
      pure (RiscV.readRegister wordState register)) = some values := by
  induction names generalizing values with
  | nil =>
      have hread' : values = [] := by
        simpa [loopReadLocals] using hread
      subst values
      simp [wordMapVars]
  | cons name names ih =>
      cases hlocal : loopState.locals name with
      | none =>
          simp [loopReadLocals, hlocal] at hread
      | some value =>
          cases hrest : loopReadLocals loopState.locals names with
          | none =>
              simp [loopReadLocals, hlocal, hrest] at hread
          | some rest =>
              have hread' : values = value :: rest := by
                simpa [loopReadLocals, hlocal, hrest] using hread.symm
              subst values
              rcases hlocals name value hlocal with
                ⟨register, hregister, hvalue⟩
              have htail := ih rest hrest
              have htail' :
                  (wordMapVars context names).mapM (fun name =>
                    (RiscV.registerOfNat name).bind (fun register =>
                      some (RiscV.readRegister wordState register))) = some rest := by
                simpa using htail
              simp [wordMapVars, hregister, hvalue]
              rw [htail']
              simp

end Flapjack
