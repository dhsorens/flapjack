import Flapjack.RiscV.RegAlloc

/-!
An oracle-backed entry point for the CakeML-shaped Word allocator.

CakeML accepts an optional externally supplied colouring when it satisfies the
clash-tree, forced-clash, and stack-colour checks.  The graph allocator already
provides the same executable clash-tree oracle and total-colour convention;
this module connects those pieces at the function boundary so a validated
colouring can be consumed by the existing Word pipeline.
-/

namespace Flapjack

def wordClashTreeNames : WordClashTree → List Nat
  | .delta writes reads => writes ++ reads
  | .set names => names
  | .branch branchLive thenBranch elseBranch =>
      (match branchLive with
      | none => []
      | some names => names) ++
        wordClashTreeNames thenBranch ++ wordClashTreeNames elseBranch
  | .seq first second => wordClashTreeNames first ++ wordClashTreeNames second
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

def wordOracleColour (oracle : NatInfoMap Nat) (source : Nat) : Nat :=
  match lookupNatInfo source oracle with
  | some colour => 2 * colour
  | none => if source % 2 == 0 then source else 0

def wordOracleEdgesSafe (colour : Nat → Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (left, right) :: edges =>
      colour left != colour right && wordOracleEdgesSafe colour edges

def wordOracleStackSafe (colour : Nat → Nat) (stackStart : Nat) :
    List Nat → Bool
  | [] => true
  | name :: names =>
      (if name % 4 == 3 then colour name ≥ stackStart else true) &&
        wordOracleStackSafe colour stackStart names

def wordOracleColouringOk (_colours stackStart : Nat)
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (oracle : NatInfoMap Nat) : Bool :=
  let colour := wordOracleColour oracle
  (wordClashTreeCheck colour tree [] []).isSome &&
    wordOracleEdgesSafe colour forced &&
      wordOracleStackSafe colour stackStart
        (wordClashTreeNames tree).eraseDups

def wordAllocateFunctionWithOracle (parameters : List Nat)
    (program : WordProg α) (colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordSsaState × List Nat × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (state, renamedParameters, wordApplyColour colour renamedProgram)
  else
    none

theorem wordOracleColouringOk_rejects_forced_alias
    (colours stackStart : Nat) (tree : WordClashTree)
    (oracle : NatInfoMap Nat) (name : Nat) :
    wordOracleColouringOk colours stackStart tree [(name, name)] oracle =
      false := by
  simp [wordOracleColouringOk, wordOracleEdgesSafe]

theorem wordAllocateFunctionWithOracle_sound
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat) (oracle : NatInfoMap Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracle parameters program colours stackStart oracle =
      some (state, renamedParameters, renamedProgram)) :
    wordOracleColouringOk colours stackStart
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
        oracle = true := by
  simp [wordAllocateFunctionWithOracle] at halloc
  rcases halloc with ⟨hcheck, rfl, rfl, rfl⟩
  exact hcheck

end Flapjack
