import Flapjack.RiscV.Backend

/-!
Correctness facts for the executable parallel-move lowering.  CakeML's
full-SSA entry setup generates fresh destinations, so its entry move list is
acyclic: no source is one of the destinations.  In that case the lowering can
take every move in source order without using the reserved scratch register.
-/

namespace Flapjack.RiscV

def wordMoveInstructionList [NeZero width] (move : Nat × Nat) :
    List (Instruction width) :=
  match wordExpToInstructions (width := width) move.1
      ((.var move.2) : WordExp (Word width)) with
  | some instructions => instructions
  | none => []

theorem wordMoveToInstructions_of_no_source_destination [NeZero width]
    (moves : List (Nat × Nat))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves → move.2 ∉ moves.map Prod.fst)
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31) :
    wordMoveToInstructions moves =
      some (moves.flatMap (wordMoveInstructionList (width := width))) := by
  induction moves with
  | nil =>
      simp [wordMoveToInstructions, wordMoveToInstructionsAux,
        wordMoveRegisterDestinations]
  | cons head tail ih =>
      have hheadValid := hvalid head (by simp)
      have htailValid : ∀ move, move ∈ tail →
          move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
        intro move hmove
        exact hvalid move (by simp [hmove])
      have hdestinations' : (head.1 :: tail.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hdestinations
      have hheadNotDestination : head.1 ∉ tail.map Prod.fst :=
        (List.nodup_cons.mp hdestinations').1
      have htailDestinations : (tail.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hdestinations').2
      have htailNoSource : ∀ move, move ∈ tail →
          move.2 ∉ tail.map Prod.fst := by
        intro move hmove hsource
        rcases List.mem_map.mp hsource with ⟨other, hother, hotherSource⟩
        apply hnoSource move (by simp [hmove])
        exact List.mem_map.mpr ⟨other, by simp [hother], hotherSource⟩
      have htailNoScratch : ∀ move, move ∈ tail →
          move.1 ≠ head.1 := by
        intro move hmove heq
        apply hheadNotDestination
        exact List.mem_map.mpr ⟨move, hmove, heq⟩
      have hremoved :
          wordMoveRegisterRemoveDestination head.1 (head :: tail) = tail := by
        simp only [wordMoveRegisterRemoveDestination, List.filter_cons]
        have hhead : (head.1 != head.1) = false := by simp
        rw [hhead]
        have htailFilter :
            List.filter (fun move => move.1 != head.1) tail = tail := by
          have hfilter : ∀ xs : List (Nat × Nat),
              (∀ move, move ∈ xs → move.1 ≠ head.1) →
              List.filter (fun move => move.1 != head.1) xs = xs := by
            intro xs hxs
            induction xs with
            | nil => rfl
            | cons move xs ihxs =>
                have hmove := hxs move (by simp)
                have htail : ∀ other, other ∈ xs → other.1 ≠ head.1 := by
                  intro other hother
                  exact hxs other (by simp [hother])
                simp [hmove, ihxs htail]
          exact hfilter tail htailNoScratch
        exact htailFilter
      have hheadReady : head.2 ∉ head.1 :: tail.map Prod.fst := by
        simpa only [List.map_cons] using hnoSource head (by simp)
      have hheadReady' :
          head.2 ∉ wordMoveRegisterDestinations (head :: tail) := by
        simpa [wordMoveRegisterDestinations] using hheadReady
      have hready :
          wordMoveRegisterReady (wordMoveRegisterDestinations (head :: tail))
              (head :: tail) =
            some head := by
        simp [wordMoveRegisterReady, hheadReady']
      have hready' :
          wordMoveRegisterReady
              (head.1 :: tail.map (fun move => move.1)) (head :: tail) =
            some head := by
        simpa [wordMoveRegisterDestinations] using hready
      have htailNoScratch31 : ∀ move, move ∈ tail →
          (move.1 == 31 || move.2 == 31) = false := by
        intro move hmove
        have hmoveValid := htailValid move hmove
        simp [hmoveValid.2.2.1, hmoveValid.2.2.2]
      have hany :
          (head :: tail).any (fun move => move.1 == 31 || move.2 == 31) = false := by
        have hanyOf : ∀ xs : List (Nat × Nat),
            (∀ move, move ∈ xs → (move.1 == 31 || move.2 == 31) = false) →
            xs.any (fun move => move.1 == 31 || move.2 == 31) = false := by
          intro xs hxs
          induction xs with
          | nil => rfl
          | cons move xs ihxs =>
              simp [hxs move (by simp), ihxs
                (fun other hother => hxs other (by simp [hother]))]
        have htailAny := hanyOf tail htailNoScratch31
        have hheadNoScratch :
            (head.1 == 31 || head.2 == 31) = false := by
          simp [hheadValid.2.2.1, hheadValid.2.2.2]
        simp [hheadNoScratch, htailAny]
      have hheadCode :
          wordExpToInstructions (width := width) head.1 (.var head.2) =
            some (wordMoveInstructionList (width := width) head) := by
        simp [wordMoveInstructionList, wordExpToInstructions,
          wordExpToInstruction, registerOfNat, hheadValid.1, hheadValid.2.1]
      have htailResult := ih htailDestinations htailNoSource htailValid
      have htailAux :
          wordMoveToInstructionsAux (tail.length + 1) tail =
            some (tail.flatMap (wordMoveInstructionList (width := width))) := by
        simpa [wordMoveToInstructions] using htailResult
      have hheadCodeAux :
          (Option.map (fun instruction => [instruction])
              (wordExpToInstruction (width := width) head.1 (.var head.2))) =
            some (wordMoveInstructionList (width := width) head) := by
        simp [wordMoveInstructionList, wordExpToInstructions,
          wordExpToInstruction, registerOfNat, hheadValid.1, hheadValid.2.1]
      rw [wordMoveToInstructions, wordMoveToInstructionsAux]
      simp [wordMoveRegisterDestinations, hdestinations', hready', hany, hremoved,
        hheadCodeAux, htailAux]

end Flapjack.RiscV
