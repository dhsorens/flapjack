import Flapjack.RiscV.Backend
import Flapjack.RiscV.CorrectnessBackend

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

theorem executeWordMove_read_destination [NeZero width]
    (state : State width) (destination source : Nat)
    (hdestination : destination < 32) (hsource : source < 32)
    (hdestinationNonzero : destination ≠ 0) :
    readRegister
        (executeInstructions state
          (wordMoveInstructionList (width := width) (destination, source)))
        ⟨destination, hdestination⟩ =
      readRegister state ⟨source, hsource⟩ := by
  simp [wordMoveInstructionList, wordExpToInstructions,
    wordExpToInstruction, registerOfNat, hdestination, hsource,
    execute, nextPc, writeRegister, readRegister, hdestinationNonzero]

theorem executeWordMove_read_other [NeZero width]
    (state : State width) (destination source other : Nat)
    (hdestination : destination < 32) (hsource : source < 32)
    (hother : other < 32) (hdestinationNonzero : destination ≠ 0)
    (hotherNe : other ≠ destination) :
    readRegister
        (executeInstructions state
          (wordMoveInstructionList (width := width) (destination, source)))
        ⟨other, hother⟩ =
      readRegister state ⟨other, hother⟩ := by
  simp [wordMoveInstructionList, wordExpToInstructions,
    wordExpToInstruction, registerOfNat, hdestination, hsource,
    execute, nextPc, writeRegister, readRegister,
    hdestinationNonzero, hotherNe]

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

theorem executeWordMoves_preserve_read [NeZero width]
    (state : State width) (moves : List (Nat × Nat)) (other : Nat)
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ moves → move.1 ≠ 0)
    (hnotDestination : ∀ move, move ∈ moves → move.1 ≠ other)
    (hother : other < 32) :
    readRegister
        (executeInstructions state
          (moves.flatMap (wordMoveInstructionList (width := width))))
        ⟨other, hother⟩ =
      readRegister state ⟨other, hother⟩ := by
  induction moves generalizing state with
  | nil => rfl
  | cons head tail ih =>
      have hheadValid := hvalid head (by simp)
      have htailValid : ∀ move, move ∈ tail →
          move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
        intro move hmove
        exact hvalid move (by simp [hmove])
      have hheadNonzero := hdestNonzero head (by simp)
      have htailNonzero : ∀ move, move ∈ tail → move.1 ≠ 0 := by
        intro move hmove
        exact hdestNonzero move (by simp [hmove])
      have hheadNot := hnotDestination head (by simp)
      have htailNot : ∀ move, move ∈ tail → move.1 ≠ other := by
        intro move hmove
        exact hnotDestination move (by simp [hmove])
      rw [List.flatMap_cons, executeInstructions_append]
      rw [ih (state := executeInstructions state
          (wordMoveInstructionList (width := width) head))
        (hvalid := htailValid) (hdestNonzero := htailNonzero)
        (hnotDestination := htailNot)]
      exact executeWordMove_read_other state head.1 head.2 other
        hheadValid.1 hheadValid.2.1 hother hheadNonzero (Ne.symm hheadNot)

theorem executeWordMoves_preserves_sources [NeZero width]
    (state : State width) (moves : List (Nat × Nat))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves → move.2 ∉ moves.map Prod.fst)
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ moves → move.1 ≠ 0) :
    ∀ move (hmove : move ∈ moves),
      readRegister
          (executeInstructions state
            (moves.flatMap (wordMoveInstructionList (width := width))))
          ⟨move.1, (hvalid move hmove).1⟩ =
        readRegister state ⟨move.2, (hvalid move hmove).2.1⟩ := by
  induction moves generalizing state with
  | nil =>
      intro move hmove
      cases hmove
  | cons head tail ih =>
      intro move hmove
      have hheadValid := hvalid head (by simp)
      have htailValid : ∀ other, other ∈ tail →
          other.1 < 32 ∧ other.2 < 32 ∧ other.1 ≠ 31 ∧ other.2 ≠ 31 := by
        intro other hother
        exact hvalid other (by simp [hother])
      have hheadNonzero := hdestNonzero head (by simp)
      have htailNonzero : ∀ other, other ∈ tail → other.1 ≠ 0 := by
        intro other hother
        exact hdestNonzero other (by simp [hother])
      have hdestinations' : (head.1 :: tail.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hdestinations
      have htailDestinations : (tail.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hdestinations').2
      have htailNoSource : ∀ other, other ∈ tail →
          other.2 ∉ tail.map Prod.fst := by
        intro other hother hsource
        rcases List.mem_map.mp hsource with ⟨another, hanother, heq⟩
        apply hnoSource other (by simp [hother])
        exact List.mem_map.mpr ⟨another, by simp [hanother], heq⟩
      have hheadNotTailDestination : ∀ other, other ∈ tail →
          other.1 ≠ head.1 := by
        intro other hother heq
        apply (List.nodup_cons.mp hdestinations').1
        exact List.mem_map.mpr ⟨other, hother, heq⟩
      have htailNoSourceHead : ∀ other, other ∈ tail →
          other.2 ≠ head.1 := by
        intro other hother heq
        apply hnoSource other (by simp [hother])
        exact List.mem_map.mpr ⟨head, by simp, heq.symm⟩
      have hheadNoSource : head.2 ∉ head.1 :: tail.map Prod.fst := by
        simpa only [List.map_cons] using hnoSource head (by simp)
      have hheadNoSourceTail : head.2 ∉ tail.map Prod.fst := by
        intro hmem
        exact hheadNoSource (by simp [hmem])
      rcases List.mem_cons.mp hmove with hmove | hmove
      · subst move
        rw [List.flatMap_cons, executeInstructions_append]
        have hpreserve := executeWordMoves_preserve_read
          (executeInstructions state
            (wordMoveInstructionList (width := width) head)) tail head.1
          htailValid htailNonzero hheadNotTailDestination hheadValid.1
        rw [hpreserve]
        exact executeWordMove_read_destination state head.1 head.2
          hheadValid.1 hheadValid.2.1 hheadNonzero
      · have hresult := ih (state := executeInstructions state
            (wordMoveInstructionList (width := width) head))
          htailDestinations htailNoSource htailValid htailNonzero move hmove
        rw [List.flatMap_cons, executeInstructions_append]
        rw [hresult]
        exact executeWordMove_read_other state head.1 head.2 move.2
          hheadValid.1 hheadValid.2.1 (hvalid move (by simp [hmove])).2.1
          hheadNonzero (htailNoSourceHead move hmove)

def wordReadRegisterNat [NeZero width] (state : State width) (name : Nat) :
    Option (Word width) :=
  do
    let register ← registerOfNat name
    pure (readRegister state register)

theorem wordReadRegisterNat_mapM_zip [NeZero width]
    (source target : State width) (destinations sources : List Nat)
    (hpair : ∀ move, move ∈ destinations.zip sources →
      wordReadRegisterNat target move.1 =
        wordReadRegisterNat source move.2)
    (hlength : destinations.length = sources.length) :
    List.mapM (wordReadRegisterNat target) destinations =
      List.mapM (wordReadRegisterNat source) sources := by
  induction destinations generalizing sources with
  | nil =>
      cases sources with
      | nil => rfl
      | cons head tail => simp at hlength
  | cons head tail ih =>
      cases sources with
      | nil => simp at hlength
      | cons sourceHead sourceTail =>
          have hlengthTail : tail.length = sourceTail.length := by
            simp_all
          simp only [List.mapM_cons]
          rw [hpair (head, sourceHead) (by simp)]
          rw [ih (sources := sourceTail) (hlength := hlengthTail)]
          intro move hmove
          exact hpair move (by simp [hmove])

end Flapjack.RiscV
