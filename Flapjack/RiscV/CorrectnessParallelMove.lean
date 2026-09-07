import Flapjack.RiscV.CorrectnessColour
import Flapjack.RiscV.ParallelMoveCorrectness

/-!
Semantic simulation for the acyclic parallel moves used by full-SSA formal
entry.  The instruction-list theorem is kept separate from the state
relation, so the executable move compiler can also be reused by backend
clients that do not use register coloring.
-/

namespace Flapjack.RiscV

def wordColourMove (colour : Nat → Nat) (move : Nat × Nat) : Nat × Nat :=
  (colour move.1, colour move.2)

theorem wordColourStateRelation_executeAcyclicMoveList [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (moves : List (Nat × Nat))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hcolourNoScratch : ∀ move, move ∈ moves →
      colour move.1 ≠ 31 ∧ colour move.2 ≠ 31) :
    ∃ source' target',
      executeInstructions source
          (moves.flatMap (wordMoveInstructionList (width := width))) = source' ∧
      executeInstructions target
          ((moves.map (wordColourMove colour)).flatMap
            (wordMoveInstructionList (width := width))) = target' ∧
      WordColourStateRelation colour source' target' := by
  induction moves generalizing source target with
  | nil =>
      exact ⟨source, target, rfl, rfl, hrelation⟩
  | cons head tail ih =>
      have hheadValid := hvalid head (by simp)
      have htailValid : ∀ move, move ∈ tail →
          move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
        intro move hmove
        exact hvalid move (by simp [hmove])
      have hheadColour := hcolourNoScratch head (by simp)
      have htailColour : ∀ move, move ∈ tail →
          colour move.1 ≠ 31 ∧ colour move.2 ≠ 31 := by
        intro move hmove
        exact hcolourNoScratch move (by simp [hmove])
      have hsourceCode :
          wordMoveInstructionList (width := width) head =
            [.addi ⟨head.1, hheadValid.1⟩ ⟨head.2, hheadValid.2.1⟩ 0] := by
        simp [wordMoveInstructionList, wordExpToInstructions,
          wordExpToInstruction, registerOfNat, hheadValid.1, hheadValid.2.1]
      have htargetCode :
          wordMoveInstructionList (width := width) (wordColourMove colour head) =
            [.addi ⟨colour head.1, valid head.1 hheadValid.1⟩
              ⟨colour head.2, valid head.2 hheadValid.2.1⟩ 0] := by
        simp [wordMoveInstructionList, wordColourMove, wordExpToInstructions,
          wordExpToInstruction, registerOfNat, valid head.1 hheadValid.1,
          valid head.2 hheadValid.2.1]
      have hstep := wordColourStateRelation_executeAddi colour valid injective
        colourZero source target hrelation head.1 head.2 hheadValid.1 hheadValid.2.1
      rcases ih (source := execute source
          (.addi ⟨head.1, hheadValid.1⟩ ⟨head.2, hheadValid.2.1⟩ 0))
        (target := execute target
          (.addi ⟨colour head.1, valid head.1 hheadValid.1⟩
            ⟨colour head.2, valid head.2 hheadValid.2.1⟩ 0))
        hstep htailValid htailColour with
        ⟨source', target', hsource', htarget', hrelation'⟩
      refine ⟨source', target', ?_, ?_, hrelation'⟩
      · rw [List.flatMap_cons, hsourceCode, executeInstructions_append]
        simpa using hsource'
      · rw [List.map_cons, List.flatMap_cons, htargetCode, executeInstructions_append]
        simpa [wordColourMove] using htarget'

theorem evalWordProg_moveAcyclic_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (moves : List (Nat × Nat))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves → move.2 ∉ moves.map Prod.fst)
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hcolourNoScratch : ∀ move, move ∈ moves →
      colour move.1 ≠ 31 ∧ colour move.2 ≠ 31) :
    ∃ source' target',
      evalWordProg source (.move 1 moves) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.move 1 moves)) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hsourceCompile := wordMoveToInstructions_of_no_source_destination
    (width := width) moves hdestinations hnoSource hvalid
  have mapNodup : ∀ names : List Nat, names.Nodup →
      (names.map colour).Nodup := by
    intro names hnames
    induction names with
    | nil => simp
    | cons name names ih =>
        have hnames' := List.nodup_cons.mp hnames
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rcases List.mem_map.mp hmem with ⟨other, hother, heq⟩
          apply hnames'.1
          have hother' : other = name := injective heq
          exact hother' ▸ hother
        · exact ih hnames'.2
  have hcolourDestinations :
      ((moves.map (wordColourMove colour)).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def, wordColourMove] using
      mapNodup (moves.map Prod.fst) hdestinations
  have hcolourNoSource : ∀ move, move ∈ moves.map (wordColourMove colour) →
      move.2 ∉ (moves.map (wordColourMove colour)).map Prod.fst := by
    intro move hmove hsource
    rcases List.mem_map.mp hmove with ⟨original, horiginal, rfl⟩
    rcases List.mem_map.mp hsource with ⟨coloredOther, hcoloredOther, heq⟩
    rcases List.mem_map.mp hcoloredOther with ⟨other, hother, rfl⟩
    have heq' : other.1 = original.2 :=
      injective (by simpa [wordColourMove] using heq)
    apply hnoSource original horiginal
    exact List.mem_map.mpr ⟨other, hother, heq'⟩
  have hcolourValid : ∀ move, move ∈ moves.map (wordColourMove colour) →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
    intro move hmove
    rcases List.mem_map.mp hmove with ⟨original, horiginal, rfl⟩
    have horiginalValid := hvalid original horiginal
    have hcolour := hcolourNoScratch original horiginal
    exact ⟨valid original.1 horiginalValid.1,
      valid original.2 horiginalValid.2.1, hcolour.1, hcolour.2⟩
  have htargetCompile := wordMoveToInstructions_of_no_source_destination
    (width := width) (moves.map (wordColourMove colour)) hcolourDestinations
    hcolourNoSource hcolourValid
  have hcolourMoves :
      moves.map (fun move => (colour move.1, colour move.2)) =
        moves.map (wordColourMove colour) := by
    induction moves with
    | nil => rfl
    | cons move moves ih =>
        rfl
  rcases wordColourStateRelation_executeAcyclicMoveList colour valid injective
      colourZero source target hrelation moves hvalid hcolourNoScratch with
    ⟨source', target', hsourceExec, htargetExec, hrelation'⟩
  refine ⟨source', target', ?_, ?_, hrelation'⟩
  · rw [evalWordProg, hsourceCompile]
    exact congrArg some hsourceExec
  · simp only [evalWordProg, wordApplyColour]
    rw [hcolourMoves, htargetCompile]
    exact congrArg some htargetExec

end Flapjack.RiscV
