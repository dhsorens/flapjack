import Flapjack.RiscV.AllocatorCorrectness

/-!
Correctness of applying a register colouring to a small, executable Word
fragment. This is the first whole-program simulation statement for allocator
output: it covers straight-line programs made from `skip`, variable-to-
variable assignments, and sequencing.
-/

namespace Flapjack.RiscV

def wordColourValid (colour : Nat → Nat) : Prop :=
  ∀ name, name < 32 → colour name < 32

structure WordColourStateRelation (colour : Nat → Nat) [NeZero width]
    (source target : State width) : Prop where
  pc : source.pc = target.pc
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode
  register : ∀ (name : Nat) (hname : name < 32)
      (hcolour : colour name < 32),
    readRegister source ⟨name, hname⟩ =
      readRegister target ⟨colour name, hcolour⟩

theorem wordColourStateRelation_nextPc
    (colour : Nat → Nat) (_valid : wordColourValid colour)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target) :
    WordColourStateRelation colour
      {source with pc := nextPc source} {target with pc := nextPc target} := by
  constructor
  · simpa [nextPc, hrelation.pc]
  · exact hrelation.memory
  · exact hrelation.privilege
  · exact hrelation.mode
  · intro name hname hcolour
    exact hrelation.register name hname hcolour

theorem wordColourStateRelation_writeRegister
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name : Nat) (hname : name < 32) (value targetValue : Word width)
    (hvalue : value = targetValue) :
    WordColourStateRelation colour
      (writeRegister source ⟨name, hname⟩ value)
      (writeRegister target ⟨colour name, valid name hname⟩ targetValue) := by
  by_cases hzero : name = 0
  · have hcolourZero : colour name = 0 := by simpa [hzero] using colourZero
    simpa [writeRegister, hzero, hcolourZero, colourZero] using hrelation
  have hsourceNonzero : (⟨name, hname⟩ : Fin 32) ≠ 0 := by
    intro h
    exact hzero (congrArg Fin.val h)
  have hcolourNonzero : colour name ≠ 0 := by
    intro h
    apply hzero
    apply injective
    simpa [colourZero] using h
  have htargetNonzero :
      (⟨colour name, valid name hname⟩ : Fin 32) ≠ 0 := by
    intro h
    exact hcolourNonzero (congrArg Fin.val h)
  constructor
  · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
    exact hrelation.pc
  · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
    exact hrelation.memory
  · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
    exact hrelation.privilege
  · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
    exact hrelation.mode
  · intro current hcurrent hcolour
    by_cases hsame : current = name
    · subst current
      have hsourceEq :
          (⟨name, hcurrent⟩ : Fin 32) = ⟨name, hname⟩ := by
        apply Fin.ext
        rfl
      have htargetEq :
          (⟨colour name, hcolour⟩ : Fin 32) =
            ⟨colour name, valid name hname⟩ := by
        apply Fin.ext
        rfl
      simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
        readRegister]
      simp only [if_true]
      exact hvalue
    · have htargetSame :
          (⟨colour current, hcolour⟩ : Fin 32) ≠
            (⟨colour name, valid name hname⟩ : Fin 32) := by
          intro h
          apply hsame
          apply injective
          exact congrArg Fin.val h
      have hsourceCurrent :
          (⟨current, hcurrent⟩ : Fin 32) ≠ ⟨name, hname⟩ := by
        intro h
        apply hsame
        exact congrArg Fin.val h
      simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
        readRegister]
      rw [if_neg hsourceCurrent, if_neg htargetSame]
      exact hrelation.register current hcurrent hcolour

theorem wordColourStateRelation_executeAddi
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32)
    (hsource : sourceName < 32) :
    WordColourStateRelation colour
      (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0))
      (execute target
        (.addi ⟨colour name, valid name hname⟩
          ⟨colour sourceName, valid sourceName hsource⟩ 0)) := by
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  have hvalue :
      readRegister source ⟨sourceName, hsource⟩ + 0 =
        readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + 0 := by
    rw [hrelation.register sourceName hsource (valid sourceName hsource)]
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (readRegister source ⟨sourceName, hsource⟩ + 0)
      (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + 0)
      hvalue)

theorem evalWordProg_assignVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32) (hsource : sourceName < 32) :
    ∃ source' target',
      evalWordProg source (.assign name (.var sourceName)) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.assign name (.var sourceName))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hsourceEval :
      evalWordProg source (.assign name (.var sourceName)) =
        some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0)) := by
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hname, hsource, executeInstructions]
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour (.assign name (.var sourceName))) =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ 0)) := by
    rw [wordApplyColour_assign]
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, valid name hname, valid sourceName hsource,
      executeInstructions]
  exact ⟨_, _, hsourceEval, htargetEval,
    wordColourStateRelation_executeAddi colour valid injective colourZero
      source target hrelation name sourceName hname hsource⟩

inductive WordVarStraightLine (width : Nat) : WordProg (Word width) → Prop where
  | skip : WordVarStraightLine width .skip
  | assign (name source : Nat) (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.var source))
  | seq {first second : WordProg (Word width)} :
      WordVarStraightLine width first → WordVarStraightLine width second →
      WordVarStraightLine width (.seq first second)

theorem evalWordProg_wordVarStraightLine_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    ∃ source' target', evalWordProg source program = some source' ∧
      evalWordProg target (wordApplyColour colour program) = some target' ∧
      WordColourStateRelation colour source' target' := by
  induction hprogram generalizing source target with
  | skip =>
      exact ⟨source, target, by simp [evalWordProg],
        by simp [evalWordProg, wordApplyColour], hrelation⟩
  | assign name sourceName hname hsource =>
      exact evalWordProg_assignVar_applyColour colour valid injective colourZero
        source target hrelation name sourceName hname hsource
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      rcases ihFirst source target hrelation with
        ⟨firstSource, firstTarget, hfirstSource, hfirstTarget, hfirstRelation⟩
      rcases ihSecond firstSource firstTarget hfirstRelation with
        ⟨secondSource, secondTarget, hsecondSource, hsecondTarget, hsecondRelation⟩
      refine ⟨secondSource, secondTarget, ?_, ?_, hsecondRelation⟩
      · simp [evalWordProg, hfirstSource, hsecondSource]
      · simp [evalWordProg, wordApplyColour, hfirstTarget, hsecondTarget]

end Flapjack.RiscV
