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
  · simp [nextPc, hrelation.pc]
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

theorem evalWordProg_assignConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name : Nat) (value : Word width) (hname : name < 32) :
    ∃ source' target',
      evalWordProg source (.assign name (.const value)) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.assign name (.const value))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  have hread : readRegister source 0 = readRegister target 0 := by
    simpa [colourZero] using
      hrelation.register 0 (by omega) (by simp [colourZero])
  have hvalue :
      readRegister source 0 + value = readRegister target 0 + value := by
    rw [hread]
  have hsourceEval :
      evalWordProg source (.assign name (.const value)) =
        some (execute source (.addi ⟨name, hname⟩ 0 value)) := by
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hname, executeInstructions]
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour (.assign name (.const value))) =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩ 0 value)) := by
    simp [wordApplyColour, wordApplyColourExp, evalWordProg,
      wordExpToInstructions, wordExpToInstruction, registerOfNat,
      valid name hname, executeInstructions]
  have hstate := wordColourStateRelation_writeRegister colour valid
    injective colourZero {source with pc := nextPc source}
    {target with pc := nextPc target} hnext name hname
    (readRegister source 0 + value) (readRegister target 0 + value) hvalue
  exact ⟨_, _, hsourceEval, htargetEval, by
    simpa [execute, colourZero] using hstate⟩

theorem wordColourStateRelation_executeBinary
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name left right : Nat)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .add ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .sub => .sub ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .and => .and ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .or => .or ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .xor => .xor ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .add => .add ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .sub => .sub ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .and => .and ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .or => .or ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .xor => .xor ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ +
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ +
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | sub =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ -
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ -
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | and =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ &&&
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ &&&
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ |||
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ |||
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ ^^^
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ ^^^
            readRegister target ⟨colour right, valid right hright⟩) hvalue)

theorem evalWordProg_assignBinaryVarVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name left right : Nat)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.op operator [.var left, .var right])) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.op operator [.var left, .var right]))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | add =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .add [.var left, .var right])) =
            some (execute source (.add ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .add [.var left, .var right]))) =
            some (execute target
              (.add ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .add name left right hname hleft hright⟩
  | sub =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .sub [.var left, .var right])) =
            some (execute source (.sub ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .sub [.var left, .var right]))) =
            some (execute target
              (.sub ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .sub name left right hname hleft hright⟩
  | and =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .and [.var left, .var right])) =
            some (execute source (.and ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .and [.var left, .var right]))) =
            some (execute target
              (.and ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .and name left right hname hleft hright⟩
  | or =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .or [.var left, .var right])) =
            some (execute source (.or ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .or [.var left, .var right]))) =
            some (execute target
              (.or ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .or name left right hname hleft hright⟩
  | xor =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .xor [.var left, .var right])) =
            some (execute source (.xor ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .xor [.var left, .var right]))) =
            some (execute target
              (.xor ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .xor name left right hname hleft hright⟩

theorem wordColourStateRelation_executeImmediateBinary
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name sourceName : Nat) (value : Word width)
    (hname : name < 32) (hsource : sourceName < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .sub => .addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ (0 - value)
        | .and => .andi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .or => .ori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .xor => .xori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value))
      (execute target (match operator with
        | .add => .addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .sub => .addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ (0 - value)
        | .and => .andi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .or => .ori ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .xor => .xori ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ + value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ + value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + value) hvalue)
  | sub =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ + (0 - value) =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ +
              (0 - value) := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ + (0 - value))
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ +
            (0 - value)) hvalue)
  | and =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ &&& value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ &&& value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ||| value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ ||| value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ^^^ value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ ^^^ value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value) hvalue)

theorem evalWordProg_assignBinaryVarConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name sourceName : Nat) (value : Word width)
    (hname : name < 32) (hsource : sourceName < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.op operator [.var sourceName, .const value])) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.op operator [.var sourceName, .const value]))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | add =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .add [.var sourceName, .const value])) =
            some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .add [.var sourceName, .const value]))) =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .add name sourceName value hname hsource⟩
  | sub =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .sub [.var sourceName, .const value])) =
            some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ (0 - value))) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .sub [.var sourceName, .const value]))) =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ (0 - value))) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .sub name sourceName value hname hsource⟩
  | and =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .and [.var sourceName, .const value])) =
            some (execute source (.andi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .and [.var sourceName, .const value]))) =
            some (execute target
              (.andi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .and name sourceName value hname hsource⟩
  | or =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .or [.var sourceName, .const value])) =
            some (execute source (.ori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .or [.var sourceName, .const value]))) =
            some (execute target
              (.ori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .or name sourceName value hname hsource⟩
  | xor =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .xor [.var sourceName, .const value])) =
            some (execute source (.xori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .xor [.var sourceName, .const value]))) =
            some (execute target
              (.xori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .xor name sourceName value hname hsource⟩

theorem wordColourStateRelation_executeSllForRotate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (.sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (.sll ⟨colour name, valid name hname⟩
        ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  have hvalue :
      BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
          (shiftAmount (readRegister source ⟨right, hright⟩)) =
        BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
          (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
    rw [hrelation.register left hleft (valid left hleft),
      hrelation.register right hright (valid right hright)]
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
        (shiftAmount (readRegister source ⟨right, hright⟩)))
      (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
        (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)

theorem wordColourStateRelation_executeSrlForRotate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (.srl ⟨colour name, valid name hname⟩
        ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  have hvalue :
      BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
          (shiftAmount (readRegister source ⟨right, hright⟩)) =
        BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
          (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
    rw [hrelation.register left hleft (valid left hleft),
      hrelation.register right hright (valid right hright)]
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
        (shiftAmount (readRegister source ⟨right, hright⟩)))
      (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
        (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)

theorem wordColourStateRelation_executeRotateRight
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourScratch : colour 31 = 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) (hnameScratch : name ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    WordColourStateRelation colour
      (executeInstructions source
        [.ori 31 0 (BitVec.ofNat width width), .sub 31 31 ⟨right, hright⟩,
          .sll 31 ⟨left, hleft⟩ 31, .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
          .or ⟨name, hname⟩ ⟨name, hname⟩ 31])
      (executeInstructions target
        [.ori ⟨colour 31, valid 31 (by omega)⟩ ⟨colour 0, valid 0 (by omega)⟩
            (BitVec.ofNat width width),
          .sub ⟨colour 31, valid 31 (by omega)⟩ ⟨colour 31, valid 31 (by omega)⟩
            ⟨colour right, valid right hright⟩,
          .sll ⟨colour 31, valid 31 (by omega)⟩ ⟨colour left, valid left hleft⟩
            ⟨colour 31, valid 31 (by omega)⟩,
          .srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
            ⟨colour right, valid right hright⟩,
          .or ⟨colour name, valid name hname⟩ ⟨colour name, valid name hname⟩
            ⟨colour 31, valid 31 (by omega)⟩]) := by
  have hnameColourScratch : colour name ≠ 31 := by
    intro h
    apply hnameScratch
    apply injective
    simpa [colourScratch] using h
  have hleftColourScratch : colour left ≠ 31 := by
    intro h
    apply hleftScratch
    apply injective
    simpa [colourScratch] using h
  have hrightColourScratch : colour right ≠ 31 := by
    intro h
    apply hrightScratch
    apply injective
    simpa [colourScratch] using h
  have h1 := wordColourStateRelation_executeImmediateBinary colour valid
    injective colourZero source target hrelation .or 31 0 (BitVec.ofNat width width)
      (by omega) (by omega)
  have h1' :
      WordColourStateRelation colour
        (execute source (.ori 31 0 (BitVec.ofNat width width)))
        (execute target (.ori 31 0 (BitVec.ofNat width width))) := by
    simpa [colourScratch, colourZero] using h1
  have h2 := wordColourStateRelation_executeBinary colour valid injective colourZero
    (execute source (.ori 31 0 (BitVec.ofNat width width)))
    (execute target (.ori 31 0 (BitVec.ofNat width width))) h1' .sub 31 31 right
      (by omega) (by omega) hright
  have h2' :
      WordColourStateRelation colour
        (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨right, hright⟩))
        (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨colour right, valid right hright⟩)) := by
    simpa [colourScratch] using h2
  have h3 := wordColourStateRelation_executeSllForRotate colour valid injective colourZero
    (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
      (.sub 31 31 ⟨right, hright⟩))
    (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
      (.sub 31 31 ⟨colour right, valid right hright⟩)) h2' 31 left 31
      (by omega) hleft (by omega)
  have h3' :
      WordColourStateRelation colour
        (execute
          (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
            (.sub 31 31 ⟨right, hright⟩))
          (.sll 31 ⟨left, hleft⟩ 31))
        (execute
          (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
            (.sub 31 31 ⟨colour right, valid right hright⟩))
          (.sll 31 ⟨colour left, valid left hleft⟩ 31)) := by
    simpa [colourScratch] using h3
  have h4 := wordColourStateRelation_executeSrlForRotate colour valid injective colourZero
    (execute
      (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
        (.sub 31 31 ⟨right, hright⟩))
      (.sll 31 ⟨left, hleft⟩ 31))
    (execute
      (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
        (.sub 31 31 ⟨colour right, valid right hright⟩))
      (.sll 31 ⟨colour left, valid left hleft⟩ 31)) h3' name left right
      hname hleft hright
  have h4' :
      WordColourStateRelation colour
        (execute
          (execute
            (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
              (.sub 31 31 ⟨right, hright⟩))
            (.sll 31 ⟨left, hleft⟩ 31))
          (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
        (execute
          (execute
            (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
              (.sub 31 31 ⟨colour right, valid right hright⟩))
            (.sll 31 ⟨colour left, valid left hleft⟩ 31))
          (.srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
            ⟨colour right, valid right hright⟩)) := by
    simpa [colourScratch] using h4
  have h5 := wordColourStateRelation_executeBinary colour valid injective colourZero
    (execute
      (execute
        (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨right, hright⟩))
        (.sll 31 ⟨left, hleft⟩ 31))
      (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
    (execute
      (execute
        (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨colour right, valid right hright⟩))
        (.sll 31 ⟨colour left, valid left hleft⟩ 31))
      (.srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
        ⟨colour right, valid right hright⟩)) h4' .or name name 31
      (by omega) hname (by omega)
  simpa [executeInstructions, colourScratch, colourZero] using h5

theorem evalWordProg_assignRotateRight_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourScratch : colour 31 = 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) (hnameScratch : name ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift .ror (.var left) (.var right))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift .ror (.var left) (.var right)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hsourceEval :
      evalWordProg source (.assign name (.shift .ror (.var left) (.var right))) =
        some (executeInstructions source
          [.ori 31 0 (BitVec.ofNat width width), .sub 31 31 ⟨right, hright⟩,
            .sll 31 ⟨left, hleft⟩ 31, .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
            .or ⟨name, hname⟩ ⟨name, hname⟩ 31]) := by
    simp [evalWordProg, wordExpToInstructions, 
      registerOfNat, hname, hleft, hright, hnameScratch, hleftScratch,
      hrightScratch, executeInstructions]
  have hnameColourScratch : colour name ≠ 31 := by
    intro h
    apply hnameScratch
    apply injective
    simpa [colourScratch] using h
  have hleftColourScratch : colour left ≠ 31 := by
    intro h
    apply hleftScratch
    apply injective
    simpa [colourScratch] using h
  have hrightColourScratch : colour right ≠ 31 := by
    intro h
    apply hrightScratch
    apply injective
    simpa [colourScratch] using h
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift .ror (.var left) (.var right)))) =
        some (executeInstructions target
          [.ori 31 0 (BitVec.ofNat width width),
            .sub 31 31 ⟨colour right, valid right hright⟩,
            .sll 31 ⟨colour left, valid left hleft⟩ 31,
            .srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
              ⟨colour right, valid right hright⟩,
            .or ⟨colour name, valid name hname⟩ ⟨colour name, valid name hname⟩ 31]) := by
    simp [evalWordProg, wordApplyColour, wordApplyColourExp,
      wordExpToInstructions, registerOfNat,
      
      valid name hname, valid left hleft, valid right hright,
      hnameColourScratch, hleftColourScratch, hrightColourScratch,
      executeInstructions]
  refine ⟨_, _, hsourceEval, htargetEval, ?_⟩
  simpa [colourScratch, colourZero] using
    (wordColourStateRelation_executeRotateRight colour valid injective colourZero
      colourScratch source target hrelation name left right hname hleft hright
      hnameScratch hleftScratch hrightScratch)

theorem wordColourStateRelation_executeShiftImmediate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left : Nat) (amount : Word width)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .slli ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .lsr => .srli ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .asr => .srai ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .ror => .slli ⟨name, hname⟩ ⟨left, hleft⟩ amount))
      (execute target (match operator with
        | .lsl => .slli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .lsr => .srli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .asr => .srai ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .ror => .slli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.sshiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_assignShiftVarConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left : Nat) (amount : Word width)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift operator (.var left) (.const amount))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift operator (.var left) (.const amount)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsl (.var left) (.const amount))) =
            some (execute source (.slli ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsl (.var left) (.const amount)))) =
            some (execute target
              (.slli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .lsl name left amount hoperator hname hleft⟩
  | lsr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsr (.var left) (.const amount))) =
            some (execute source (.srli ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsr (.var left) (.const amount)))) =
            some (execute target
              (.srli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .lsr name left amount hoperator hname hleft⟩
  | asr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .asr (.var left) (.const amount))) =
            some (execute source (.srai ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .asr (.var left) (.const amount)))) =
            some (execute target
              (.srai ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .asr name left amount hoperator hname hleft⟩
  | ror => exact (hoperator rfl).elim

theorem wordColourStateRelation_executeShift
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .lsr => .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .asr => .sra ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .ror => .sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .lsl => .sll ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .lsr => .srl ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .asr => .sra ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .ror => .sll ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.sshiftRight (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_assignShiftVarVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift operator (.var left) (.var right))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift operator (.var left) (.var right)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsl (.var left) (.var right))) =
            some (execute source (.sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsl (.var left) (.var right)))) =
            some (execute target
              (.sll ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .lsl name left right hoperator hname hleft hright⟩
  | lsr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsr (.var left) (.var right))) =
            some (execute source (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsr (.var left) (.var right)))) =
            some (execute target
              (.srl ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .lsr name left right hoperator hname hleft hright⟩
  | asr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .asr (.var left) (.var right))) =
            some (execute source (.sra ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .asr (.var left) (.var right)))) =
            some (execute target
              (.sra ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .asr name left right hoperator hname hleft hright⟩
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_moveOne_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32) (hsource : sourceName < 32)
    (hname31 : name ≠ 31) (hsource31 : sourceName ≠ 31)
    (hcolourName31 : colour name ≠ 31) (hcolourSource31 : colour sourceName ≠ 31)
    (hne : name ≠ sourceName) :
    ∃ source' target',
      evalWordProg source (.move 1 [(name, sourceName)]) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.move 1 [(name, sourceName)])) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hne' : sourceName ≠ name := Ne.symm hne
  have hcolourNe : colour name ≠ colour sourceName := fun heq =>
    hne (injective heq)
  have hcolourNe' : colour sourceName ≠ colour name := Ne.symm hcolourNe
  have hsourceMove :
      evalWordProg source (.move 1 [(name, sourceName)]) =
        evalWordProg source (.assign name (.var sourceName)) := by
    simp [evalWordProg, wordMoveToInstructions, wordMoveToInstructionsAux,
      wordMoveRegisterDestinations, wordMoveRegisterReady,
      wordMoveRegisterRemoveDestination, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hname, hsource, hname31, hsource31,
      hne']
  have htargetMove :
      evalWordProg target
          (wordApplyColour colour (.move 1 [(name, sourceName)])) =
        evalWordProg target
          (.assign (colour name) (.var (colour sourceName))) := by
    simp [evalWordProg, wordApplyColour, wordMoveToInstructions,
      wordMoveToInstructionsAux, wordMoveRegisterDestinations,
      wordMoveRegisterReady, wordMoveRegisterRemoveDestination,
      wordExpToInstructions, wordExpToInstruction, registerOfNat,
      valid name hname, valid sourceName hsource, hcolourName31,
      hcolourSource31, hcolourNe']
  rcases evalWordProg_assignVar_applyColour colour valid injective colourZero
      source target hrelation name sourceName hname hsource with
    ⟨source', target', hsource', htarget', hrelation'⟩
  refine ⟨source', target', hsourceMove.trans hsource', ?_, hrelation'⟩
  exact htargetMove.trans (by simpa [wordApplyColour, wordApplyColourExp]
    using htarget')

inductive WordVarStraightLine (width : Nat) : WordProg (Word width) → Prop where
  | skip : WordVarStraightLine width .skip
  | assign (name source : Nat) (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.var source))
  | assignConst (name : Nat) (value : Word width) (hname : name < 32) :
      WordVarStraightLine width (.assign name (.const value))
  | assignBinary (operator : BinOp) (name left right : Nat)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var left, .var right]))
  | assignImmediate (operator : BinOp) (name source : Nat) (value : Word width)
      (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var source, .const value]))
  | assignShift (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.var right)))
  | assignShiftImmediate (operator : Shift) (name left : Nat) (amount : Word width)
      (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.const amount)))
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
  | assignConst name value hname =>
      exact evalWordProg_assignConst_applyColour colour valid injective colourZero
        source target hrelation name value hname
  | assignBinary operator name left right hname hleft hright =>
      exact evalWordProg_assignBinaryVarVar_applyColour colour valid injective colourZero
        source target hrelation operator name left right hname hleft hright
  | assignImmediate operator name sourceName value hname hsource =>
      exact evalWordProg_assignBinaryVarConst_applyColour colour valid injective colourZero
        source target hrelation operator name sourceName value hname hsource
  | assignShift operator name left right hoperator hname hleft hright =>
      exact evalWordProg_assignShiftVarVar_applyColour colour valid injective colourZero
        source target hrelation operator name left right hoperator hname hleft hright
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      exact evalWordProg_assignShiftVarConst_applyColour colour valid injective colourZero
        source target hrelation operator name left amount hoperator hname hleft
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      rcases ihFirst source target hrelation with
        ⟨firstSource, firstTarget, hfirstSource, hfirstTarget, hfirstRelation⟩
      rcases ihSecond firstSource firstTarget hfirstRelation with
        ⟨secondSource, secondTarget, hsecondSource, hsecondTarget, hsecondRelation⟩
      refine ⟨secondSource, secondTarget, ?_, ?_, hsecondRelation⟩
      · simp [evalWordProg, hfirstSource, hsecondSource]
      · simp [evalWordProg, wordApplyColour, hfirstTarget, hsecondTarget]

end Flapjack.RiscV
