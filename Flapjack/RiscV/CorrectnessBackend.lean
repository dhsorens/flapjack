import Flapjack.RiscV.Backend

/-!
Compositional correctness for the straight-line Word fragment.  The RISC-V
instruction runner is intentionally separate from the branch-aware `executeCode`
runner, so this theorem captures exactly the fragment whose compiler emits a
single sequential instruction list.
-/

namespace Flapjack.RiscV

inductive WordRiscVStraightLine : WordProg α → Prop where
  | skip : WordRiscVStraightLine (.skip : WordProg α)
  | move (store : Nat) (moves : List (Nat × Nat)) :
      WordRiscVStraightLine (.move store moves)
  | assign (destination : Nat) (value : WordExp α) :
      WordRiscVStraightLine (.assign destination value)
  | inst (instruction : WordInst) :
      WordRiscVStraightLine (.inst instruction)
  | store (address : WordExp α) (value : Nat) :
      WordRiscVStraightLine (.store address value)
  | seq (first second : WordProg α) :
      WordRiscVStraightLine first → WordRiscVStraightLine second →
      WordRiscVStraightLine (.seq first second)
  | locValue (destination source : Nat) :
      WordRiscVStraightLine (.locValue destination source)
  | tick : WordRiscVStraightLine (.tick : WordProg α)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordExp α) :
      WordRiscVStraightLine (.shareInst operator name address)

theorem executeInstructions_append [NeZero width] (state : State width)
    (first second : List (Instruction width)) :
    executeInstructions state (first ++ second) =
      executeInstructions (executeInstructions state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, executeInstructions]
      exact ih (execute state instruction)

theorem wordProgToRiscV_sound_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV program = some code) :
    evalWordProg state program = some (executeInstructions state code) := by
  induction hstraight generalizing state code with
  | skip =>
      have hcompile' : some ([] : List (Instruction width)) = some code := by
        simpa only [wordProgToRiscV] using hcompile
      have hcode : ([] : List (Instruction width)) = code :=
        Option.some.inj hcompile'
      subst code
      simp [evalWordProg, executeInstructions]
  | move store moves =>
      have hcompile' : wordMoveToInstructions (width := width) moves = some code := by
        simpa only [wordProgToRiscV] using hcompile
      cases h : wordMoveToInstructions (width := width) moves with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProg, h]
  | assign destination value =>
      have hcompile' : wordExpToInstructions (width := width) destination value = some code := by
        simpa only [wordProgToRiscV] using hcompile
      cases h : wordExpToInstructions (width := width) destination value with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProg, h]
  | inst instruction =>
      cases instruction with
      | arith operation =>
          have hcompile' : wordArithToInstructions (width := width) operation = some code := by
            simpa only [wordProgToRiscV] using hcompile
          cases h : wordArithToInstructions (width := width) operation with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instructions =>
              have hcode : instructions = code :=
                Option.some.inj (h.symm.trans hcompile')
              subst code
              simp [evalWordProg, h]
      | mem operator destination address =>
          have hcompile' : (wordInstToInstruction (width := width)
            (.mem operator destination address)).map (fun instruction => [instruction]) =
            some code := by
            simpa only [wordProgToRiscV] using hcompile
          cases h : wordInstToInstruction (width := width)
              (.mem operator destination address) with
          | none => rw [h] at hcompile'; cases hcompile'
          | some instruction =>
              have hcode : [instruction] = code := by
                have hcompile'' : some [instruction] = some code := by
                  simpa [h] using hcompile'
                exact Option.some.inj hcompile''
              subst code
              cases operator <;>
                cases hd : registerOfNat destination <;>
                cases ha : registerOfNat address <;>
                simp [wordInstToInstruction,
                  hd, ha] at h
              all_goals
                simp [evalWordProg, executeInstructions, hd, ha, h]
  | store address value =>
      have hcompile' : wordStoreToInstructions (width := width) address value = some code := by
        simpa only [wordProgToRiscV] using hcompile
      cases h : wordStoreToInstructions (width := width) address value with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          have h' : wordShareInstToInstructions .store value address =
              some instructions := by
            simpa [wordStoreToInstructions] using h
          simp [evalWordProg, evalWordShareInst, h']
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [wordProgToRiscV] at hcompile
      cases hfirstCompile : wordProgToRiscV first with
      | none => simp [hfirstCompile] at hcompile
      | some firstCode =>
          cases hsecondCompile : wordProgToRiscV second with
          | none => simp [hsecondCompile] at hcompile
          | some secondCode =>
              have hfirst' := ihfirst state firstCode hfirstCompile
              have hsecond' := ihsecond
                (executeInstructions state firstCode) secondCode hsecondCompile
              have hcode : firstCode ++ secondCode = code := by
                simpa [hfirstCompile, hsecondCompile] using hcompile
              subst code
              simp [evalWordProg, hfirst', hsecond', executeInstructions_append]
  | locValue destination source =>
      have hcompile' : wordExpToInstructions (width := width) destination (.var source) =
          some code := by
        simpa only [wordProgToRiscV] using hcompile
      cases h : wordExpToInstructions (width := width) destination (.var source) with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp only [evalWordProg, h]
          rfl
  | tick =>
      have hcompile' : some ([.addi 0 0 0] : List (Instruction width)) = some code := by
        simpa only [wordProgToRiscV] using hcompile
      have hcode : ([.addi 0 0 0] : List (Instruction width)) = code :=
        Option.some.inj hcompile'
      subst code
      simp [evalWordProg, executeInstructions]
  | shareInst operator name address =>
      have hcompile' : wordShareInstToInstructions (width := width) operator name address =
          some code := by
        simpa only [wordProgToRiscV] using hcompile
      cases h : wordShareInstToInstructions (width := width) operator name address with
      | none => rw [h] at hcompile'; cases hcompile'
      | some instructions =>
          have hcode : instructions = code :=
            Option.some.inj (h.symm.trans hcompile')
          subst code
          simp [evalWordProg, evalWordShareInst, h]

/-!
The RISC-V expansion of `LongMul` writes the high word first and the low
word second.  The two source registers are deliberately below the output
registers in this theorem, matching the normalized backend fragment and
making the non-clobbering condition explicit in the execution result.
-/
theorem executeInstructions_longMul_result [NeZero width] (state : State width) :
    (readRegister (executeInstructions state
      [.mulHU 5 2 3, .mul 6 2 3]) 5,
      readRegister (executeInstructions state
        [.mulHU 5 2 3, .mul 6 2 3]) 6) =
      (BitVec.ofNat width
        ((readRegister state 2).toNat * (readRegister state 3).toNat / 2 ^ width),
       readRegister state 2 * readRegister state 3) := by
  simp [executeInstructions, execute, writeRegister, readRegister]

theorem executeInstructions_longMul_general [NeZero width] (state : State width)
    (destinationLeft destinationRight sourceLeft sourceRight : Fin 32)
    (hdestinationLeft_nonzero : destinationLeft ≠ 0)
    (hdestinationRight_nonzero : destinationRight ≠ 0)
    (hdestination_distinct : destinationLeft ≠ destinationRight)
    (hdestinationLeft_sourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeft_sourceRight : destinationLeft ≠ sourceRight) :
    (readRegister (executeInstructions state
      [.mulHU destinationLeft sourceLeft sourceRight,
       .mul destinationRight sourceLeft sourceRight]) destinationLeft,
      readRegister (executeInstructions state
        [.mulHU destinationLeft sourceLeft sourceRight,
         .mul destinationRight sourceLeft sourceRight]) destinationRight) =
      (BitVec.ofNat width
        ((readRegister state sourceLeft).toNat *
          (readRegister state sourceRight).toNat / 2 ^ width),
       readRegister state sourceLeft * readRegister state sourceRight) := by
  have hsourceLeft_destinationLeft : sourceLeft ≠ destinationLeft :=
    Ne.symm hdestinationLeft_sourceLeft
  have hsourceRight_destinationLeft : sourceRight ≠ destinationLeft :=
    Ne.symm hdestinationLeft_sourceRight
  have hdestinationRight_destinationLeft : destinationRight ≠ destinationLeft :=
    Ne.symm hdestination_distinct
  simp [executeInstructions, execute, writeRegister, readRegister,
    hdestinationLeft_nonzero, hdestinationRight_nonzero,
    hdestination_distinct, 
    hsourceLeft_destinationLeft,
    hsourceRight_destinationLeft]

end Flapjack.RiscV
