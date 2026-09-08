import Flapjack.RiscV.Backend
import Flapjack.RiscV.Correctness
import Flapjack.RiscV.Calls

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

/-! On the straight-line fragment the call-aware selector is definitionally the
    base selector with an empty return carrier.  This agreement is the bridge
    that lets the existing instruction-level theorem be reused after calls
    have been introduced into the surrounding compiler. -/

theorem wordFunctionToRiscVWithCalls_agrees_straightLine [NeZero width]
    (context : WordCallContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    wordFunctionToRiscVWithCalls context program =
      (wordProgToRiscV program).map (fun code => (code, [])) := by
  induction hstraight with
  | skip => simp [wordFunctionToRiscVWithCalls, wordProgToRiscV]
  | move store moves =>
      cases h : wordMoveToInstructions (width := width) moves <;>
        simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | assign destination value =>
      cases h : wordExpToInstructions (width := width) destination value <;>
        simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | inst instruction =>
      cases instruction with
      | arith operation =>
          cases h : wordArithToInstructions (width := width) operation <;>
            simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
      | mem operator destination address =>
          cases h : wordInstToInstruction (width := width)
              (.mem operator destination address) <;>
            simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | store address value =>
      cases h : wordStoreToInstructions (width := width) address value <;>
        simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | locValue destination source =>
      cases h : wordExpToInstruction (width := width) destination (.var source) <;>
        simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | tick => simp [wordFunctionToRiscVWithCalls, wordProgToRiscV]
  | shareInst operator name address =>
      cases h : wordShareInstToInstructions (width := width) operator name address <;>
        simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      cases hfirstCode : wordProgToRiscV first with
      | none => simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, ihfirst,
          hfirstCode]
      | some firstCode =>
          cases hsecondCode : wordProgToRiscV second with
          | none => simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, ihfirst,
              ihsecond, hfirstCode, hsecondCode]
          | some secondCode =>
              simp [wordFunctionToRiscVWithCalls, wordProgToRiscV, ihfirst,
                ihsecond, hfirstCode, hsecondCode]

theorem evalWordFunction_wordRiscVStraightLine_eq_evalWordProg [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    evalWordFunction state program =
      (evalWordProg state program).map (fun state => (state, [])) := by
  induction hstraight generalizing state with
  | skip => simp [evalWordFunction, evalWordProg]
  | move store moves => simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assign destination value =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | inst instruction =>
      cases instruction with
      | arith operation =>
          simp [evalWordFunction, evalWordProg, Function.comp_def]
      | mem operator destination address =>
          cases operator <;>
            simp [evalWordFunction, evalWordProg, Function.comp_def]
  | store address value =>
      cases h : wordShareInstToInstructions (width := width) .store value address <;>
        simp [evalWordFunction, evalWordProg, evalWordShareInst, h]
  | locValue destination source =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | tick => simp [evalWordFunction, evalWordProg]
  | shareInst operator name address =>
      cases h : wordShareInstToInstructions (width := width) operator name address <;>
        simp [evalWordFunction, evalWordProg, evalWordShareInst, h]
  | @seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [evalWordFunction, evalWordProg]
      rw [ihfirst state]
      cases hfirstEval : evalWordProg state first with
      | none => simp
      | some firstState =>
          simp [ihsecond firstState]
          cases hsecondEval : evalWordProg firstState second with
          | none => simp
          | some secondState => simp

theorem wordControlInstructions_map_instruction [NeZero width]
    (code : List (Instruction width)) :
    wordControlInstructions (code.map .instruction) = some code := by
  induction code with
  | nil => rfl
  | cons instruction code ih =>
      simp [wordControlInstructions, ih]

theorem wordFunctionToRiscVWithCallsAndLoopsAux_agrees_straightLine [NeZero width]
    (context : WordCallContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    wordFunctionToRiscVWithCallsAndLoopsAux context program =
      (wordFunctionToRiscVWithCalls context program).map
        (fun result => (result.1.map .instruction, result.2)) := by
  induction hstraight with
  | skip =>
      cases h : wordFunctionToRiscVWithCalls context
          (.skip : WordProg (Word width)) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | move store moves =>
      cases h : wordFunctionToRiscVWithCalls context (.move store moves) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | assign destination value =>
      cases h : wordFunctionToRiscVWithCalls context (.assign destination value) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | inst instruction =>
      cases h : wordFunctionToRiscVWithCalls context (.inst instruction) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | store address value =>
      cases h : wordFunctionToRiscVWithCalls context (.store address value) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | locValue destination source =>
      cases h : wordFunctionToRiscVWithCalls context
          (.locValue destination source) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | tick =>
      cases h : wordFunctionToRiscVWithCalls context
          (.tick : WordProg (Word width)) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | shareInst operator name address =>
      cases h : wordFunctionToRiscVWithCalls context
          (.shareInst operator name address) <;>
        simp [wordFunctionToRiscVWithCallsAndLoopsAux, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [wordFunctionToRiscVWithCallsAndLoopsAux]
      rw [ihfirst, ihsecond]
      simp only [wordFunctionToRiscVWithCalls]
      cases hfirstCode : wordFunctionToRiscVWithCalls context first with
      | none => simp
      | some firstResult =>
          cases hsecondCode : wordFunctionToRiscVWithCalls context second with
          | none =>
              cases firstResult with
              | mk firstCode firstReturns =>
                  cases firstReturns with
                  | nil => simp
                  | cons firstReturn firstReturns => simp
          | some secondResult =>
              cases firstResult with
              | mk firstCode firstReturns =>
                  cases firstReturns with
                  | nil =>
                      cases secondResult with
                      | mk secondCode secondReturns =>
                          simp
                  | cons firstReturn firstReturns =>
                      simp

theorem wordFunctionToRiscVWithCallsAndLoops_agrees_straightLine [NeZero width]
    (context : WordCallContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    wordFunctionToRiscVWithCallsAndLoops context program =
      wordFunctionToRiscVWithCalls context program := by
  simp only [wordFunctionToRiscVWithCallsAndLoops]
  rw [wordFunctionToRiscVWithCallsAndLoopsAux_agrees_straightLine
    context program hstraight]
  cases h : wordFunctionToRiscVWithCalls context program with
  | none => simp
  | some result =>
      cases result with
      | mk code returns =>
          simp [wordControlInstructions_map_instruction]

theorem wordFunctionToRiscVWithCalls_sound_of_straightLine [NeZero width]
    (context : WordCallContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCalls context program =
      some (code, [])) :
    evalWordFunction state program =
      some (executeInstructions state code, []) := by
  have hagree := wordFunctionToRiscVWithCalls_agrees_straightLine
    context program hstraight
  rw [hagree] at hcompile
  have hbase : wordProgToRiscV program = some code := by
    cases hcode : wordProgToRiscV program with
    | none => simp [hcode] at hcompile
    | some instructions =>
        have hinstructions : instructions = code := by
          simpa [hcode] using hcompile
        exact congrArg (fun xs : List (Instruction width) => some xs)
          hinstructions
  have hword := wordProgToRiscV_sound_of_straightLine state program
    hstraight code hbase
  rw [evalWordFunction_wordRiscVStraightLine_eq_evalWordProg state
    program hstraight, hword]
  rfl

theorem wordFunctionToRiscVWithCalls_move_sound [NeZero width]
    (context : WordCallContext width) (state : State width)
    (store : Nat) (moves : List (Nat × Nat))
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCalls context (.move store moves) =
      some (code, [])) :
    evalWordFunction state (.move store moves) =
      some (executeInstructions state code, []) := by
  cases hmove : wordMoveToInstructions (width := width) moves with
  | none =>
      simp [wordFunctionToRiscVWithCalls, hmove] at hcompile
  | some instructions =>
      have hcompile' :
          some (instructions, ([] : List (Fin 32))) =
            some (code, ([] : List (Fin 32))) := by
        simpa [wordFunctionToRiscVWithCalls, hmove] using hcompile
      have hcode : instructions = code :=
        congrArg Prod.fst (Option.some.inj hcompile')
      subst code
      simp [evalWordFunction, hmove]

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

/-! The call-aware selector preserves the source arithmetic meaning at the
    concrete multiword boundaries.  These statements retain the selector
    result as a hypothesis, so they remain useful after the selector grows
    additional call and control-flow cases. -/

theorem wordFunctionToRiscVWithCalls_addCarry_result [NeZero width]
    (context : WordCallContext width) (state : State width)
    (code : List (Instruction width))
    (zero : readRegister state 0 = 0)
    (hcompile : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some (code, [])) :
    (readRegister (executeInstructions state code) 5,
      readRegister (executeInstructions state code) 6) =
      addCarryWords (readRegister state 2) (readRegister state 3)
        (readRegister state 4) := by
  have hshape : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some ([.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3,
        .add 5 5 31, .sltu 31 5 31, .or 6 6 31], []) := by
    simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
      registerOfNat]
  have hcode : ([.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3,
      .add 5 5 31, .sltu 31 5 31, .or 6 6 31] :
      List (Instruction width)) = code := by
    exact congrArg Prod.fst (Option.some.inj (hshape.symm.trans hcompile))
  subst code
  exact executeInstructions_addCarry state zero

theorem wordFunctionToRiscVWithCalls_longMul_result [NeZero width]
    (context : WordCallContext width) (state : State width)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.longMul 5 6 2 3))) : WordProg (Word width)) =
      some (code, [])) :
    (readRegister (executeInstructions state code) 5,
      readRegister (executeInstructions state code) 6) =
      (BitVec.ofNat width
        ((readRegister state 2).toNat * (readRegister state 3).toNat / 2 ^ width),
       readRegister state 2 * readRegister state 3) := by
  have hshape : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.longMul 5 6 2 3))) : WordProg (Word width)) =
      some ([.mulHU 5 2 3, .mul 6 2 3], []) := by
    simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
      registerOfNat]
  have hcode : ([.mulHU 5 2 3, .mul 6 2 3] :
      List (Instruction width)) = code := by
    exact congrArg Prod.fst (Option.some.inj (hshape.symm.trans hcompile))
  subst code
  exact executeInstructions_longMul_result state


theorem wordFunctionToRiscVWithCalls_div_result [NeZero width]
    (context : WordCallContext width) (state : State width)
    (code : List (Instruction width))
    (hdivisor : readRegister state 3 ≠ 0)
    (hcompile : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.div 5 2 3))) : WordProg (Word width)) =
      some (code, [])) :
    readRegister (executeInstructions state code) 5 =
      BitVec.ofNat width
        ((readRegister state 2).toNat / (readRegister state 3).toNat) := by
  have hshape : wordFunctionToRiscVWithCalls context
      ((.inst (.arith (.div 5 2 3))) : WordProg (Word width)) =
      some ([.divU 5 2 3], []) := by
    simp [wordFunctionToRiscVWithCalls, wordArithToInstructions,
      wordArithToInstruction, registerOfNat]
  have hcode : ([.divU 5 2 3] : List (Instruction width)) = code := by
    exact congrArg Prod.fst (Option.some.inj (hshape.symm.trans hcompile))
  subst code
  rw [executeInstructions_single, execute_divU]
  split <;> simp_all

end Flapjack.RiscV
