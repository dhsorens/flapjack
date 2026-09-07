import Flapjack.CrepeSemantics

/-!
Initial generic correctness lemmas for the stateful Crepe evaluator.

These statements deliberately quantify over all semantic handlers: the
programs involved do not invoke them, so the lemmas establish a clean
source-to-Crepe result boundary before adding hypotheses for calls, memory,
and FFI.
-/

namespace Flapjack

theorem compile_full_skip_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.skip : Prog α)) =
      evalPanMemResult locals state.memory (.skip : Prog α) := by
  simp [compileProg, evalCrepFullResult, evalCrepFullProg,
    evalPanMemResult, evalPanMemProg]

theorem compile_full_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress value : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 1 state
        (compileProg context (.return (.const value))) =
      evalPanMemResult locals state.memory
        (.return (.const value) : Prog α) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemExp]

theorem compile_full_add_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress left right : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 10 state
        (compileProg context
          (.return (.op .add [.const left, .const right]))) =
      evalPanMemResult locals state.memory
        (.return (.op .add [.const left, .const right]) : Prog α) := by
  simp [compileProg, compileExp, compileExp.compileExpList, cexpHeads,
    evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemExp, evalPanBinOp]

theorem compile_full_store_load_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress address value : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.store (.const address) (.const value))
            (.return (.load .one (.const address))))) =
      evalPanMemResult locals state.memory
        (.seq (.store (.const address) (.const value))
          (.return (.load .one (.const address)))) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    loadShape, evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanMemResult, evalPanMemProg, evalPanMemExp,
    updateMemory, updateCrepLocal, restoreCrepResult]

theorem compile_full_ite_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress condition thenValue elseValue : α) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.ite (.const condition)
            (.return (.const thenValue))
            (.return (.const elseValue)))) =
      evalPanMemResult locals state.memory
        (.ite (.const condition)
          (.return (.const thenValue))
          (.return (.const elseValue))) := by
  simp [compileProg, compileExp, evalCrepFullResult, evalCrepFullProg,
    evalCrepFullExps, evalCrepFullExp, evalPanMemResult,
    evalPanMemProg, evalPanMemCondition, evalPanMemExp]
  split <;> simp_all [
    ]

theorem compile_full_local_assign_return_const_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat) (value : α)
    (lookup : lookupInfo name context.vars = some (.one, [slot])) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 20 state
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))) =
      evalPanMemResult locals state.memory
        (.seq (.assign .local name (.const value))
          (.return (.var .local name))) := by
  simp [compileProg, compileExp, crepNestedSeq, lookup,
    evalCrepFullResult, evalCrepFullProg, evalCrepFullExps,
    evalCrepFullExp, evalPanMemResult, evalPanMemProg,
    evalPanMemExp, updateCrepLocal, updatePanLocal,
    distinctLists]

theorem compile_full_local_return_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (name : VarName) (slot : Nat)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (environment_agrees : state.locals slot = locals name) :
    evalCrepFullResult [] primitive ffi sharedMem
        baseAddress topAddress 5 state
        (compileProg context (.return (.var .local name))) =
      evalPanMemResult locals state.memory
        (.return (.var .local name) : Prog α) := by
  simp [compileProg, compileExp, lookup, evalCrepFullResult,
    evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanMemResult, evalPanMemProg, evalPanMemExp,
    environment_agrees]
  cases h : locals name <;> simp []

theorem compile_full_extCall_const_noop_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α) (locals : VarName → Option α)
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress configuration configurationLength array arrayLength : α)
    (function : FunName) :
    evalCrepFullProg [] primitive
        (fun _ _ _ _ _ sourceState => some sourceState) sharedMem
        baseAddress topAddress 30 state
        (compileProg context
          (.extCall function (.const configuration)
            (.const configurationLength) (.const array) (.const arrayLength))) =
      some (.normal state) ∧
    evalPanFfiProg
        (fun _ _ _ _ _ sourceLocals => some sourceLocals) locals
        (.extCall function (.const configuration)
          (.const configurationLength) (.const array) (.const arrayLength)) =
      some locals := by
  have hrestoreFour (base : Nat → Option α) (offset : Nat)
      (value1 value2 value3 value4 : α) :
      restoreCrepLocal
          (restoreCrepLocal
            (restoreCrepLocal
              (restoreCrepLocal
                (updateCrepLocal
                  (updateCrepLocal
                    (updateCrepLocal (updateCrepLocal base (offset + 1) value1)
                      (offset + 2) value2)
                    (offset + 3) value3)
                  (offset + 4) value4)
                (offset + 4) (base (offset + 4)))
              (offset + 3) (base (offset + 3)))
            (offset + 2) (base (offset + 2)))
          (offset + 1) (base (offset + 1)) = base := by
    funext current
    by_cases h1 : current = offset + 1
    · simp [restoreCrepLocal, h1]
    by_cases h2 : current = offset + 2
    · simp [restoreCrepLocal, h2]
    by_cases h3 : current = offset + 3
    · simp [restoreCrepLocal, h3]
    by_cases h4 : current = offset + 4
    · simp [restoreCrepLocal, h4]
    · simp [restoreCrepLocal, updateCrepLocal, h1, h2, h3, h4]
  simp [compileProg, firstCompiledExp, compileExp, nestedDecs,
    evalCrepFullProg, evalCrepFullExp, evalPanExp, evalPanFfiProg, evalPanExtCall,
    updateCrepLocal, restoreCrepResult, hrestoreFour]

end Flapjack
