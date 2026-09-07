import Flapjack.Pipeline

namespace Flapjack

def pipelineAllocatedMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := true, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 6), .const (BitVec.ofNat 64 7)]),
      returnShape := .one }]

example [OfNat α 1] :
    pipelineWordFunctionsAllocated
      ([] : List (Nat × List Nat × LoopProg α)) = some [] := by
  rfl

example [OfNat α 1] :
    pipelineWordFunctionsAllocatedWithAnalysis
      [(0, [0], (.assign 1 (.var 0) : LoopProg α))] =
      some [(0, [2], (.assign 3 (.var 2) : WordProg α))] := by
  simp [pipelineWordFunctionsAllocatedWithAnalysis,
    wordAllocateProgramWithSlots, wordAllocateContextWithClashes,
    wordAllocateVarsWithClashes, wordGreedyColour, wordColourCandidates,
    wordFirstAvailable, wordPreferredRegister,
    wordAllocatableRegisters, wordNeighbours, wordUsedRegisters,
    wordRegisterIsAllocatable,
    wordColouringUsesAllocatable, wordColouringRespectsClashes,
    wordProgClashAnalysis, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs,
    wordExpReadVars, loopAccVars, loopVarsOfExp, loopInsertAll, loopInsert,
    loopToWordProg, wordCompileExp, wordFindVar, wordMapVars, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example [OfNat α 1] :
    pipelineWordFunctionsAllocatedWithAnalysisAndColour
      [(0, [0], (.assign 1 (.var 0) : LoopProg α))] =
      some [(0, [2], (.assign 3 (.var 2) : WordProg α))] := by
  simp [pipelineWordFunctionsAllocatedWithAnalysisAndColour,
    wordAllocateProgramWithSlotsAndColour, wordAllocateContextWithClashes,
    wordAllocateVarsWithClashes, wordGreedyColour, wordColourCandidates,
    wordFirstAvailable, wordPreferredRegister, wordAllocatableRegisters,
    wordNeighbours, wordUsedRegisters, wordRegisterIsAllocatable,
    wordColouringUsesAllocatable, wordColouringRespectsClashes,
    wordProgClashAnalysis, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordExpReadVars, loopAccVars, loopVarsOfExp,
    loopInsertAll, loopInsert, loopToWordProg, wordCompileExp, wordFindVar,
    wordApplyColour, wordApplyColourExp, wordMapVars, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example [NeZero width] :
    pipelineWordFunctionsAllocatedWithSpills
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word width))) = some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithGraph
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome := by
  native_decide

example :
    RiscV.wordToStackFunctionWithParameters
        { locations := [(0, .stack 0)], scratch := 31, stackBase := 10 }
        [0]
        ((.skip : WordProg (RiscV.Word 64))) =
      some (.seq (.arith .or 31 2 2) (.stackStore 31 10) : StackProg Nat) := by
  simp [RiscV.wordToStackFunctionWithParameters, RiscV.wordToStackProgWord,
    RiscV.wordToStackProgNat, RiscV.wordStackMovesFromPhysical,
    RiscV.wordStackPhysicalMovesFrom, RiscV.wordStackParallelLocationMove,
    RiscV.wordStackParallelLocationMoveAux,
    RiscV.wordStackLocationMoveDestinations,
    RiscV.wordStackLocationMoveReady,
    RiscV.wordStackLocationMoveRemoveDestination,
    RiscV.wordStackLocationMove, RiscV.wordStackMoveFromPhysical,
    RiscV.wordStackJoin, RiscV.wordStackLocation, RiscV.wordStackOffset,
    lookupNatInfo,
    RiscV.wordProgToNat]

example :
    (pipelineWordFunctionsAllocatedWithSpills
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome := by
  native_decide


example :
    (pipelineWordFunctionsAllocatedWithSpills
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).map
        (fun functions => functions.map (fun (_, parameters, _) => parameters)) =
      some [[2]] := by
  native_decide

example :
    (compileFlapjackRiscVViaAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaGraphAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaGraphAllocatedStackLinked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).map
        (fun sections => sections.map (fun (label, entry, _) => (label, entry))) =
      some [(0, BitVec.ofNat 64 0), (1, BitVec.ofNat 64 76)] := by
  native_decide


end Flapjack
