import Flapjack.RiscV.CorrectnessFfi

namespace Flapjack

open RiscV

def ffiIdentityLoopState : LoopState (Word 64) :=
  { locals := fun name =>
      if name = 1 then some (BitVec.ofNat 64 10)
      else if name = 2 then some (BitVec.ofNat 64 1)
      else if name = 3 then some (BitVec.ofNat 64 20)
      else if name = 4 then some (BitVec.ofNat 64 2)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def ffiIdentityWordState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 1 10) 2 1) 3 20) 4 2

def ffiIdentityLoopHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun _ _ _ _ _ state => some state

def ffiIdentityWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun _ _ _ _ _ state => some state

theorem ffiIdentity_mappedLocals : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    ffiIdentityLoopState.locals ffiIdentityWordState := by
  apply loopToWord_ffi_single_simulation
    ({ vars := [] } : WordContext)
    ffiIdentityLoopState ffiIdentityWordState
    ffiIdentityLoopHandler ffiIdentityWordHandler
    (by
      intro function configuration configurationLength array arrayLength
        loopInput wordInput loopOutput wordOutput hlocals hloop hword
      simp [ffiIdentityLoopHandler, ffiIdentityWordHandler] at hloop hword
      cases hloop
      cases hword
      exact hlocals)
    "identity" 1 2 3 4 []
    (by
      intro name value hvalue
      by_cases h1 : name = 1
      · subst name
        refine ⟨1, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
        simpa [ffiIdentityLoopState, ffiIdentityWordState,
          readRegister, writeRegister] using hvalue
      · by_cases h2 : name = 2
        · subst name
          refine ⟨2, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
          simpa [ffiIdentityLoopState, ffiIdentityWordState,
            readRegister, writeRegister] using hvalue
        · by_cases h3 : name = 3
          · subst name
            refine ⟨3, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
            simpa [ffiIdentityLoopState, ffiIdentityWordState,
              readRegister, writeRegister] using hvalue
          · by_cases h4 : name = 4
            · subst name
              refine ⟨4, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
              simpa [ffiIdentityLoopState, ffiIdentityWordState,
                readRegister, writeRegister] using hvalue
            · simp [ffiIdentityLoopState, h1, h2, h3, h4] at hvalue)
  · simp [evalLoopFfi, ffiIdentityLoopHandler, ffiIdentityLoopState]
  · simp [loopToWordProg, evalWordFfi, ffiIdentityWordHandler,
      registerOfNat, wordFindVar, lookupNatInfo, 
      ]

example : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    ffiIdentityLoopState.locals ffiIdentityWordState := by
  apply loopToWord_ffi_single_combined_simulation_fuel
    (context := ({ vars := [] } : WordContext))
    (functions := [])
    (wordFunctions := [])
    (loopState := ffiIdentityLoopState)
    (wordState := ffiIdentityWordState)
    (loopHandler := ffiIdentityLoopHandler)
    (wordHandler := ffiIdentityWordHandler)
    (handler_agrees := by
      intro function configuration configurationLength array arrayLength
        loopInput wordInput loopOutput wordOutput hlocals hloop hword
      simp [ffiIdentityLoopHandler, ffiIdentityWordHandler] at hloop hword
      cases hloop
      cases hword
      exact hlocals)
    (function := "identity")
    (configuration := 1)
    (configurationLength := 2)
    (array := 3)
    (arrayLength := 4)
    (live := [])
    (fuel := 3)
    (hlocals := ffiIdentity_mappedLocals)
  · simp [evalLoopProgWithCallsAndFfi, ffiIdentityLoopHandler,
      ffiIdentityLoopState]
  · simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi,
      ffiIdentityWordHandler, registerOfNat, wordFindVar, lookupNatInfo,
      ]

example : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    ffiIdentityLoopState.locals
      (RiscV.execute ffiIdentityWordState (.addi 0 0 0)) := by
  apply loopToWord_seq_combined_simulation
    (context := ({ vars := [] } : WordContext))
    (functions := [])
    (wordFunctions := [])
    (loopState := ffiIdentityLoopState)
    (wordState := ffiIdentityWordState)
    (loopHandler := ffiIdentityLoopHandler)
    (wordHandler := ffiIdentityWordHandler)
    (fuel := 1)
    (first := .ffi "identity" 1 2 3 4 [])
    (second := .tick)
    (finalLoop := ffiIdentityLoopState)
    (finalWord := RiscV.execute ffiIdentityWordState (.addi 0 0 0))
    (hfirst := by
      intro middleLoop middleWord hloop hword
      exact loopToWord_ffi_single_combined_simulation_fuel
        (context := ({ vars := [] } : WordContext))
        (functions := [])
        (wordFunctions := [])
        (loopState := ffiIdentityLoopState)
        (wordState := ffiIdentityWordState)
        (loopHandler := ffiIdentityLoopHandler)
        (wordHandler := ffiIdentityWordHandler)
        (handler_agrees := by
          intro function configuration configurationLength array arrayLength
            loopInput wordInput loopOutput wordOutput hlocals hloop hword
          simp [ffiIdentityLoopHandler, ffiIdentityWordHandler] at hloop hword
          cases hloop
          cases hword
          exact hlocals)
        (function := "identity")
        (configuration := 1)
        (configurationLength := 2)
        (array := 3)
        (arrayLength := 4)
        (live := [])
        (fuel := 0)
        (hlocals := ffiIdentity_mappedLocals)
        middleLoop middleWord hloop hword)
    (hsecond := by
      intro middleLoop middleWord hlocals finalLoop finalWord hloop hword
      have hloop' : evalLoopProg 1 middleLoop (.tick : LoopProg (Word 64)) =
          some (.normal finalLoop) := by
        simpa [evalLoopProgWithCallsAndFfi, evalLoopProg] using hloop
      have hfinalLoop : finalLoop = middleLoop := by
        simpa [evalLoopProg] using hloop'.symm
      subst finalLoop
      have hword' : RiscV.evalWordProg middleWord (.tick : WordProg (Word 64)) =
          some finalWord := by
        simpa [loopToWordProg, evalWordFunctionWithHandlersAndFfi,
          evalWordFunction, RiscV.evalWordProg] using hword
      exact loopToWord_tick_preserves_mapped_locals ({ vars := [] } : WordContext)
        middleLoop.locals middleWord hlocals finalWord hword')
  · simp [evalLoopProgWithCallsAndFfi, evalLoopProg, ffiIdentityLoopHandler,
      ffiIdentityLoopState]
  · simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi,
      evalWordFunction, ffiIdentityWordHandler, registerOfNat, wordFindVar,
      lookupNatInfo, RiscV.execute, RiscV.writeRegister, RiscV.nextPc]

def sourceFfiIdBody : Prog (Word 64) :=
  .dec "result" .one (.const 0)
    (.seq
      (.extCall "inc" (.var .local "x") (.const 0)
        (.const 0) (.const 0))
      (.return (.var .local "result")))

def sourceFfiDeclarations : List (Decl (Word 64)) :=
  [.function
    { name := "ffiId", inline := false, exported := false,
      params := [("x", .one)],
      body := sourceFfiIdBody, returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "answer" .one "ffiId"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "answer")), returnShape := .one }]

def sourceFfiPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscVWithFfi (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    [("inc", 7)] sourceFfiDeclarations

def sourceFfiHandler : PanFfiHandler (Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + 1))
    else none

def sourceFfiMainBody : Prog (Word 64) :=
  .decCall "answer" .one "ffiId"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "answer"))

def sourceFfiFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("ffiId", ["x"], sourceFfiIdBody), ("main", [], sourceFfiMainBody)]

example :
    (evalPanProgWithCallsAndFfi sourceFfiFunctions sourceFfiHandler 20
      (fun _ => none) sourceFfiMainBody).map
        (fun result => match result with
        | .returned _ values => values
        | _ => []) = some [42] := by
  decide +kernel

example :
    (evalPanProgWithCallsAndFfi [] sourceFfiHandler 10
      (fun name => if name == "x" then some (BitVec.ofNat 64 41) else none)
      (.while (.const (BitVec.ofNat 64 0))
        (.extCall "inc" (.var .local "x") (.const 0)
          (.const 0) (.const 0)))).map (fun result => match result with
        | .normal locals => locals "x"
        | _ => none) = some (some 41) := by
  decide +kernel

example :
    sourceFfiPipeline.pipeline.word.length = 2 &&
      sourceFfiPipeline.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example : sourceFfiPipeline.callLinkedFunctions.isSome := by
  native_decide

def sourceFfiHost : WordFfiHost 64 :=
  fun service configuration _ _ _ state =>
    if service = 7 then
      some { (writeRegister state 4 (configuration + 1)) with pc := state.pc + 4 }
    else none

def sourceFfiImage : Option (Word 64 × List (Instruction 64)) := do
  let entries ← sourceFfiPipeline.callLinkedFunctions
  let entry ← lookupLinkedEntry 2 entries
  let code := entries.flatMap (fun (_, _, _, code, _) => code)
  pure (entry, code)

example :
    sourceFfiImage.bind (fun (entry, code) =>
      executeFunctionAtWithFfi sourceFfiHost 100 0 entry 100 [] code [4] []
        (writeRegister (zeroState 64) 1 100)) = some [42] := by
  native_decide

theorem sourceFfi_end_to_end_correct :
    (evalPanProgWithCallsAndFfi sourceFfiFunctions sourceFfiHandler 20
      (fun _ => none) sourceFfiMainBody).map
        (fun result => match result with
        | .returned _ values => values
        | _ => []) = some [42] ∧
      sourceFfiImage.bind (fun (entry, code) =>
        executeFunctionAtWithFfi sourceFfiHost 100 0 entry 100 [] code [4] []
          (writeRegister (zeroState 64) 1 100)) = some [42] := by
  constructor <;> native_decide

end Flapjack
