import Flapjack.RiscV.Ffi
import Flapjack.RiscV.Lab

/-!
Machine-level correctness for the RISC-V FFI ABI.  The abstract Word FFI
handler receives the four source-register values and the pre-call state.  The
target host instead receives the state after the four ABI moves and service
materialization.  These theorems make that boundary explicit.
-/

namespace Flapjack.RiscV

theorem executeInstructionsWithFfi_append
    [NeZero width] (host : WordFfiHost width) (state : State width)
    (first second : List (Instruction width)) :
    executeInstructionsWithFfi host state (first ++ second) =
      (executeInstructionsWithFfi host state first).bind
        (fun state => executeInstructionsWithFfi host state second) := by
  induction first generalizing state with
  | nil => simp [executeInstructionsWithFfi]
  | cons instruction first ih =>
      simp only [List.cons_append, executeInstructionsWithFfi]
      cases hstep : executeWithFfi host state instruction with
      | none => simp []
      | some nextState => simp [ih]

/-!
The Lab FFI operation is the point at which the already-marshalled Word ABI
is handed to the target machine.  Its compiler expansion only materializes
the service number in x14 and then executes ECALL; the four argument
registers are intentionally preserved.  This lemma exposes that boundary in
a form that can be composed with Lab section and program compilation.
-/
theorem labCompileAsm_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat)
    (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (labCompileAsm context sectionId labels position (.callFfi function)).bind
        (executeInstructionsWithFfi host state) = resultState := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  simpa [labCompileAsm, hservice, executeInstructionsWithFfi, executeWithFfi,
    executeInstructions, execute, writeRegister, readRegister, nextPc,
    hzero', Nat.mod_eq_of_lt hservice_bounded] using hhost

/-!
Lift the instruction-level result through the section compiler for the
singleton FFI section.  This keeps label collection and the generated code
shape behind a reusable semantic boundary for later linked-program proofs.
-/
theorem compileLabSection_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (compileLabSection context
      ⟨sectionId, [.labAsm (.callFfi function) [] 0]⟩).bind
        (executeInstructionsWithFfi host state) = resultState := by
  simp [compileLabSection, labCompileLines, labCompileAsm]
  exact labCompileAsm_callFfi_execute_agreement context host state sectionId
    [] 0 function service resultState hservice hservice_bounded hzero hhost

/-!
The corresponding one-section program theorem closes the next linking
boundary.  Since the section contains no labels, flattening preserves the
same service materialization and ECALL sequence proved above.
-/
theorem compileLabProgram_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (compileLabProgram context
      [⟨sectionId, [.labAsm (.callFfi function) [] 0]⟩]).bind
        (executeInstructionsWithFfi host state) = resultState := by
  simp [compileLabProgram, labCompileProgramSections, labCompileProgramLines,
    labCompileAsmProgram]
  exact labCompileAsm_callFfi_execute_agreement context host state sectionId
    [] 0 function service resultState hservice hservice_bounded hzero hhost

/-!
At the function boundary, an FFI call must return through the caller's x1
continuation.  This theorem composes the linked program shape, ECALL host
transition, and JALR x0, x1, 0 return path for the smallest call-and-return
function.  The fixed four-step fuel is the exact cost of the generated
addi, ecall, jalr, and return-address check.
-/
theorem compileLabProgram_callFfi_return_executeFunctionAt_agreement
    (context : WordFfiContext)
    (host : WordFfiHost 64) (state hostState : State 64)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ 64)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (state.registers 10) (state.registers 11)
      (state.registers 12) (state.registers 13)
      { pc := 4, registers := fun current =>
          if current = 14 then BitVec.ofNat 64 service
          else state.registers current,
        memory := state.memory, privilege := state.privilege, mode := state.mode } =
      some hostState)
    (hhost_pc : hostState.pc = 8)
    (hhost_return : readRegister hostState 1 = BitVec.ofNat 64 100) :
    (compileLabProgram context
      [⟨sectionId, [
        .labAsm (.callFfi function) [] 0,
        .labAsm (.return) [] 0]⟩]).bind
    (fun code =>
          (executeFunctionAtWithFfi host 4 0 0 (BitVec.ofNat 64 100)
            [] code [] [] state)) = some [] := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  let afterAddi : State 64 :=
    { pc := 4, registers := fun current =>
        if current = 14 then BitVec.ofNat 64 service
        else state.registers current,
      memory := state.memory, privilege := state.privilege, mode := state.mode }
  have hadd :
      execute { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service)) = afterAddi := by
    simp [afterAddi, execute, writeRegister, readRegister, nextPc, hzero']
  have haddWithFfi :
      executeWithFfi host { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service)) = some afterAddi := by
    simpa [executeWithFfi] using congrArg some hadd
  have hecall :
      executeWithFfi host afterAddi .ecall = some hostState := by
    simpa [executeWithFfi, afterAddi, readRegister,
      Nat.mod_eq_of_lt hservice_bounded] using hhost
  have hhost_return' : hostState.registers 1 = BitVec.ofNat 64 100 := by
    simpa [readRegister] using hhost_return
  have hmask :
      (BitVec.ofNat 64 100) &&& (BitVec.ofNat 64 (2 ^ 64 - 2)) =
        BitVec.ofNat 64 100 := by
    decide
  have hreturn :
      execute hostState (.jalr 0 1 (0#64)) = { hostState with pc := 100 } := by
    simp [execute, writeRegister, readRegister, hhost_return', hmask]
  have hrun :
      executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { state with pc := 0 } =
      some { hostState with pc := 100 } := by
    have hzeroNe : (0#64) ≠ (BitVec.ofNat 64 100) := by decide
    have hfourNe : (4#64) ≠ (BitVec.ofNat 64 100) := by decide
    have hfirst :
        executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { state with pc := 0 } =
          executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            afterAddi := by
      rw [executeCodeUntilWithFfi]
      simp [hzeroNe]
      change
        (executeWithFfi host { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service))).bind
            (fun nextState =>
              executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
                [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
                nextState) = _
      rw [haddWithFfi]
      simp
    have hsecond :
        executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            afterAddi =
          executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            hostState := by
      rw [executeCodeUntilWithFfi]
      simp [afterAddi, hfourNe]
      change
        (executeWithFfi host afterAddi .ecall).bind
            (fun nextState =>
              executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
                [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
                nextState) = _
      rw [hecall]
      simp
    have hreturnWithFfi :
        executeWithFfi host hostState (.jalr 0 1 (0#64)) =
          some { hostState with pc := 100 } := by
      simpa [executeWithFfi] using congrArg some hreturn
    have hthird :
        executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            hostState =
          executeCodeUntilWithFfi host 1 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { hostState with pc := 100 } := by
      simp [executeCodeUntilWithFfi, hreturnWithFfi, hhost_pc]
    rw [hfirst, hsecond, hthird]
    simp [executeCodeUntilWithFfi]
  have hcode :
      compileLabProgram context
        [⟨sectionId, [
          .labAsm (.callFfi function) [] 0,
          .labAsm (.return) [] 0]⟩] =
        some [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0] := by
    simp [compileLabProgram, labCompileProgramSections,
      labCompileProgramLines, labCompileAsmProgram, hservice]
  rw [hcode]
  change
    (executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
      [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
      { state with pc := 0 }).map (fun _ => ([] : List (Word 64))) =
      some []
  rw [hrun]
  simp

theorem executeInstructionsWithFfi_wordFfi_abi
    [NeZero width] (host : WordFfiHost width) (state : State width)
    (service : Nat) (configuration configurationLength array arrayLength : Fin 32)
    (resultState : Option (State width))
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configuration, configurationLength, array, arrayLength] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhost : host service
      (readRegister state configuration)
      (readRegister state configurationLength)
      (readRegister state array)
      (readRegister state arrayLength)
      (executeInstructions state
        [.addi 10 configuration (0#width), .addi 11 configurationLength (0#width),
         .addi 12 array (0#width), .addi 13 arrayLength (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      resultState) :
      executeInstructionsWithFfi host state
      [.addi 10 configuration (0#width), .addi 11 configurationLength (0#width),
       .addi 12 array (0#width), .addi 13 arrayLength (0#width),
       .addi 14 0 (BitVec.ofNat width service), .ecall] =
      resultState := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  have hconfiguration10 : configuration ≠ 10 :=
    hsource configuration (by simp) 10 (by simp)
  have hconfiguration11 : configuration ≠ 11 :=
    hsource configuration (by simp) 11 (by simp)
  have hconfiguration12 : configuration ≠ 12 :=
    hsource configuration (by simp) 12 (by simp)
  have hconfiguration13 : configuration ≠ 13 :=
    hsource configuration (by simp) 13 (by simp)
  have hconfigurationLength10 : configurationLength ≠ 10 :=
    hsource configurationLength (by simp) 10 (by simp)
  have hconfigurationLength11 : configurationLength ≠ 11 :=
    hsource configurationLength (by simp) 11 (by simp)
  have hconfigurationLength12 : configurationLength ≠ 12 :=
    hsource configurationLength (by simp) 12 (by simp)
  have hconfigurationLength13 : configurationLength ≠ 13 :=
    hsource configurationLength (by simp) 13 (by simp)
  have harray10 : array ≠ 10 :=
    hsource array (by simp) 10 (by simp)
  have harray11 : array ≠ 11 :=
    hsource array (by simp) 11 (by simp)
  have harray12 : array ≠ 12 :=
    hsource array (by simp) 12 (by simp)
  have harray13 : array ≠ 13 :=
    hsource array (by simp) 13 (by simp)
  have harrayLength10 : arrayLength ≠ 10 :=
    hsource arrayLength (by simp) 10 (by simp)
  have harrayLength11 : arrayLength ≠ 11 :=
    hsource arrayLength (by simp) 11 (by simp)
  have harrayLength12 : arrayLength ≠ 12 :=
    hsource arrayLength (by simp) 12 (by simp)
  have harrayLength13 : arrayLength ≠ 13 :=
    hsource arrayLength (by simp) 13 (by simp)
  simpa [executeInstructionsWithFfi, executeWithFfi, executeInstructions,
    execute, writeRegister, readRegister, nextPc,
    hconfiguration10, hconfiguration11, hconfiguration12, hconfiguration13,
    hconfigurationLength10, hconfigurationLength11,
    hconfigurationLength12, hconfigurationLength13,
    harray10, harray11, harray12, harray13,
    harrayLength10, harrayLength11, harrayLength12, harrayLength13, hzero,
    hzero', Nat.mod_eq_of_lt hservice_bounded]
    using hhost

theorem wordFfiToRiscV_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (wordHandler : FunName → Word width →
      Word width → Word width → Word width → State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (service : Nat) (configurationRegister configurationLengthRegister
      arrayRegister arrayLengthRegister : Fin 32)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hconfiguration : registerOfNat configuration = some configurationRegister)
    (hconfigurationLength : registerOfNat configurationLength =
      some configurationLengthRegister)
    (harray : registerOfNat array = some arrayRegister)
    (harrayLength : registerOfNat arrayLength = some arrayLengthRegister)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configurationRegister, configurationLengthRegister, arrayRegister,
        arrayLengthRegister] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhandler : host service
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister)
      (executeInstructions state
        [.addi 10 configurationRegister (0#width),
         .addi 11 configurationLengthRegister (0#width),
         .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      wordHandler function
        (readRegister state configurationRegister)
        (readRegister state configurationLengthRegister)
        (readRegister state arrayRegister)
        (readRegister state arrayLengthRegister) state) :
    (wordFfiToRiscV context function configuration configurationLength array
      arrayLength).bind (fun code =>
        (executeInstructionsWithFfi host state code).map (fun result =>
          (result, ([] : List (Word width))))) =
      evalWordFfi wordHandler 1 state
        (.ffi function configuration configurationLength array arrayLength ([], [])) := by
  have h10 : registerOfNat 10 = some 10 := by decide
  have h11 : registerOfNat 11 = some 11 := by decide
  have h12 : registerOfNat 12 = some 12 := by decide
  have h13 : registerOfNat 13 = some 13 := by decide
  cases hwordHandler : wordHandler function
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister) state with
  | none =>
      have hhost_none : host service
          (readRegister state configurationRegister)
          (readRegister state configurationLengthRegister)
          (readRegister state arrayRegister)
          (readRegister state arrayLengthRegister)
          (executeInstructions state
            [.addi 10 configurationRegister (0#width),
             .addi 11 configurationLengthRegister (0#width),
             .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
             .addi 14 0 (BitVec.ofNat width service)]) = none := by
        simpa [hwordHandler] using hhandler
      have hexecuted : executeInstructionsWithFfi host state
          [.addi 10 configurationRegister (0#width),
           .addi 11 configurationLengthRegister (0#width),
           .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
           .addi 14 0 (BitVec.ofNat width service), .ecall] = none :=
        executeInstructionsWithFfi_wordFfi_abi host state service
          configurationRegister configurationLengthRegister arrayRegister
          arrayLengthRegister none hservice_bounded hzero hsource hhost_none
      simp [wordFfiToRiscV, hservice, wordRegisterMoves, h10, h11, h12, h13,
        
        hconfiguration, hconfigurationLength, harray, harrayLength,
        evalWordFfi, hwordHandler, hexecuted]
  | some resultState =>
      have hhost_some : host service
          (readRegister state configurationRegister)
          (readRegister state configurationLengthRegister)
          (readRegister state arrayRegister)
          (readRegister state arrayLengthRegister)
          (executeInstructions state
            [.addi 10 configurationRegister (0#width),
             .addi 11 configurationLengthRegister (0#width),
             .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
             .addi 14 0 (BitVec.ofNat width service)]) = some resultState := by
        simpa [hwordHandler] using hhandler
      have hexecuted := executeInstructionsWithFfi_wordFfi_abi host state service
        configurationRegister configurationLengthRegister arrayRegister
        arrayLengthRegister (some resultState) hservice_bounded hzero hsource hhost_some
      simp [wordFfiToRiscV, hservice, wordRegisterMoves, h10, h11, h12, h13,
        
        hconfiguration, hconfigurationLength, harray, harrayLength,
        evalWordFfi, hwordHandler, hexecuted]

/-!
The previous theorem compares the raw FFI selector with the one-step Word
semantics.  This wrapper lifts that agreement through the compiler's
call-aware `WordProg` entry point, making the generated code and the
fuel-bounded handler-aware evaluator share one semantic statement.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_ffi_simulation
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width)
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (service : Nat) (configurationRegister configurationLengthRegister
      arrayRegister arrayLengthRegister : Fin 32)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hconfiguration : registerOfNat configuration = some configurationRegister)
    (hconfigurationLength : registerOfNat configurationLength =
      some configurationLengthRegister)
    (harray : registerOfNat array = some arrayRegister)
    (harrayLength : registerOfNat arrayLength = some arrayLengthRegister)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configurationRegister, configurationLengthRegister, arrayRegister,
        arrayLengthRegister] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhandler : host service
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister)
      (executeInstructions state
        [.addi 10 configurationRegister (0#width),
         .addi 11 configurationLengthRegister (0#width),
         .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      wordHandler function
        (readRegister state configurationRegister)
        (readRegister state configurationLengthRegister)
        (readRegister state arrayRegister)
        (readRegister state arrayLengthRegister) state) :
    (wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := context.services } : WordCallFfiContext width)
      (.ffi function configuration configurationLength array arrayLength ([], []))).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, ([] : List (Word width))))) =
      evalWordFunctionWithCallsAndFfi [] wordHandler 1 state
        (.ffi function configuration configurationLength array arrayLength ([], [])) := by
  simpa [wordFunctionToRiscVWithCallsAndFfi, Option.bind_assoc,
    evalWordFunctionWithCallsAndFfi] using
    (wordFfiToRiscV_execute_agreement context host wordHandler state function
      configuration configurationLength array arrayLength service
      configurationRegister configurationLengthRegister arrayRegister
      arrayLengthRegister hservice hservice_bounded hconfiguration
      hconfigurationLength harray harrayLength hzero hsource hhandler)

/-!
The one-step FFI theorem composes with the compiler's sequencing rule.  A
normal first component contributes code without return values, while the
second component determines the return-register list of the whole sequence.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_seq_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfi context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState) :
    (wordFunctionToRiscVWithCallsAndFfi context (.seq first second)).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, returns))) =
      some (finalState, returns) := by
  simp [wordFunctionToRiscVWithCallsAndFfi, hfirstCompile, hsecondCompile,
    executeInstructionsWithFfi_append, hfirstExec, hsecondExec]

end Flapjack.RiscV
