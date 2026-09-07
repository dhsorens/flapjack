import Flapjack.RiscV.Ffi

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
