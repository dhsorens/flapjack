import Flapjack.StackAlloc.Machine

/-!
# Word-to-Stack FFI ABI correctness

The Word-to-Stack pass emits four ordinary StackLang moves followed by the
foreign-call node.  This file connects that generated prefix to the
FFI-aware StackLang evaluator.  The result is deliberately stated with the
intermediate machine states exposed: callers can discharge the four move
obligations using the lower-level preservation theorem in `WordToStack`.
-/

namespace Flapjack.RiscV

theorem evalStackProgFuelWithCodeAndFfi_wordStackMove
    [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination : Nat) (sourceLocation : WordLocation)
    (move : StackProg Nat)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hmove : wordStackFfiMove config source destination = some move)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state move =
      some (.normal final) := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      by_cases hsame : register = destination
      · simp [wordStackFfiMove, wordStackLocation, 
          hsource, hsame] at hmove heval
        cases hmove
        cases heval
        rfl
      · simp [wordStackFfiMove, wordStackLocation, 
          hsource, hsame] at hmove heval
        cases hmove
        cases heval
        rfl
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at hmove heval
      cases hmove
      cases heval
      rfl

theorem wordStackFfiMove_ne_skip
    (config : WordStackConfig) (source destination : Nat)
    (sourceLocation : WordLocation) (move : StackProg Nat)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination : sourceLocation ≠ .register destination)
    (hmove : wordStackFfiMove config source destination = some move) :
    move ≠ .skip := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      have hregister : register ≠ destination := by
        intro heq
        apply hdestination
        simp [heq]
      simp [wordStackFfiMove, wordStackLocation, 
        hsource, hregister] at hmove
      cases hmove
      simp
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at hmove
      cases hmove
      simp

theorem wordStackJoin_eq_seq_of_ne_skip
    (first second : StackProg Nat)
    (hfirst : first ≠ .skip) (hsecond : second ≠ .skip) :
    wordStackJoin first second = .seq first second := by
  cases first <;> cases second <;> simp_all [wordStackJoin]

theorem wordStackFfi_eq_join
    (config : WordStackConfig) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (hsafe : wordStackFfiSourcesSafe config
      [configuration, configurationLength, array, arrayLength] = true)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove : wordStackFfiMove config configurationLength 11 =
      some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove) :
    wordStackFfi config function configuration configurationLength array
      arrayLength =
      some (wordStackJoin configurationMove
        (wordStackJoin configurationLengthMove
          (wordStackJoin arrayMove
            (wordStackJoin arrayLengthMove
              (.ffi function 10 11 12 13 0))))) := by
  simp [wordStackFfi, hsafe, hconfigurationMove,
    hconfigurationLengthMove, harrayMove, harrayLengthMove]

theorem evalStackProgFuelWithCodeAndFfi_seq_normal_result [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (state middle : WordStackMachineState width)
    (first second : StackProg Nat)
    (result : Option (StackMachineControl width))
    (hfirst : evalStackProgFuelWithCodeAndFfi host fuel code state first =
      some (.normal middle))
    (hsecond : evalStackProgFuelWithCodeAndFfi host fuel code middle second =
      result) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 1) code state
      (.seq first second) = result := by
  simp [evalStackProgFuelWithCodeAndFfi, hfirst, hsecond]

theorem evalStackProgFuelWithCodeAndFfi_wordStackFfi_join [NeZero width]
    (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig) (state state1 state2 state3 final :
      WordStackMachineState width)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hconfigurationDestination : configurationLocation ≠ .register 10)
    (hconfigurationLengthDestination :
      configurationLengthLocation ≠ .register 11)
    (harrayDestination : arrayLocation ≠ .register 12)
    (harrayLengthDestination : arrayLengthLocation ≠ .register 13)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove : wordStackFfiMove config configurationLength 11 =
      some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine state) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 5) code state
      (wordStackJoin configurationMove
        (wordStackJoin configurationLengthMove
          (wordStackJoin arrayMove
            (wordStackJoin arrayLengthMove
              (.ffi function 10 11 12 13 0))))) =
      (host function (final.registers 10) (final.registers 11)
        (final.registers 12) (final.registers 13) final).map .normal := by
  have hconfigurationMoveNe := wordStackFfiMove_ne_skip config configuration 10
    configurationLocation configurationMove hconfiguration
    hconfigurationDestination hconfigurationMove
  have hconfigurationLengthMoveNe := wordStackFfiMove_ne_skip config
    configurationLength 11 configurationLengthLocation configurationLengthMove
    hconfigurationLength hconfigurationLengthDestination hconfigurationLengthMove
  have harrayMoveNe := wordStackFfiMove_ne_skip config array 12 arrayLocation
    arrayMove harray harrayDestination harrayMove
  have harrayLengthMoveNe := wordStackFfiMove_ne_skip config arrayLength 13
    arrayLengthLocation arrayLengthMove harrayLength harrayLengthDestination
    harrayLengthMove
  have hffiNe : (.ffi function 10 11 12 13 0 : StackProg Nat) ≠ .skip := by
    simp
  have hjoin4Ne : wordStackJoin arrayLengthMove
      (.ffi function 10 11 12 13 0 : StackProg Nat) ≠ .skip := by
    rw [wordStackJoin_eq_seq_of_ne_skip arrayLengthMove _
      harrayLengthMoveNe hffiNe]
    simp
  have hjoin3Ne : wordStackJoin arrayMove
      (wordStackJoin arrayLengthMove
        (.ffi function 10 11 12 13 0 : StackProg Nat)) ≠ .skip := by
    rw [wordStackJoin_eq_seq_of_ne_skip arrayMove _ harrayMoveNe hjoin4Ne]
    simp
  have hjoin2Ne : wordStackJoin configurationLengthMove
      (wordStackJoin arrayMove
        (wordStackJoin arrayLengthMove
          (.ffi function 10 11 12 13 0 : StackProg Nat))) ≠ .skip := by
    rw [wordStackJoin_eq_seq_of_ne_skip configurationLengthMove _
      hconfigurationLengthMoveNe hjoin3Ne]
    simp
  have hmove1 := evalStackProgFuelWithCodeAndFfi_wordStackMove host (fuel + 3)
    code config state state1 configuration 10 configurationLocation
    configurationMove hconfiguration hconfigurationMove hevalConfiguration
  have hmove2 := evalStackProgFuelWithCodeAndFfi_wordStackMove host (fuel + 2)
    code config state1 state2 configurationLength 11
    configurationLengthLocation configurationLengthMove hconfigurationLength
    hconfigurationLengthMove hevalConfigurationLength
  have hmove3 := evalStackProgFuelWithCodeAndFfi_wordStackMove host (fuel + 1)
    code config state2 state3 array 12 arrayLocation arrayMove harray
    harrayMove hevalArray
  have hmove4 := evalStackProgFuelWithCodeAndFfi_wordStackMove host fuel code
    config state3 final arrayLength 13 arrayLengthLocation arrayLengthMove
    harrayLength harrayLengthMove hevalArrayLength
  have hffi := evalStackProgFuelWithCodeAndFfi_ffi host fuel code final
    function 10 11 12 13 0
  have hjoin4 := evalStackProgFuelWithCodeAndFfi_seq_normal_result (host := host)
    (fuel := fuel + 1) (code := code) (state := state3) (middle := final)
    (first := arrayLengthMove)
    (second := (.ffi function 10 11 12 13 0 : StackProg Nat))
    (result := (host function (final.registers 10) (final.registers 11)
      (final.registers 12) (final.registers 13) final).map .normal)
    hmove4 hffi
  have hjoin3 := evalStackProgFuelWithCodeAndFfi_seq_normal_result (host := host)
    (fuel := fuel + 2) (code := code) (state := state2) (middle := state3)
    (first := arrayMove)
    (second := .seq arrayLengthMove
      (.ffi function 10 11 12 13 0 : StackProg Nat))
    (result := (host function (final.registers 10) (final.registers 11)
      (final.registers 12) (final.registers 13) final).map .normal)
    hmove3 hjoin4
  have hjoin2 := evalStackProgFuelWithCodeAndFfi_seq_normal_result (host := host)
    (fuel := fuel + 3) (code := code) (state := state1) (middle := state2)
    (first := configurationLengthMove)
    (second := .seq arrayMove (.seq arrayLengthMove
      (.ffi function 10 11 12 13 0 : StackProg Nat)))
    (result := (host function (final.registers 10) (final.registers 11)
      (final.registers 12) (final.registers 13) final).map .normal)
    hmove2 hjoin3
  have hjoined := evalStackProgFuelWithCodeAndFfi_seq_normal_result (host := host)
    (fuel := fuel + 4) (code := code) (state := state) (middle := state1)
    (first := configurationMove)
    (second := .seq configurationLengthMove (.seq arrayMove
      (.seq arrayLengthMove
        (.ffi function 10 11 12 13 0 : StackProg Nat))))
    (result := (host function (final.registers 10) (final.registers 11)
      (final.registers 12) (final.registers 13) final).map .normal)
    hmove1 hjoin2
  have hshape : wordStackJoin configurationMove
      (wordStackJoin configurationLengthMove
        (wordStackJoin arrayMove
          (wordStackJoin arrayLengthMove
            (.ffi function 10 11 12 13 0 : StackProg Nat)))) =
      .seq configurationMove (.seq configurationLengthMove
        (.seq arrayMove (.seq arrayLengthMove
          (.ffi function 10 11 12 13 0 : StackProg Nat)))) := by
    rw [wordStackJoin_eq_seq_of_ne_skip arrayLengthMove _
      harrayLengthMoveNe hffiNe]
    rw [wordStackJoin_eq_seq_of_ne_skip arrayMove _ harrayMoveNe (by simp)]
    rw [wordStackJoin_eq_seq_of_ne_skip configurationLengthMove _
      hconfigurationLengthMoveNe (by simp)]
    rw [wordStackJoin_eq_seq_of_ne_skip configurationMove _
      hconfigurationMoveNe (by simp)]
  rw [hshape]
  exact hjoined

theorem evalStackProgFuelWithCodeAndFfi_wordStackFfi_source_values
    [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig) (state state1 state2 state3 final :
      WordStackMachineState width)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      Word width)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hconfigurationDestination : configurationLocation ≠ .register 10)
    (hconfigurationLengthDestination :
      configurationLengthLocation ≠ .register 11)
    (harrayDestination : arrayLocation ≠ .register 12)
    (harrayLengthDestination : arrayLengthLocation ≠ .register 13)
    (hsafe : ∀ location, location ∈
      [configurationLocation, configurationLengthLocation, arrayLocation,
        arrayLengthLocation] →
      ∀ destination, destination ∈ [10, 11, 12, 13] →
        location ≠ .register destination)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove : wordStackFfiMove config configurationLength 11 =
      some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove)
    (hconfigurationValue : wordStackMachineValue config state configuration =
      some configurationValue)
    (hconfigurationLengthValue :
      wordStackMachineValue config state configurationLength =
        some configurationLengthValue)
    (harrayValue : wordStackMachineValue config state array =
      some arrayValue)
    (harrayLengthValue :
      wordStackMachineValue config state arrayLength =
        some arrayLengthValue)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine state) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    evalStackProgFuelWithCodeAndFfi host (fuel + 5) code state
      (wordStackJoin configurationMove
        (wordStackJoin configurationLengthMove
          (wordStackJoin arrayMove
            (wordStackJoin arrayLengthMove
              (.ffi function 10 11 12 13 0))))) =
      (host function configurationValue configurationLengthValue
        arrayValue arrayLengthValue final).map .normal := by
  have habi := evalWordStackMachine_ffi_argument_moves
    (config := config) (state := state) (state1 := state1)
    (state2 := state2) (state3 := state3) (final := final)
    (configuration := configuration)
    (configurationLength := configurationLength) (array := array)
    (arrayLength := arrayLength)
    (configurationLocation := configurationLocation)
    (configurationLengthLocation := configurationLengthLocation)
    (arrayLocation := arrayLocation)
    (arrayLengthLocation := arrayLengthLocation)
    hconfiguration hconfigurationLength harray harrayLength hsafe
    hevalConfiguration hevalConfigurationLength hevalArray hevalArrayLength
  have hconfigurationRegister : final.registers 10 = configurationValue := by
    apply Option.some.inj
    exact habi.1.trans hconfigurationValue
  have hconfigurationLengthRegister :
      final.registers 11 = configurationLengthValue := by
    apply Option.some.inj
    exact habi.2.1.trans hconfigurationLengthValue
  have harrayRegister : final.registers 12 = arrayValue := by
    apply Option.some.inj
    exact habi.2.2.1.trans harrayValue
  have harrayLengthRegister :
      final.registers 13 = arrayLengthValue := by
    apply Option.some.inj
    exact habi.2.2.2.trans harrayLengthValue
  have hstack := evalStackProgFuelWithCodeAndFfi_wordStackFfi_join
    (host := host) (fuel := fuel) (code := code) (config := config)
    (state := state) (state1 := state1) (state2 := state2)
    (state3 := state3) (final := final) (function := function)
    (configuration := configuration)
    (configurationLength := configurationLength) (array := array)
    (arrayLength := arrayLength)
    (configurationLocation := configurationLocation)
    (configurationLengthLocation := configurationLengthLocation)
    (arrayLocation := arrayLocation)
    (arrayLengthLocation := arrayLengthLocation)
    (configurationMove := configurationMove)
    (configurationLengthMove := configurationLengthMove)
    (arrayMove := arrayMove) (arrayLengthMove := arrayLengthMove)
    hconfiguration hconfigurationLength harray harrayLength
    hconfigurationDestination hconfigurationLengthDestination
    harrayDestination harrayLengthDestination
    hconfigurationMove hconfigurationLengthMove harrayMove harrayLengthMove
    hevalConfiguration hevalConfigurationLength hevalArray hevalArrayLength
  simpa [hconfigurationRegister, hconfigurationLengthRegister,
    harrayRegister, harrayLengthRegister] using hstack

/-! Lift the FFI prefix theorem through the actual Word-to-Stack compiler.
    Keeping the compiler option in the statement makes failed lowering
    observable and lets callers compose this result with the surrounding
    `wordToStackProgWord` recursion. -/

theorem evalStackProgFuelWithCodeAndFfi_wordToStackProgWord_ffi
    [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig) (state state1 state2 state3 final :
      WordStackMachineState width)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      Word width)
    (hsafe : wordStackFfiSourcesSafe config
      [configuration, configurationLength, array, arrayLength] = true)
    (hsafeLocations : ∀ location, location ∈
      [configurationLocation, configurationLengthLocation, arrayLocation,
        arrayLengthLocation] →
      ∀ destination, destination ∈ [10, 11, 12, 13] →
        location ≠ .register destination)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hconfigurationDestination : configurationLocation ≠ .register 10)
    (hconfigurationLengthDestination :
      configurationLengthLocation ≠ .register 11)
    (harrayDestination : arrayLocation ≠ .register 12)
    (harrayLengthDestination : arrayLengthLocation ≠ .register 13)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove :
      wordStackFfiMove config configurationLength 11 =
        some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove)
    (hconfigurationValue : wordStackMachineValue config state configuration =
      some configurationValue)
    (hconfigurationLengthValue :
      wordStackMachineValue config state configurationLength =
        some configurationLengthValue)
    (harrayValue : wordStackMachineValue config state array =
      some arrayValue)
    (harrayLengthValue : wordStackMachineValue config state arrayLength =
      some arrayLengthValue)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine state) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    (wordToStackProgWord config
      ((.ffi function configuration configurationLength array arrayLength live) :
        WordProg (Word width))).bind
        (fun program => evalStackProgFuelWithCodeAndFfi host (fuel + 5)
          code state program) =
      (host function configurationValue configurationLengthValue
        arrayValue arrayLengthValue final).map .normal := by
  have hstack := evalStackProgFuelWithCodeAndFfi_wordStackFfi_source_values
    (host := host) (fuel := fuel) (code := code) (config := config)
    (state := state) (state1 := state1) (state2 := state2)
    (state3 := state3) (final := final) (function := function)
    (configuration := configuration)
    (configurationLength := configurationLength) (array := array)
    (arrayLength := arrayLength)
    (configurationLocation := configurationLocation)
    (configurationLengthLocation := configurationLengthLocation)
    (arrayLocation := arrayLocation)
    (arrayLengthLocation := arrayLengthLocation)
    (configurationMove := configurationMove)
    (configurationLengthMove := configurationLengthMove)
    (arrayMove := arrayMove) (arrayLengthMove := arrayLengthMove)
    (configurationValue := configurationValue)
    (configurationLengthValue := configurationLengthValue)
    (arrayValue := arrayValue) (arrayLengthValue := arrayLengthValue)
    hconfiguration hconfigurationLength harray harrayLength
    hconfigurationDestination hconfigurationLengthDestination
    harrayDestination harrayLengthDestination hsafeLocations
    hconfigurationMove hconfigurationLengthMove harrayMove harrayLengthMove
    hconfigurationValue hconfigurationLengthValue harrayValue harrayLengthValue
    hevalConfiguration hevalConfigurationLength hevalArray hevalArrayLength
  have hcompile : wordToStackProgWord config
      ((.ffi function configuration configurationLength array arrayLength live) :
        WordProg (Word width)) =
      some (wordStackJoin configurationMove
        (wordStackJoin configurationLengthMove
          (wordStackJoin arrayMove
            (wordStackJoin arrayLengthMove
              (.ffi function 10 11 12 13 0)))) ) := by
    simp [wordToStackProgWord, wordProgToNat, wordToStackProgNat,
      wordStackFfi, hsafe, hconfigurationMove, hconfigurationLengthMove,
      harrayMove, harrayLengthMove]
  rw [hcompile]
  simpa using hstack

/-! The stateful lowering keeps the bitmap accumulator threaded through a
    handler body.  This equation exposes the generated handler call and the
    final bitmap state together, which is the compiler-side premise needed by
    a later frame-machine simulation theorem. -/

theorem wordToStackProgNatWithBitmapBuilder_call_handler
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state finalState : WordStackBitmapState)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat))
    (target : Nat) (arguments : List Nat)
    (exception handlerLabel entryLabel : Nat)
    (body : WordProg Nat)
    (argumentMoves returnCode handlerCode : StackProg Nat)
    (hargs : wordStackMovesToPhysical config arguments 2 = some argumentMoves)
    (hreturn : wordStackReturnCode config returns = some returnCode)
    (hhandler : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
      some (handlerCode, finalState)) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount
      bitmapRegister frameSlots wordBits storeConstsStub state
      (.call returns (some target) arguments
        (some (exception, body, handlerLabel, entryLabel))) =
      some (wordStackJoin argumentMoves
        (wordToStackCallWithHandler config.perf target arguments.length
          config.frameOffset config.scratch returnCode handlerCode
          config.returnLabel config.entryLabel config.handlerLabel exception),
        finalState) := by
  simp [wordToStackProgNatWithBitmapBuilder, hargs, hreturn, hhandler]

theorem wordToStackProgNatWithBitmapBuilder_call_no_handler
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat))
    (target : Nat) (arguments : List Nat)
    (argumentMoves returnCode : StackProg Nat)
    (hargs : wordStackMovesToPhysical config arguments 2 = some argumentMoves)
    (hreturn : wordStackReturnCode config returns = some returnCode)
    (hreturns : returns ≠ none) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount
      bitmapRegister frameSlots wordBits storeConstsStub state
      (.call returns (some target) arguments none) =
      some (wordStackJoin argumentMoves
        (wordToStackCallNoHandler config.perf target arguments.length
          config.frameOffset config.scratch
          (returns.map (fun result => result.1) |>.getD []) returnCode
          config.returnLabel config.entryLabel), state) := by
  simp only [wordToStackProgNatWithBitmapBuilder]
  rw [wordToStackProgNat]
  simp_all [wordStackReturnCode]
  all_goals exact hreturns

/-! The handler-call lowering equation composes with bounded StackLang
    execution.  Argument moves are kept as an explicit premise because their
    machine-level proof depends on the caller's location relation; once they
    establish the intermediate state, the generated call code can be supplied
    with the corresponding callee/handler execution equation. -/

theorem evalStackProgFuelWithCodeAndFfi_wordToStackProgNatWithBitmapBuilder_call_handler
    [BEq Nat] [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (machineState middle : WordStackMachineState width)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat))
    (target : Nat) (arguments : List Nat)
    (exception handlerLabel entryLabel : Nat)
    (body : WordProg Nat)
    (argumentMoves returnCode handlerCode : StackProg Nat)
    (finalState : WordStackBitmapState)
    (result : StackMachineControl width)
    (hargs : wordStackMovesToPhysical config arguments 2 = some argumentMoves)
    (hreturn : wordStackReturnCode config returns = some returnCode)
    (hhandler : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub bitmapState body =
      some (handlerCode, finalState))
    (hargumentMovesNe : argumentMoves ≠ .skip)
    (hmove : evalStackProgFuelWithCodeAndFfi host fuel code machineState
      argumentMoves = some (.normal middle))
    (hcall : evalStackProgFuelWithCodeAndFfi host fuel code middle
      (wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception) =
      some result) :
    (wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub bitmapState
      (.call returns (some target) arguments
        (some (exception, body, handlerLabel, entryLabel)))).bind
        (fun compiled =>
          (evalStackProgFuelWithCodeAndFfi host (fuel + 1) code machineState
            compiled.1).map (fun control => (control, compiled.2))) =
      some (result, finalState) := by
  have hcompile := wordToStackProgNatWithBitmapBuilder_call_handler
    (config := config) (bitmapBuilder := bitmapBuilder)
    (registerCount := registerCount) (bitmapRegister := bitmapRegister)
    (frameSlots := frameSlots) (wordBits := wordBits)
    (storeConstsStub := storeConstsStub) (state := bitmapState)
    (returns := returns) (target := target) (arguments := arguments)
    (exception := exception) (handlerLabel := handlerLabel)
    (entryLabel := entryLabel) (body := body)
    (argumentMoves := argumentMoves) (returnCode := returnCode)
    (handlerCode := handlerCode) (finalState := finalState)
    (hargs := hargs) (hreturn := hreturn) (hhandler := hhandler)
  rw [hcompile]
  simp only [Option.bind_some]
  have hcallNe :
      wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception ≠
        (.skip : StackProg Nat) := by
    simp [wordToStackCallWithHandler, stackSeq, stackPushHandler,
      stackHandlerArgs, stackArgs, stackMove, stackHandlerSlots]
  rw [wordStackJoin_eq_seq_of_ne_skip argumentMoves _ hargumentMovesNe hcallNe]
  have hseq := evalStackProgFuelWithCodeAndFfi_seq_normal_result
    (host := host) (fuel := fuel) (code := code) (state := machineState)
    (middle := middle) (first := argumentMoves)
    (second := wordToStackCallWithHandler config.perf target arguments.length
      config.frameOffset config.scratch returnCode handlerCode
      config.returnLabel config.entryLabel config.handlerLabel exception)
    (result := some result) hmove hcall
  simp [hseq]

theorem evalStackProgFuelWithCodeAndFfi_wordToStackProgNatWithBitmapBuilder_call_no_handler
    [BEq Nat] [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (machineState middle : WordStackMachineState width)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat))
    (target : Nat) (arguments : List Nat)
    (argumentMoves returnCode : StackProg Nat)
    (result : StackMachineControl width)
    (hargs : wordStackMovesToPhysical config arguments 2 = some argumentMoves)
    (hreturn : wordStackReturnCode config returns = some returnCode)
    (hreturns : returns ≠ none)
    (hargumentMovesNe : argumentMoves ≠ .skip)
    (hmove : evalStackProgFuelWithCodeAndFfi host fuel code machineState
      argumentMoves = some (.normal middle))
    (hcall : evalStackProgFuelWithCodeAndFfi host fuel code middle
      (wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch
        (returns.map (fun item => item.1) |>.getD []) returnCode
        config.returnLabel config.entryLabel) = some result) :
    (wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub bitmapState
      (.call returns (some target) arguments none)).bind
        (fun compiled =>
          (evalStackProgFuelWithCodeAndFfi host (fuel + 1) code machineState
            compiled.1).map (fun control => (control, compiled.2))) =
      some (result, bitmapState) := by
  have hcompile := wordToStackProgNatWithBitmapBuilder_call_no_handler
    (config := config) (bitmapBuilder := bitmapBuilder)
    (registerCount := registerCount) (bitmapRegister := bitmapRegister)
    (frameSlots := frameSlots) (wordBits := wordBits)
    (storeConstsStub := storeConstsStub) (state := bitmapState)
    (returns := returns) (target := target) (arguments := arguments)
    (argumentMoves := argumentMoves) (returnCode := returnCode)
    (hargs := hargs) (hreturn := hreturn) (hreturns := hreturns)
  rw [hcompile]
  simp only [Option.bind_some]
  have hcallNe :
      wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch
        (returns.map (fun item => item.1) |>.getD []) returnCode
        config.returnLabel config.entryLabel ≠ (.skip : StackProg Nat) := by
    simp [wordToStackCallNoHandler, stackSeq, stackArgs, stackMove]
  rw [wordStackJoin_eq_seq_of_ne_skip argumentMoves _ hargumentMovesNe hcallNe]
  have hseq := evalStackProgFuelWithCodeAndFfi_seq_normal_result
    (host := host) (fuel := fuel) (code := code) (state := machineState)
    (middle := middle) (first := argumentMoves)
    (second := wordToStackCallNoHandler config.perf target arguments.length
      config.frameOffset config.scratch
      (returns.map (fun item => item.1) |>.getD []) returnCode
      config.returnLabel config.entryLabel)
    (result := some result) hmove hcall
  simp [hseq]

/-! The state-threaded compiler composes the results of sequential source
    programs.  Keeping both intermediate states in the theorem makes the
    equation useful for composing an allocating prefix with a later FFI or
    handler body. -/

theorem wordToStackProgNatWithBitmapBuilder_seq
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat)
    (state state1 finalState : WordStackBitmapState)
    (first second : WordProg Nat)
    (firstCode secondCode : StackProg Nat)
    (hfirst : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state first =
      some (firstCode, state1))
    (hsecond : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state1 second =
      some (secondCode, finalState)) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state
      (.seq first second) =
      some (.seq firstCode secondCode, finalState) := by
  simp [wordToStackProgNatWithBitmapBuilder, hfirst, hsecond]

/-! Conditional compilation threads the bitmap state through the two branch
    compilations in the same order as the executable compiler.  The explicit
    condition-prelude witness keeps this equation compositional for spilled
    conditions as well. -/

theorem wordToStackProgNatWithBitmapBuilder_ite
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat)
    (state state1 finalState : WordStackBitmapState)
    (operator : Cmp) (condition : Nat) (right : WordRegImm Nat)
    (thenBranch elseBranch : WordProg Nat)
    (conditionPrelude : StackProg Nat) (conditionRegister : Nat)
    (rightOperand : WordRegImm Nat)
    (thenCode elseCode : StackProg Nat)
    (hcondition : wordStackConditionOperands config condition right =
      some (conditionPrelude, conditionRegister, rightOperand))
    (hthen : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state
      thenBranch = some (thenCode, state1))
    (helse : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state1
      elseBranch = some (elseCode, finalState)) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state
      (.ite operator condition right thenBranch elseBranch) =
      some (wordStackJoin conditionPrelude
        (.ite operator conditionRegister rightOperand thenCode elseCode),
        finalState) := by
  simp [wordToStackProgNatWithBitmapBuilder, hcondition, hthen, helse]

/-! Loops compile their body once, threading the body's bitmap state to the
    surrounding continuation.  `MustTerminate` is the corresponding
    structural wrapper and preserves the body compiler result unchanged. -/

theorem wordToStackProgNatWithBitmapBuilder_loop
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat)
    (state finalState : WordStackBitmapState)
    (liveIn liveOut : List Nat) (body : WordProg Nat)
    (bodyCode : StackProg Nat)
    (hbody : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
      some (bodyCode, finalState)) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state
      (.loop liveIn body liveOut) =
      some (.loop bodyCode, finalState) := by
  simp [wordToStackProgNatWithBitmapBuilder, hbody]

theorem wordToStackProgNatWithBitmapBuilder_mustTerminate
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat)
    (state finalState : WordStackBitmapState)
    (body : WordProg Nat) (bodyCode : StackProg Nat)
    (hbody : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
      some (bodyCode, finalState)) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state
      (.mustTerminate body) =
      some (bodyCode, finalState) := by
  simpa [wordToStackProgNatWithBitmapBuilder] using hbody

/-! The state-threaded compiler has no special bitmap effect for an FFI
    instruction.  Its lowering equation therefore returns the original
    accumulator while exposing the same four-move ABI prefix as the
    stateless compiler. -/

theorem wordToStackProgNatWithBitmapBuilder_ffi
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (hsafe : wordStackFfiSourcesSafe config
      [configuration, configurationLength, array, arrayLength] = true)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove :
      wordStackFfiMove config configurationLength 11 =
        some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove) :
    wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount
      bitmapRegister frameSlots wordBits storeConstsStub state
      (.ffi function configuration configurationLength array arrayLength live) =
      some (wordStackJoin configurationMove
        (wordStackJoin configurationLengthMove
          (wordStackJoin arrayMove
            (wordStackJoin arrayLengthMove
              (.ffi function 10 11 12 13 0)))), state) := by
  simp [wordToStackProgNatWithBitmapBuilder, wordToStackProgNat, wordStackFfi, hsafe,
    hconfigurationMove, hconfigurationLengthMove, harrayMove,
    harrayLengthMove]

/-! Combine the state-threaded compiler equation with the bounded StackLang
    evaluator.  The bitmap accumulator is an explicit component of the
    result, so this theorem records that an FFI action does not alter it. -/

theorem evalStackProgFuelWithCodeAndFfi_wordToStackProgNatWithBitmapBuilder_ffi
    [BEq Nat] [NeZero width] (host : StackMachineFfiHandler width)
    (fuel : Nat) (code : Nat → Option (StackProg Nat))
    (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (machineState state1 state2 state3 final : WordStackMachineState width)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (configurationMove configurationLengthMove arrayMove arrayLengthMove :
      StackProg Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      Word width)
    (hsafe : wordStackFfiSourcesSafe config
      [configuration, configurationLength, array, arrayLength] = true)
    (hsafeLocations : ∀ location, location ∈
      [configurationLocation, configurationLengthLocation, arrayLocation,
        arrayLengthLocation] →
      ∀ destination, destination ∈ [10, 11, 12, 13] →
        location ≠ .register destination)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hconfigurationDestination : configurationLocation ≠ .register 10)
    (hconfigurationLengthDestination :
      configurationLengthLocation ≠ .register 11)
    (harrayDestination : arrayLocation ≠ .register 12)
    (harrayLengthDestination : arrayLengthLocation ≠ .register 13)
    (hconfigurationMove : wordStackFfiMove config configuration 10 =
      some configurationMove)
    (hconfigurationLengthMove :
      wordStackFfiMove config configurationLength 11 =
        some configurationLengthMove)
    (harrayMove : wordStackFfiMove config array 12 = some arrayMove)
    (harrayLengthMove : wordStackFfiMove config arrayLength 13 =
      some arrayLengthMove)
    (hconfigurationValue : wordStackMachineValue config machineState
      configuration = some configurationValue)
    (hconfigurationLengthValue :
      wordStackMachineValue config machineState configurationLength =
        some configurationLengthValue)
    (harrayValue : wordStackMachineValue config machineState array =
      some arrayValue)
    (harrayLengthValue : wordStackMachineValue config machineState arrayLength =
      some arrayLengthValue)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine machineState) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    (wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount
      bitmapRegister frameSlots wordBits storeConstsStub bitmapState
      (.ffi function configuration configurationLength array arrayLength live)).bind
        (fun result =>
          (evalStackProgFuelWithCodeAndFfi host (fuel + 5) code machineState
            result.1).map (fun control => (control, result.2))) =
      (host function configurationValue configurationLengthValue
        arrayValue arrayLengthValue final).map
        (fun machine => (.normal machine, bitmapState)) := by
  have hcompile := wordToStackProgNatWithBitmapBuilder_ffi
    (config := config) (bitmapBuilder := bitmapBuilder)
    (registerCount := registerCount) (bitmapRegister := bitmapRegister)
    (frameSlots := frameSlots) (wordBits := wordBits)
    (storeConstsStub := storeConstsStub) (state := bitmapState)
    (function := function) (configuration := configuration)
    (configurationLength := configurationLength) (array := array)
    (arrayLength := arrayLength) (live := live)
    (configurationMove := configurationMove)
    (configurationLengthMove := configurationLengthMove)
    (arrayMove := arrayMove) (arrayLengthMove := arrayLengthMove)
    hsafe hconfigurationMove hconfigurationLengthMove harrayMove
    harrayLengthMove
  have hstack := evalStackProgFuelWithCodeAndFfi_wordStackFfi_source_values
    (host := host) (fuel := fuel) (code := code) (config := config)
    (state := machineState) (state1 := state1) (state2 := state2)
    (state3 := state3) (final := final) (function := function)
    (configuration := configuration)
    (configurationLength := configurationLength) (array := array)
    (arrayLength := arrayLength)
    (configurationLocation := configurationLocation)
    (configurationLengthLocation := configurationLengthLocation)
    (arrayLocation := arrayLocation)
    (arrayLengthLocation := arrayLengthLocation)
    (configurationMove := configurationMove)
    (configurationLengthMove := configurationLengthMove)
    (arrayMove := arrayMove) (arrayLengthMove := arrayLengthMove)
    (configurationValue := configurationValue)
    (configurationLengthValue := configurationLengthValue)
    (arrayValue := arrayValue) (arrayLengthValue := arrayLengthValue)
    hconfiguration hconfigurationLength harray harrayLength
    hconfigurationDestination hconfigurationLengthDestination
    harrayDestination harrayLengthDestination hsafeLocations
    hconfigurationMove hconfigurationLengthMove harrayMove harrayLengthMove
    hconfigurationValue hconfigurationLengthValue harrayValue harrayLengthValue
    hevalConfiguration hevalConfigurationLength hevalArray hevalArrayLength
  rw [hcompile]
  simp only [Option.bind_some]
  simpa only [Option.map_map, Function.comp_def] using
    congrArg (fun result => result.map (fun control => (control, bitmapState)))
      hstack

end Flapjack.RiscV
