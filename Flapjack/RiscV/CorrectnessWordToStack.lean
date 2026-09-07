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
      · simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
          hsource, hsame] at hmove heval
        cases hmove
        cases heval
        rfl
      · simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
          hsource, hsame] at hmove heval
        cases hmove
        cases heval
        rfl
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
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
      simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
        hsource, hregister] at hmove
      cases hmove
      simp
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, lookupNatInfo,
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

end Flapjack.RiscV
