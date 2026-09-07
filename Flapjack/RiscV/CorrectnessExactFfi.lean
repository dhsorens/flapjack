import Flapjack.RiscV.ExactFfi

/-!
# Correctness equations for the exact RISC-V FFI adapter

These lemmas expose the adapter's semantic contract independently of any
particular oracle implementation. They are the proof seam used when a
compiler-generated ECALL is related to CakeML's `callFfi` transition.
-/

namespace Flapjack.RiscV

/-!
The generated ABI prefix is ordinary RISC-V code.  Once it has run, the
following ECALL is exactly the adapter above; the only arithmetic fact needed
to expose the service number is that it fits in the machine word.
-/
theorem executeInstructionsWithExactFfi_abi [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat)
    (configuration configurationLength array arrayLength : Fin 32)
    (result : ExactRiscVFfiResult width σ)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = result) :
    executeInstructionsWithExactFfi context state
      [.addi 10 configuration (0#width),
       .addi 11 configurationLength (0#width),
       .addi 12 array (0#width),
       .addi 13 arrayLength (0#width),
       .addi 14 0 (BitVec.ofNat width service), .ecall] = result := by
  have hservice_read :
      (readRegister (executeInstructions state.machine
        [.addi 10 configuration (0#width),
         .addi 11 configurationLength (0#width),
         .addi 12 array (0#width),
         .addi 13 arrayLength (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) 14).toNat = service := by
    have hzero' : state.machine.registers 0 = 0 := by
      simpa [readRegister] using hzero
    simp [executeInstructions, execute, writeRegister, readRegister,
      nextPc, hzero', Nat.mod_eq_of_lt hservice_bounded]
  have hresult' : exactRiscVFfiCall context
      { machine := execute (execute (execute (execute
          (execute state.machine (.addi 10 configuration (0#width)))
            (.addi 11 configurationLength (0#width)))
            (.addi 12 array (0#width)))
            (.addi 13 arrayLength (0#width)))
            (.addi 14 0 (BitVec.ofNat width service)),
        ffi := state.ffi } service = result := by
    simpa [executeInstructions] using hresult
  simp only [executeInstructionsWithExactFfi, executeWithExactFfi]
  have hservice_read' :
      (readRegister
        (execute (execute (execute (execute
          (execute state.machine (.addi 10 configuration (0#width)))
            (.addi 11 configurationLength (0#width)))
            (.addi 12 array (0#width)))
            (.addi 13 arrayLength (0#width)))
            (.addi 14 0 (BitVec.ofNat width service))) 14).toNat = service := by
    simpa [executeInstructions] using hservice_read
  rw [hservice_read', hresult']
  cases result <;> rfl

theorem exactWriteBytesAux_pc [NeZero width] (address : Word width)
    (state : State width) (offset : Nat) (bytes : List UInt8) :
    (exactWriteBytesAux address state offset bytes).pc = state.pc := by
  induction bytes generalizing state offset with
  | nil => rfl
  | cons byte bytes induction =>
      simp only [exactWriteBytesAux]
      exact induction (state :=
        writeByte state (byteAddress address offset) (BitVec.ofNat 8 byte.toNat))
        (offset := offset + 1)

theorem exactWriteBytes_pc [NeZero width] (state : State width)
    (address : Word width) (bytes : List UInt8) :
    (exactWriteBytes state address bytes).pc = state.pc := by
  exact exactWriteBytesAux_pc address state 0 bytes

theorem exactRiscVFfiCall_return [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (nextState : σ) (nextBytes : List UInt8)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .returned nextState nextBytes)
    (hlength : nextBytes.length =
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat).length) :
    exactRiscVFfiCall context state service =
      .normal
        { machine :=
            { exactWriteBytes state.machine (readRegister state.machine 12)
                nextBytes with
              pc := nextPc state.machine }
          ffi :=
            { state.ffi with
              state := nextState
              ioEvents := state.ffi.ioEvents ++
                [{ name := .extCall function,
                   configuration := exactReadBytes state.machine
                     (readRegister state.machine 10)
                     (readRegister state.machine 11).toNat,
                   bytes :=
                     (exactReadBytes state.machine
                       (readRegister state.machine 12)
                       (readRegister state.machine 13).toNat).zip nextBytes }] } } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle, hlength]
  change (exactWriteBytes state.machine (readRegister state.machine 12) nextBytes).pc + 4 =
    state.machine.pc + 4
  rw [exactWriteBytes_pc]

theorem exactRiscVFfiCall_final [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (outcome : FfiOutcome)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .final outcome) :
    exactRiscVFfiCall context state service =
      .final state
        { name := .extCall function,
          configuration := exactReadBytes state.machine
            (readRegister state.machine 10)
            (readRegister state.machine 11).toNat,
          bytes := exactReadBytes state.machine
            (readRegister state.machine 12)
            (readRegister state.machine 13).toNat,
          outcome := outcome } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle]

theorem exactRiscVFfiCall_length_failure [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (nextState : σ) (nextBytes : List UInt8)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .returned nextState nextBytes)
    (hlength : nextBytes.length ≠
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat).length) :
    exactRiscVFfiCall context state service =
      .final state
        { name := .extCall function,
          configuration := exactReadBytes state.machine
            (readRegister state.machine 10)
            (readRegister state.machine 11).toNat,
          bytes := exactReadBytes state.machine
            (readRegister state.machine 12)
            (readRegister state.machine 13).toNat,
          outcome := .failed } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle, hlength]

end Flapjack.RiscV
