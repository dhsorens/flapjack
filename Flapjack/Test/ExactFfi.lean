import Flapjack.RiscV.ExactFfi

/-! Regression tests for the exact byte-level RISC-V FFI adapter. -/

namespace Flapjack.RiscV

def exactFfiMachine : State 64 :=
  let state := zeroState 64
  let state := writeRegister state 1 10
  let state := writeRegister state 2 1
  let state := writeRegister state 3 20
  writeRegister state 4 2

def exactFfiMachineWithBytes : State 64 :=
  { exactFfiMachine with
    memory := fun address =>
      if address = 10 then BitVec.ofNat 8 42 else
      if address = 20 then BitVec.ofNat 8 9 else
      if address = 21 then BitVec.ofNat 8 8 else 0 }

def exactFfiState : ExactRiscVFfiState 64 Unit :=
  { machine := exactFfiMachineWithBytes
    ffi :=
      { oracle := fun _ state _ bytes => .returned state bytes
        state := ()
        ioEvents := [] } }

def exactFfiResultBytes (address : Word 64) (length : Nat)
    (expected : List UInt8) : ExactRiscVFfiResult 64 Unit → Bool
  | .normal state => exactReadBytes state.machine address length == expected
  | .final _ _ | .error _ => false

def exactFfiResultEvents (expected : List FfiEvent) :
    ExactRiscVFfiResult 64 Unit → Bool
  | .normal state => state.ffi.ioEvents == expected
  | .final _ _ | .error _ => false

example :
    match wordFfiToRiscV
        { services := [("echo", 7)] } "echo" 1 2 3 4 with
    | some code =>
        exactFfiResultBytes 20 2 [9, 8]
            (executeInstructionsWithExactFfi
              { services := [("echo", 7)] } exactFfiState code) = true ∧
        exactFfiResultEvents
          [{ name := .extCall "echo", configuration := [42],
             bytes := [(9, 9), (8, 8)] }]
            (executeInstructionsWithExactFfi
              { services := [("echo", 7)] } exactFfiState code) = true
    | none => False := by
  have hcode : wordFfiToRiscV
      { services := [("echo", 7)] } "echo" 1 2 3 4 =
      some ([.addi 10 1 0, .addi 11 2 0, .addi 12 3 0,
        .addi 13 4 0, .addi 14 0 (BitVec.ofNat 64 7), .ecall] :
        List (Instruction 64)) := by
    decide
  rw [hcode]
  decide

example :
    executeWithExactFfi
      { services := [("echo", 7)] } exactFfiState
      (.addi 1 0 99) =
      .normal { exactFfiState with
        machine := execute exactFfiState.machine (.addi 1 0 99) } := by
  rfl

example :
    executeWithExactFfi
      { services := [] } exactFfiState
      (.ecall) = .error exactFfiState := by
  rfl

end Flapjack.RiscV
