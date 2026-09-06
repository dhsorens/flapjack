import Flapjack.StackAlloc

/-!
# StackAlloc runtime code

This file ports the non-generational (`Simple`) branch of
`cakeml/compiler/backend/stack_allocScript.sml`.  CakeML's StackLang
instruction set has immediate arithmetic instructions, while Flapjack's
small StackLang carrier currently exposes register-register arithmetic and
`const` separately.  The helpers below materialize an immediate in the
reserved scratch register before applying the corresponding operation.

The resulting program is executable StackLang syntax.  The state-level
simulation of heap copying and bitmap forwarding is deliberately a separate
proof layer, because it requires the full StackLang heap/stack semantics and
the collector invariants from `stack_allocProofScript.sml`.
-/

namespace Flapjack

structure StackGcConfig where
  shiftLength : Nat := 11
  smallShiftLength : Nat := 9
  lenSize : Nat := 32
  wordShift : Nat := 3
  wordBits : Nat := 64
  bytesInWord : Nat := 8
  immediateScratch : Nat := 31
  deriving Repr

def stackGcMove (destination source : Nat) : StackProg Nat :=
  .arith .or destination source source

def stackGcAdd (destination source : Nat) : StackProg Nat :=
  .arith .add destination destination source

def stackGcSub (destination source : Nat) : StackProg Nat :=
  .arith .sub destination destination source

def stackGcConst (register value : Nat) : StackProg Nat :=
  .const register value

def stackGcAddImmediate (config : StackGcConfig) (register value : Nat) :
    StackProg Nat :=
  stackSeq [stackGcConst config.immediateScratch value,
    stackGcAdd register config.immediateScratch]

def stackGcSubImmediate (config : StackGcConfig) (register value : Nat) :
    StackProg Nat :=
  stackSeq [stackGcConst config.immediateScratch value,
    stackGcSub register config.immediateScratch]

def stackGcShiftImmediate (config : StackGcConfig) (operator : Shift)
    (register amount : Nat) : StackProg Nat :=
  stackSeq [stackGcConst config.immediateScratch amount,
    .shift operator register register config.immediateScratch]

def stackGcAddOne (config : StackGcConfig) (register : Nat) : StackProg Nat :=
  stackGcAddImmediate config register 1

def stackGcSubOne (config : StackGcConfig) (register : Nat) : StackProg Nat :=
  stackGcSubImmediate config register 1

def stackGcAddBytes (config : StackGcConfig) (register : Nat) : StackProg Nat :=
  stackGcAddImmediate config register config.bytesInWord

def stackGcClearTop (config : StackGcConfig) (register amount : Nat) :
    StackProg Nat :=
  let shift := config.wordBits - amount - 1
  stackSeq [stackGcShiftImmediate config .lsl register shift,
    stackGcShiftImmediate config .lsr register shift]

def stackGcWhile (operator : Cmp) (condition : Nat) (right : WordRegImm Nat)
    (body : StackProg Nat) : StackProg Nat :=
  .loop (.ite operator condition right body (.break 0))

def stackGcMemcpyBody (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    .inst (.mem .load 1 2),
    stackGcAddBytes config 2,
    stackGcSubOne config 0,
    .inst (.mem .store 1 3),
    stackGcAddBytes config 3]

def stackGcMemcpy (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notEqual 0 (.imm 0) (stackGcMemcpyBody config)

def stackGcMoveAddressPrefix (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    stackGcMove 0 5,
    .get 1 .currHeap,
    stackGcShiftImmediate config .lsr 0 config.shiftLength,
    stackGcShiftImmediate config .lsl 0 config.wordShift,
    stackGcAdd 0 1,
    .inst (.mem .load 1 0)]

def stackGcMoveCopyPrefix (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    stackGcShiftImmediate config .lsr 1 (config.wordBits - config.lenSize),
    stackGcAddOne config 1,
    stackGcMove 6 1,
    stackGcMove 2 0,
    stackGcMove 0 1]

def stackGcMoveCopySuffix (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    stackGcMemcpy config,
    stackGcMove 0 6,
    stackGcShiftImmediate config .lsl 0 config.wordShift,
    stackGcSub 2 0,
    stackGcMove 0 4,
    stackGcShiftImmediate config .lsl 0 2,
    .inst (.mem .store 0 2),
    stackGcMove 1 4,
    stackGcClearTop config 5 (config.smallShiftLength - 1),
    stackGcShiftImmediate config .lsl 1 config.shiftLength,
    .arith .or 5 5 1,
    stackGcAdd 4 6]

def stackGcMoveForwardingSuffix (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    stackGcShiftImmediate config .lsr 1 2,
    stackGcShiftImmediate config .lsl 1 config.shiftLength,
    stackGcClearTop config 5 (config.smallShiftLength - 1),
    .arith .or 5 5 1]

def stackGcMoveCode (config : StackGcConfig) : StackProg Nat :=
  .ite .test 5 (.imm 1) .skip (stackSeq [
    stackGcMoveAddressPrefix config,
    .ite .test 1 (.imm 3)
      (stackGcMoveForwardingSuffix config)
      (stackSeq [stackGcMoveCopyPrefix config,
        stackGcMoveCopySuffix config])])

def stackGcMoveListCode (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notEqual 7 (.imm 0) (stackSeq [
    .inst (.mem .load 5 8),
    stackGcSubOne config 7,
    stackGcMoveCode config,
    .inst (.mem .store 5 8),
    stackGcAddBytes config 8])

def stackGcMoveLoopCode (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notEqual 3 (.reg 8) (stackSeq [
    .inst (.mem .load 7 8),
    .ite .test 7 (.imm 4)
      (stackSeq [
        stackGcShiftImmediate config .lsr 7 (config.wordBits - config.lenSize),
        stackGcAddBytes config 8,
        stackGcMoveListCode config])
      (stackSeq [
        stackGcShiftImmediate config .lsr 7 (config.wordBits - config.lenSize),
        stackGcAddOne config 7,
        stackGcShiftImmediate config .lsl 7 config.wordShift,
        stackGcAdd 8 7])])

def stackGcMoveBitmapCode (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notLower 7 (.imm 2) (stackSeq [
    .ite .test 7 (.imm 1)
      (stackSeq [
        stackGcShiftImmediate config .lsr 7 1,
        stackGcAddBytes config 8])
      (stackSeq [
        .stackLoadAny 5 8,
        stackGcShiftImmediate config .lsr 7 1,
        stackGcMoveCode config,
        .stackStoreAny 5 8,
        stackGcAddBytes config 8])])

def stackGcMoveBitmapsCode (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notTest 0 (.reg 0) (stackSeq [
    .bitmapLoad 7 9,
    stackGcMoveBitmapCode config,
    .bitmapLoad 0 9,
    stackGcAddOne config 9,
    stackGcShiftImmediate config .lsr 0 (config.wordBits - 1)])

def stackGcMoveRootsBitmapsCode (config : StackGcConfig) : StackProg Nat :=
  stackGcWhile .notTest 9 (.reg 9) (stackSeq [
    stackGcMove 0 9,
    stackGcSubOne config 9,
    stackGcAddBytes config 8,
    stackGcMoveBitmapsCode config,
    .stackLoadAny 9 8])

def stackGcSimpleCode (config : StackGcConfig) : StackProg Nat :=
  stackSeq [
    .set .allocSize 1,
    .set .nextFree 0,
    stackGcConst 1 0,
    stackGcMove 2 1,
    .get 3 .otherHeap,
    stackGcMove 4 1,
    .get 5 .globals,
    stackGcMove 6 1,
    stackGcMove 8 1,
    stackGcMoveCode config,
    .set .globals 5,
    stackGcMove 7 5,
    stackGcShiftImmediate config .lsr 7 config.shiftLength,
    stackGcShiftImmediate config .lsl 7 config.wordShift,
    .get 9 .otherHeap,
    stackGcAdd 7 9,
    .set .globReal 7,
    stackGcConst 7 0,
    .stackLoadAny 9 8,
    stackGcMove 8 7,
    stackGcMoveRootsBitmapsCode config,
    .get 8 .otherHeap,
    stackGcMoveLoopCode config,
    .get 0 .currHeap,
    .get 1 .otherHeap,
    .get 2 .heapLength,
    stackGcAdd 2 1,
    .set .currHeap 1,
    .set .otherHeap 0,
    .get 0 .nextFree,
    .set .nextFree 8,
    .set .endOfHeap 2,
    .set .triggerGC 2,
    .get 1 .allocSize,
    stackGcSub 2 8,
    .ite .lower 2 (.reg 1)
      (stackSeq [stackGcConst 1 1, .halt 1])
      .skip]

def stackGcSimpleStub (config : StackGcConfig) : StackProg Nat :=
  stackSeq [stackGcSimpleCode config, .return 0]

/-! A runtime-backed section compiler for the RISC-V/Nat StackLang adapter.
    The ordinary `stackAllocCompile` remains the generic boundary used by
    clients whose collector configuration is not yet represented. -/
def stackAllocSimpleStubs (allocConfig : StackAllocConfig)
    (gcConfig : StackGcConfig) : List (Nat × StackProg Nat) :=
  [(allocConfig.gcStubLocation, stackGcSimpleStub gcConfig)]

def stackAllocCompileWithSimpleGc (allocConfig : StackAllocConfig)
    (gcConfig : StackGcConfig)
    (programs : List (Nat × StackProg Nat)) : List (Nat × StackProg Nat) :=
  stackAllocSimpleStubs allocConfig gcConfig ++
    programs.map (stackAllocProgram allocConfig)

theorem stackGcWhile_shape (operator : Cmp) (condition : Nat)
    (right : WordRegImm Nat) (body : StackProg Nat) :
    stackGcWhile operator condition right body =
      .loop (.ite operator condition right body (.break 0)) := by
  rfl

theorem stackGcSimpleStub_ends_in_return (config : StackGcConfig) :
    stackGcSimpleStub config = stackSeq [stackGcSimpleCode config, .return 0] := by
  rfl

theorem stackAllocCompileWithSimpleGc_emits_runtime
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (programs : List (Nat × StackProg Nat)) :
    (stackAllocCompileWithSimpleGc allocConfig gcConfig programs).head? =
      some (allocConfig.gcStubLocation, stackGcSimpleStub gcConfig) := by
  simp [stackAllocCompileWithSimpleGc, stackAllocSimpleStubs]

end Flapjack
