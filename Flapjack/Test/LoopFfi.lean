import Flapjack.LoopFfi

namespace Flapjack

def loopByteFfiTestState : LoopFfiState Nat Unit :=
  { locals := fun name =>
      match name with
      | 1 => some 10
      | 2 => some 1
      | 3 => some 20
      | 4 => some 2
      | 5 => some 7
      | _ => none
    globals := fun _ => none
    memory := fun address =>
      if address = 10 then some 42 else
      if address = 20 then some 9 else
      if address = 21 then some 8 else none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    byteAlign := id
    clock := 10
    bigEndian := false
    baseAddress := 0
    topAddress := 0
    ffi :=
      { oracle := fun _ state _ bytes => .returned state bytes
        state := ()
        ioEvents := [] }
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes => bytes.head?.getD 0 |>.toNat
    valueToNat := id }

example :
    (loopFfiReadBytes loopByteFfiTestState 10 1) = some [42] := by
  decide

example :
    match loopFfiSharedMem loopByteFfiTestState .load 5 10 with
    | (.normal state, _) => state.locals 5 = some 10
    | _ => False := by
  simp [loopFfiSharedMem, loopFfiSharedLoad, loopFfiIsLoad,
    loopFfiMemWidth, loopFfiSharedAddress, loopFfiSharedOperator,
    loopFfiByteCount, loopByteFfiTestState, callFfi, loopFfiUpdateLocal,
    loopFfiReadBytes]

example :
    match loopFfiSharedMem { loopByteFfiTestState with shMemaddrs := fun _ => false }
      .load 5 10 with
    | (.error _, _) => True
    | _ => False := by
  simp [loopFfiSharedMem, loopFfiSharedLoad, loopFfiIsLoad,
    loopFfiMemWidth, loopFfiSharedAddress, loopByteFfiTestState]

example :
    match loopFfiSharedMem loopByteFfiTestState .store8 5 10 with
    | (.normal state, _) => state.memory 10 = some 42
    | _ => False := by
  simp [loopFfiSharedMem, loopFfiSharedStore, loopFfiIsLoad,
    loopFfiMemWidth, loopFfiSharedAddress, loopFfiSharedOperator,
    loopFfiByteCount, loopByteFfiTestState, callFfi, loopFfiUpdateByte]

example :
    match loopFfiExtCall loopByteFfiTestState "echo" 10 1 20 2 with
    | (.normal state, _) => state.memory 20 = some 9
    | _ => False := by
  simp [loopFfiExtCall, loopByteFfiTestState, callFfi, loopFfiReadBytes,
    loopFfiWriteBytes, loopFfiUpdateByte]

def terminalLoopFfiState : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with
    ffi :=
      { loopByteFfiTestState.ffi with
        oracle := fun _ _ _ _ => .final .failed } }

example :
    match loopFfiExtCall terminalLoopFfiState "echo" 10 1 20 2 with
    | (.finalFfi _ event, _) =>
        event =
          { name := .extCall "echo", configuration := [42], bytes := [9, 8],
            outcome := .failed }
    | _ => False := by
  simp [loopFfiExtCall, terminalLoopFfiState, loopByteFfiTestState,
    loopFfiReadBytes, callFfi, loopFfiClearLocals]

example :
    match loopFfiProgramBoundary loopByteFfiTestState
      (.shMem .load8 5 (.var 1)) with
    | some ((.normal state, _)) => state.locals 5 = some 10
    | _ => False := by
  simp [loopFfiProgramBoundary, loopFfiEvalExp, loopFfiSharedMem,
    loopFfiSharedLoad, loopFfiIsLoad, loopFfiMemWidth,
    loopFfiSharedAddress, loopFfiSharedOperator, loopFfiByteCount,
    loopByteFfiTestState, callFfi, loopFfiUpdateLocal]

example :
    match loopFfiProgramBoundary loopByteFfiTestState
      (.ffi "echo" 1 2 3 4 [1, 2, 3, 4]) with
    | some ((.normal state, _)) => state.memory 20 = some 9
    | _ => False := by
  simp [loopFfiProgramBoundary, loopFfiCutState, loopFfiLocalsPresent,
    loopFfiExtCall, loopByteFfiTestState, callFfi, loopFfiReadBytes,
    loopFfiWriteBytes, loopFfiUpdateByte]

example :
    loopFfiProgramBoundary loopByteFfiTestState
      (.ffi "echo" 1 2 3 4 [1, 99]) = none := by
  simp [loopFfiProgramBoundary, loopFfiCutState, loopFfiLocalsPresent,
    loopByteFfiTestState]

end Flapjack
