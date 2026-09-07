import Flapjack.PanMemory
import Flapjack.RiscV.Model

/-!
RISC-V byte-addressed operations for CakeML-style flat memory.

CakeML's Pancake memory stores one machine word per aligned cell, while
loadByte and load32 address individual bytes within that cell.  The
RISC-V backend uses little-endian memory, so this adapter makes that
representation explicit over PanFlatMemory (Word width).
-/

namespace Flapjack.RiscV

def panRiscVByteAlign [NeZero width]
    (bytesInWord address : Word width) : Word width :=
  let bytes := bytesInWord.toNat
  if bytes = 0 then address
  else BitVec.ofNat width ((address.toNat / bytes) * bytes)

def panRiscVByteIndex [NeZero width]
    (bytesInWord address : Word width) : Nat :=
  let bytes := bytesInWord.toNat
  if bytes = 0 then 0 else address.toNat % bytes

def panRiscVGetByte [NeZero width]
    (bytesInWord address value : Word width) : Word width :=
  let offset := 256 ^ panRiscVByteIndex bytesInWord address
  BitVec.ofNat width ((value.toNat / offset) % 256)

def panRiscVSetByte [NeZero width]
    (bytesInWord address byte value : Word width) : Word width :=
  let offset := 256 ^ panRiscVByteIndex bytesInWord address
  let block := offset * 256
  let low := value.toNat % offset
  let high := value.toNat / block
  BitVec.ofNat width
    (low + (byte.toNat % 256) * offset + high * block)

def panRiscVReadByte [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  let alignedAddress := panRiscVByteAlign bytesInWord address
  if domain alignedAddress then
    (memory alignedAddress).map
      (panRiscVGetByte bytesInWord address)
  else none

def panRiscVRead32 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  if aligned address 4 then do
    let byte0 ← panRiscVReadByte domain memory bytesInWord address
    let byte1 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 1)
    let byte2 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 2)
    let byte3 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 3)
    pure (BitVec.ofNat width
      (byte0.toNat + 256 * byte1.toNat +
        256 ^ 2 * byte2.toNat + 256 ^ 3 * byte3.toNat))
  else none

def panRiscVRead16 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  if aligned address 2 then do
    let byte0 ← panRiscVReadByte domain memory bytesInWord address
    let byte1 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 1)
    pure (BitVec.ofNat width (byte0.toNat + 256 * byte1.toNat))
  else none

def panRiscVStoreByte [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address byte : Word width) :
    Option (PanFlatMemory (Word width)) :=
  let alignedAddress := panRiscVByteAlign bytesInWord address
  if domain alignedAddress then do
    let value ← memory alignedAddress
    pure (updatePanValueMap memory alignedAddress
      (panRiscVSetByte bytesInWord address byte value))
  else none

def panRiscVStore32 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address value : Word width) :
    Option (PanFlatMemory (Word width)) :=
  if aligned address 4 then do
    let byte0 := BitVec.ofNat width (value.toNat % 256)
    let byte1 := BitVec.ofNat width (value.toNat / 256 % 256)
    let byte2 := BitVec.ofNat width (value.toNat / 256 ^ 2 % 256)
    let byte3 := BitVec.ofNat width (value.toNat / 256 ^ 3 % 256)
    let memory ← panRiscVStoreByte domain memory bytesInWord address byte0
    let memory ← panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 1) byte1
    let memory ← panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 2) byte2
    panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 3) byte3
  else none

def panRiscVStore16 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address value : Word width) :
    Option (PanFlatMemory (Word width)) :=
  if aligned address 2 then
    let byte0 := BitVec.ofNat width (value.toNat % 256)
    let byte1 := BitVec.ofNat width (value.toNat / 256 % 256)
    do
      let memory ← panRiscVStoreByte domain memory bytesInWord address byte0
      panRiscVStoreByte domain memory bytesInWord
        (byteAddress address 1) byte1
  else none

def panRiscVReadWord [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (address : Word width) : Option (Word width) :=
  if domain address then memory address else none

def panRiscVStoreWord [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (address value : Word width) : Option (PanFlatMemory (Word width)) :=
  if domain address then some (updatePanValueMap memory address value) else none

def panRiscVReadShared [NeZero width]
    (size : OpSize)
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  match size with
  | .op8 => panRiscVReadByte domain memory bytesInWord address
  | .opW => panRiscVReadWord domain memory address
  | .op32 => panRiscVRead32 domain memory bytesInWord address
  | .op16 => panRiscVRead16 domain memory bytesInWord address

def panRiscVStoreShared [NeZero width]
    (size : OpSize)
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address value : Word width) :
    Option (PanFlatMemory (Word width)) :=
  match size with
  | .op8 =>
      panRiscVStoreByte domain memory bytesInWord address value
  | .opW => panRiscVStoreWord domain memory address value
  | .op32 => panRiscVStore32 domain memory bytesInWord address value
  | .op16 => panRiscVStore16 domain memory bytesInWord address value

def evalPanRiscVFlatExp [NeZero width]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (baseAddress topAddress bytesInWord : Word width) :
    Exp (Word width) → Option (PanValue (Word width))
  | .const value => some (.word value)
  | .var .local name => locals name
  | .var .global name => globals name
  | .rStruct fields =>
      (evalPanRiscVFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord fields).map .rStruct
  | .rField index expression => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let values ← evalPanRiscVFlatFields structs locals globals domain memory
        baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      panFlatLoad structs domain memory bytesInWord address shape
  | .load32 address => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      (panRiscVRead32 domain memory bytesInWord address).map .word
  | .loadByte address => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      (panRiscVReadByte domain memory bytesInWord address).map .word
  | .op operator arguments => do
      let values ← evalPanRiscVFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] =>
          some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments => do
      let values ← evalPanRiscVFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right => do
      let left ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right => do
      let left ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          (evalPanShift operator left right).map .word
      | _, _ => none
  | .baseAddr => some (.word baseAddress)
  | .topAddr => some (.word topAddress)
  | .bytesInWord => some (.word bytesInWord)
termination_by expression => sizeOf expression
where
  evalPanRiscVFlatExps [NeZero width]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue (Word width)))
      (domain : PanMemoryDomain (Word width))
      (memory : PanFlatMemory (Word width))
      (baseAddress topAddress bytesInWord : Word width) :
      List (Exp (Word width)) → Option (List (PanValue (Word width)))
    | [] => some []
    | expression :: expressions => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanRiscVFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values)
    termination_by expressions => sizeOf expressions

  evalPanRiscVFlatFields [NeZero width]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue (Word width)))
      (domain : PanMemoryDomain (Word width))
      (memory : PanFlatMemory (Word width))
      (baseAddress topAddress bytesInWord : Word width) :
      List (FieldName × Exp (Word width)) →
        Option (List (FieldName × PanValue (Word width)))
    | [] => some []
    | (name, expression) :: fields => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanRiscVFlatFields structs locals globals domain memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values)
    termination_by fields => sizeOf fields

def evalPanRiscVFlatExps [NeZero width]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (baseAddress topAddress bytesInWord : Word width) :
    List (Exp (Word width)) → Option (List (PanValue (Word width)))
  | [] => some []
  | expression :: expressions => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      let values ← evalPanRiscVFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

def evalPanRiscVFlatProg [NeZero width]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : Word width)
    (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width)) :
    Prog (Word width) →
      Option ((VarName → Option (PanValue (Word width))) ×
        (VarName → Option (PanValue (Word width))) ×
        PanFlatMemory (Word width) × List (PanValue (Word width)))
  | .skip => some (locals, globals, memory, [])
  | .dec name shape value body => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals domain memory body
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .store address value => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let memory ← panFlatStore domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .store32 address value => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      let memory ← panRiscVStore32 domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .storeByte address value => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      let memory ← panRiscVStoreByte domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .shMemLoad size kind name address => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← panRiscVReadShared size domain memory bytesInWord address
      match kind with
      | .local => pure (updatePanValueMap locals name (.word value), globals, memory, [])
      | .global => pure (locals, updatePanValueMap globals name (.word value), memory, [])
  | .shMemStore size address value => do
      let address ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      let memory ← panRiscVStoreShared size domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .seq first second => do
      let result ← evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
        locals globals domain memory first
      if result.2.2.2.isEmpty then
        evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
          result.1 result.2.1 domain result.2.2.1 second
      else pure result
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord condition
      let .word condition := condition | none
      if condition != 0 then
        evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
          locals globals domain memory thenBranch
      else
        evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
          locals globals domain memory elseBranch
  | .return value => do
      let value ← evalPanRiscVFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, globals, memory, [value])
  | .tick | .annot _ _ => some (locals, globals, memory, [])
  | _ => none
termination_by program => sizeOf program

/-!
Fuel-bounded RISC-V source semantics.  The non-fuel evaluator above is useful
for small straight-line examples, but it cannot represent loops or recursive
calls.  This evaluator mirrors the generic flat evaluator while routing every
memory operation through the RISC-V byte-addressed adapter in this file.
-/
mutual
  def evalPanRiscVFlatCallWithPrimitiveAndFfi [NeZero width]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog (Word width)))
      (ffi : PanFlatFfiHandler (Word width))
      (primitive : PanPrimitiveHandler (Word width))
      (baseAddress topAddress bytesInWord : Word width)
      (domain : PanMemoryDomain (Word width)) :
      Nat → (VarName → Option (PanValue (Word width))) →
        (VarName → Option (PanValue (Word width))) →
        PanFlatMemory (Word width) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog (Word width))) → FunName →
        List (Exp (Word width)) → Option (PanFlatControlResult (Word width))
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments => do
        let values ← evalPanRiscVFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
          ffi primitive baseAddress topAddress bytesInWord domain fuel
          calleeLocals globals memory body
        match result with
        | .normal _ calleeGlobals calleeMemory =>
            pure (.normal locals calleeGlobals calleeMemory)
        | .returned _ calleeGlobals calleeMemory values =>
            match info with
            | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals calleeGlobals calleeMemory)
        | .raised _ calleeGlobals calleeMemory exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
                    ffi primitive baseAddress topAddress bytesInWord domain fuel
                    (updatePanValueMap locals handlerVariable value)
                    calleeGlobals calleeMemory handlerProgram
                else
                  pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
            | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
        | .broke _ calleeGlobals calleeMemory =>
            pure (.broke (fun _ => none) calleeGlobals calleeMemory)
        | .continued _ calleeGlobals calleeMemory =>
            pure (.continued (fun _ => none) calleeGlobals calleeMemory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanRiscVFlatProgFuelWithPrimitiveAndFfi [NeZero width]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog (Word width)))
      (ffi : PanFlatFfiHandler (Word width))
      (primitive : PanPrimitiveHandler (Word width))
      (baseAddress topAddress bytesInWord : Word width)
      (domain : PanMemoryDomain (Word width)) :
      Nat → (VarName → Option (PanValue (Word width))) →
        (VarName → Option (PanValue (Word width))) →
        PanFlatMemory (Word width) → Prog (Word width) →
        Option (PanFlatControlResult (Word width))
    | 0, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .dec name shape value body => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
            ffi primitive baseAddress topAddress bytesInWord domain fuel
            (updatePanValueMap locals name value) globals memory body
          pure (restorePanFlatControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | _fuel + 1, locals, globals, memory, .assign .global name value => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments => do
        let values ← evalPanRiscVFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value => do
        let address ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let memory ← panFlatStore domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value => do
        let address ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        let memory ← panRiscVStore32 domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value => do
        let address ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        let memory ← panRiscVStoreByte domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .seq first second => do
        let result ← evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
          ffi primitive baseAddress topAddress bytesInWord domain fuel
          locals globals memory first
        match result with
        | .normal locals globals memory =>
            evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
              baseAddress topAddress bytesInWord domain fuel locals globals memory second
        | result => pure result
    | fuel + 1, locals, globals, memory, .ite condition thenBranch elseBranch => do
        let condition ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        if condition != 0 then
          evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory thenBranch
        else
          evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory elseBranch
    | fuel + 1, locals, globals, memory, .call info function arguments =>
        evalPanRiscVFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory info function arguments
    | fuel + 1, locals, globals, memory, .decCall name shape function arguments body => do
        let oldValue := locals name
        let result ← evalPanRiscVFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory
          (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals globals memory =>
            if let some value := locals name then
              if panShapeMatches (panValueShape structs value) shape then
                let result ← evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
                  ffi primitive baseAddress topAddress bytesInWord domain fuel
                  locals globals memory body
                pure (restorePanFlatControlLocal name oldValue result)
              else none
            else none
        | result => pure result
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength => do
        let configuration ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configuration
        let configurationLength ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configurationLength
        let array ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord array
        let arrayLength ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord arrayLength
        let .word configuration := configuration | none
        let .word configurationLength := configurationLength | none
        let .word array := array | none
        let .word arrayLength := arrayLength | none
        let locals ← ffi function configuration configurationLength array arrayLength locals
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while condition body => do
        let evaluatedCondition ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word conditionValue := evaluatedCondition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions
            ffi primitive baseAddress topAddress bytesInWord domain fuel
            locals globals memory body
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                baseAddress topAddress bytesInWord domain fuel locals globals memory
                (.while condition body)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.raised locals globals memory exception value)
    | _fuel + 1, locals, globals, memory, .return value => do
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.returned locals globals memory [value])
    | _fuel + 1, locals, globals, memory, .shMemLoad size kind name address => do
        let address ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let .word address := address | none
        let value ← panRiscVReadShared size domain memory bytesInWord address
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name (.word value)) globals memory)
        | .global => pure (.normal locals (updatePanValueMap globals name (.word value)) memory)
    | _fuel + 1, locals, globals, memory, .shMemStore size address value => do
        let address ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanRiscVFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        let memory ← panRiscVStoreShared size domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .tick | _fuel + 1, locals, globals, memory, .annot _ _ =>
        pure (.normal locals globals memory)
    termination_by fuel _ _ _ _ => fuel
end

def evalPanRiscVFlatProgWithPrimitiveAndFfi [NeZero width]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog (Word width)))
    (ffi : PanFlatFfiHandler (Word width))
    (primitive : PanPrimitiveHandler (Word width))
    (baseAddress topAddress bytesInWord : Word width)
    (fuel : Nat) (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width)) (program : Prog (Word width)) :
    Option (PanFlatControlResult (Word width)) :=
  evalPanRiscVFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
    baseAddress topAddress bytesInWord domain fuel locals globals memory program

def evalPanRiscVFlatProgWithCallsAndFfi [NeZero width]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog (Word width)))
    (ffi : PanFlatFfiHandler (Word width))
    (baseAddress topAddress bytesInWord : Word width) (fuel : Nat)
    (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width)) (program : Prog (Word width)) :
    Option (PanFlatControlResult (Word width)) :=
  evalPanRiscVFlatProgWithPrimitiveAndFfi structs functions ffi (fun _ _ => none)
    baseAddress topAddress bytesInWord fuel locals globals domain memory program

def evalPanRiscVFlatResult [NeZero width]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : Word width)
    (locals globals : VarName → Option (PanValue (Word width)))
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width)) (program : Prog (Word width)) :
    Option (List (PanValue (Word width))) :=
  (evalPanRiscVFlatProg structs baseAddress topAddress bytesInWord
    locals globals domain memory program).map (fun result => result.2.2.2)

end Flapjack.RiscV
