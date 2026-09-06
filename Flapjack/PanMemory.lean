import Flapjack.PanValues

/-!
Flat source memory semantics.

CakeML's Pancake evaluator does not store a record as one memory cell.  It
flattens `RStruct` and `NStruct` values into consecutive words and reconstructs
them from a shape when loading.  This module ports that part of `panSem`: the
memory domain is explicit, failed reads and writes return `none`, and offsets
are measured in `bytesInWord` units.
-/

namespace Flapjack

abbrev PanFlatMemory (α : Type u) := α → Option α
abbrev PanMemoryDomain (α : Type u) := α → Bool

def panOffset [Add α] (bytesInWord address : α) : Nat → α
  | 0 => address
  | count + 1 => panOffset bytesInWord address count + bytesInWord

def panShapeFuel : Shape → Nat
  | .one => 1
  | .comb shapes => 1 + panShapeListFuel shapes
  | .named _ => 1
where
  panShapeListFuel : List Shape → Nat
    | [] => 0
    | shape :: shapes => panShapeFuel shape + panShapeListFuel shapes

def panShapeFieldsFuel : List (FieldName × Shape) → Nat
  | [] => 0
  | (_, shape) :: fields => 1 + panShapeFuel shape + panShapeFieldsFuel fields

def panStructContextFuel : StructContext → Nat
  | [] => 0
  | (_, info) :: context => panShapeFieldsFuel info.fields + panStructContextFuel context

def panValueFuel : PanValue α → Nat
  | .word _ => 1
  | .rStruct fields => 1 + panValueListFuel fields
  | .nStruct _ fields => 1 + panValueFieldListFuel fields
where
  panValueListFuel : List (PanValue α) → Nat
    | [] => 0
    | value :: values => panValueFuel value + panValueListFuel values

  panValueFieldListFuel : List (FieldName × PanValue α) → Nat
    | [] => 0
    | (_, value) :: fields => panValueFuel value + panValueFieldListFuel fields

def panValueWordsFuel : Nat → PanValue α → List α
  | 0, _ => []
  | fuel + 1, .word value => [value]
  | fuel + 1, .rStruct fields => panValueWordsListFuel fuel fields
  | fuel + 1, .nStruct _ fields => panValueWordsFieldListFuel fuel fields
where
  panValueWordsListFuel : Nat → List (PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, value :: values =>
        panValueWordsFuel fuel value ++ panValueWordsListFuel fuel values

  panValueWordsFieldListFuel : Nat → List (FieldName × PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, (_, value) :: fields =>
        panValueWordsFuel fuel value ++ panValueWordsFieldListFuel fuel fields

def panValueWords (value : PanValue α) : List α :=
  panValueWordsFuel (panValueFuel value + 1) value

def panFlatReadWord [BEq α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (address : α) : Option (PanValue α) :=
  if domain address then (memory address).map .word else none

def panFlatLoadFuel [BEq α] [OfNat α 0] [Add α]
    (context : StructContext) (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord : α) : Nat → Shape → α →
      Option (PanValue α)
  | 0, _, _ => none
  | fuel + 1, .one, address => panFlatReadWord domain memory address
  | fuel + 1, .comb shapes, address =>
      (panFlatLoadListFuel context domain memory bytesInWord fuel shapes address).map
        PanValue.rStruct
  | fuel + 1, .named name, address => do
      let info ← lookupInfo name context
      let fields ← panFlatLoadFieldsFuel context domain memory bytesInWord fuel
        info.fields address
      pure (.nStruct name fields)
termination_by fuel shape address => fuel
where
  panFlatLoadListFuel [BEq α] [OfNat α 0] [Add α]
      (context : StructContext) (domain : PanMemoryDomain α)
      (memory : PanFlatMemory α) (bytesInWord : α) : Nat → List Shape → α →
        Option (List (PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, shape :: shapes, address => do
        let value ← panFlatLoadFuel context domain memory bytesInWord fuel shape address
        let values ← panFlatLoadListFuel context domain memory bytesInWord fuel shapes
          (panOffset bytesInWord address (shapeSizeWithContext context shape))
        pure (value :: values)
    termination_by fuel shapes address => fuel

  panFlatLoadFieldsFuel [BEq α] [OfNat α 0] [Add α]
      (context : StructContext) (domain : PanMemoryDomain α)
      (memory : PanFlatMemory α) (bytesInWord : α) : Nat →
        List (FieldName × Shape) → α →
        Option (List (FieldName × PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, (field, shape) :: fields, address => do
        let value ← panFlatLoadFuel context domain memory bytesInWord fuel shape address
        let values ← panFlatLoadFieldsFuel context domain memory bytesInWord fuel fields
          (panOffset bytesInWord address (shapeSizeWithContext context shape))
        pure ((field, value) :: values)
    termination_by fuel fields address => fuel

def panFlatLoad [BEq α] [OfNat α 0] [Add α]
    (context : StructContext) (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α) (shape : Shape) :
    Option (PanValue α) :=
  if isWfShape context shape then
    panFlatLoadFuel context domain memory bytesInWord
      (panStructContextFuel context + panShapeFuel shape + 1) shape address
  else none

def panFlatStoreWord [BEq α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (address value : α) : Option (PanFlatMemory α) :=
  if domain address then
    some (updatePanValueMap memory address value)
  else none

def panFlatStoreWords [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord : α) : α → List α →
      Option (PanFlatMemory α)
  | address, [] => some memory
  | address, value :: values => do
      let memory ← panFlatStoreWord domain memory address value
      panFlatStoreWords domain memory bytesInWord
        (panOffset bytesInWord address 1) values

def panFlatStore [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α)
    (value : PanValue α) : Option (PanFlatMemory α) :=
  panFlatStoreWords domain memory bytesInWord address (panValueWords value)

def evalPanFlatExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α) : Exp α → Option (PanValue α)
  | .const value => some (.word value)
  | .var .local name => locals name
  | .var .global name => globals name
  | .rStruct fields =>
      (evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord fields).map .rStruct
  | .rField index expression => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let values ← evalPanFlatFields structs locals globals domain memory
        baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      panFlatLoad structs domain memory bytesInWord address shape
  | .load32 address | .loadByte address => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      panFlatReadWord domain memory address
  | .op operator arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right => some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanFlatExp structs locals globals domain memory
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
  evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      List (Exp α) → Option (List (PanValue α))
    | [] => some []
    | expression :: expressions => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values)
    termination_by expressions => sizeOf expressions

  evalPanFlatFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α))
    | [] => some []
    | (name, expression) :: fields => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanFlatFields structs locals globals domain memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values)
    termination_by fields => sizeOf fields

def evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) : Option (List (PanValue α)) :=
  evalPanFlatExp.evalPanFlatExps structs locals globals domain memory
    baseAddress topAddress bytesInWord expressions

def evalPanFlatProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (primitive : PanPrimitiveHandler α) :
    Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (PanFlatMemory α) × List (PanValue α))
  | .skip => some (locals, globals, memory, [])
  | .dec name shape value body => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals domain memory primitive body
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .primitive name operator arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let memory ← panFlatStore domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .seq first second => do
      let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals domain memory primitive first
      if result.2.2.2.isEmpty then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 domain result.2.2.1 primitive second
      else pure result
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord condition
      let .word condition := condition | none
      if condition != 0 then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive thenBranch
      else
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive elseBranch
  | .return value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, globals, memory, [value])
  | .tick | .annot _ _ => some (locals, globals, memory, [])
  | _ => none
termination_by program => sizeOf program

def evalPanFlatProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) : Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × PanFlatMemory α × List (PanValue α)) :=
  evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals domain memory (fun _ _ => none)

inductive PanFlatControlResult (α : Type u) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)

abbrev PanFlatFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
      Option (VarName → Option (PanValue α))

def restorePanFlatControlLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanFlatControlResult α → PanFlatControlResult α
  | .normal locals globals memory =>
      .normal (restorePanValueLocal locals name oldValue) globals memory
  | .returned locals globals memory values =>
      .returned (restorePanValueLocal locals name oldValue) globals memory values
  | .raised locals globals memory exception value =>
      .raised (restorePanValueLocal locals name oldValue) globals memory exception value
  | .broke locals globals memory =>
      .broke (restorePanValueLocal locals name oldValue) globals memory
  | .continued locals globals memory =>
      .continued (restorePanValueLocal locals name oldValue) globals memory

mutual
  def evalPanFlatCallWithPrimitiveAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
      (baseAddress topAddress bytesInWord : α)
      (domain : PanMemoryDomain α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → PanFlatMemory α →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        Option (PanFlatControlResult α)
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments => do
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel calleeLocals globals memory body
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
                  evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                    baseAddress topAddress bytesInWord domain fuel
                    (updatePanValueMap locals handlerVariable value)
                    calleeGlobals calleeMemory handlerProgram
                else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
            | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
        | .broke _ calleeGlobals calleeMemory =>
            pure (.broke (fun _ => none) calleeGlobals calleeMemory)
        | .continued _ calleeGlobals calleeMemory =>
            pure (.continued (fun _ => none) calleeGlobals calleeMemory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanFlatProgFuelWithPrimitiveAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
      (baseAddress topAddress bytesInWord : α)
      (domain : PanMemoryDomain α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → PanFlatMemory α → Prog α →
        Option (PanFlatControlResult α)
    | 0, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, .skip =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .dec name shape value body => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel
            (updatePanValueMap locals name value) globals memory body
          pure (restorePanFlatControlLocal name oldValue result)
        else none
    | fuel + 1, locals, globals, memory, .assign .local name value => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | fuel + 1, locals, globals, memory, .assign .global name value => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | fuel + 1, locals, globals, memory, .primitive name operator arguments => do
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | fuel + 1, locals, globals, memory, .store address value => do
        let address ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let memory ← panFlatStore domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .seq first second => do
        let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory first
        match result with
        | .normal locals globals memory =>
            evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
              baseAddress topAddress bytesInWord domain fuel locals globals memory second
        | result => pure result
    | fuel + 1, locals, globals, memory, .ite condition thenBranch elseBranch => do
        let condition ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        if condition != 0 then
          evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory thenBranch
        else
          evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory elseBranch
    | fuel + 1, locals, globals, memory, .call info function arguments =>
        evalPanFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory info function arguments
    | fuel + 1, locals, globals, memory, .decCall name shape function arguments body => do
        let oldValue := locals name
        let result ← evalPanFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory
          (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals globals memory =>
            if let some value := locals name then
              if panShapeMatches (panValueShape structs value) shape then
                let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                  baseAddress topAddress bytesInWord domain fuel locals globals memory body
                pure (restorePanFlatControlLocal name oldValue result)
              else none
            else none
        | result => pure result
    | fuel + 1, locals, globals, memory, .extCall function configuration configurationLength array arrayLength => do
        let configuration ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configuration
        let configurationLength ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configurationLength
        let array ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord array
        let arrayLength ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord arrayLength
        let .word configuration := configuration | none
        let .word configurationLength := configurationLength | none
        let .word array := array | none
        let .word arrayLength := arrayLength | none
        let locals ← ffi function configuration configurationLength array arrayLength locals
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while condition body => do
        let evaluatedCondition ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word conditionValue := evaluatedCondition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory body
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                baseAddress topAddress bytesInWord domain fuel locals globals memory
                (.while condition body)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | fuel + 1, locals, globals, memory, .break =>
        pure (.broke locals globals memory)
    | fuel + 1, locals, globals, memory, .continue =>
        pure (.continued locals globals memory)
    | fuel + 1, locals, globals, memory, .raise exception value => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.raised locals globals memory exception value)
    | fuel + 1, locals, globals, memory, .return value => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        pure (.returned locals globals memory [value])
    | fuel + 1, locals, globals, memory, .tick | fuel + 1, locals, globals, memory, .annot _ _ =>
        pure (.normal locals globals memory)
    | _, _, _, _, _ => none
    termination_by fuel _ _ _ _ => fuel
end

def evalPanFlatProgWithPrimitiveAndFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) (program : Prog α) :
    Option (PanFlatControlResult α) :=
  evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
    baseAddress topAddress bytesInWord domain fuel locals globals memory program

def evalPanFlatProgWithCallsAndFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (ffi : PanFlatFfiHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) (program : Prog α) :
    Option (PanFlatControlResult α) :=
  evalPanFlatProgWithPrimitiveAndFfi structs functions ffi (fun _ _ => none)
    baseAddress topAddress bytesInWord fuel locals globals domain memory program

end Flapjack
