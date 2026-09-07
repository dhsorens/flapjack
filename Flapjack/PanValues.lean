import Flapjack.Semantics

/-!
Structured source values and the corresponding executable expression/state
semantics.  The original scalar evaluator in `Semantics.lean` is useful for
the first compiler slices, but the Pancake source language distinguishes words
from records and named records.  This file preserves that distinction and
matches the value/shape checks in CakeML's `panSem` evaluator.
-/

namespace Flapjack

inductive PanValue (α : Type u) where
  | word (value : α)
  | rStruct (fields : List (PanValue α))
  | nStruct (name : StructName) (fields : List (FieldName × PanValue α))
  deriving Repr

def panValueShape (context : StructContext) : PanValue α → Shape
  | .word _ => .one
  | .rStruct fields => .comb (fields.map (panValueShape context))
  | .nStruct name _ => .named name
termination_by value => sizeOf value

def panShapeMatches : Shape → Shape → Bool
  | .one, .one => true
  | .named left, .named right => left == right
  | .comb left, .comb right => panShapeListMatches left right
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
where
  panShapeListMatches : List Shape → List Shape → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        panShapeMatches left right && panShapeListMatches leftRest rightRest
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right
    decreasing_by
      all_goals first | decreasing_trivial

def panValueFieldsHaveShapes (context : StructContext) :
    List (FieldName × Shape) → List (FieldName × PanValue α) → Bool
  | [], [] => true
  | (expectedName, expectedShape) :: expected,
      (actualName, actualValue) :: actual =>
      expectedName == actualName &&
        panShapeMatches (panValueShape context actualValue) expectedShape &&
        panValueFieldsHaveShapes context expected actual
  | _, _ => false

def lookupPanValueField (name : FieldName) :
    List (FieldName × PanValue α) → Option (PanValue α)
  | [] => none
  | (candidate, value) :: fields =>
      if candidate == name then some value else lookupPanValueField name fields

def evalPanValueExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) : Exp α → Option (PanValue α)
  | .const value => some (.word value)
  | .var .local name => locals name
  | .var .global name => globals name
  | .rStruct fields =>
      (evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord fields).map .rStruct
  | .rField index expression => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let values ← evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      if isWfShape structs shape && panShapeMatches (panValueShape structs value) shape then
        some value
      else none
  | .load32 address | .loadByte address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match value with
      | .word value => some (.word value)
      | _ => none
  | .op operator arguments => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] =>
          some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right => some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          (evalPanShift operator left right).map .word
      | _, _ => none
  | .baseAddr => some (.word baseAddress)
  | .topAddr => some (.word topAddress)
  | .bytesInWord => some (.word bytesInWord)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (Exp α) → Option (List (PanValue α))
    | [] => some []
    | expression :: expressions => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  evalPanValueFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α))
    | [] => some []
    | (name, expression) :: fields => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanValueFields structs locals globals memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values)
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) : Option (List (PanValue α)) :=
  evalPanValueExp.evalPanValueExps structs locals globals memory
    baseAddress topAddress bytesInWord expressions

def updatePanValueMap [BEq γ] (values : γ → Option α)
    (name : γ) (value : α) : γ → Option α :=
  fun current => if current == name then some value else values current

def updatePanValueMemory [BEq α] (memory : α → Option (PanValue α))
    (address : α) (value : PanValue α) : α → Option (PanValue α) :=
  updatePanValueMap memory address value

abbrev PanPrimitiveHandler (α : Type u) :=
  PrimOp → List (PanValue α) → Option (PanValue α)

def restorePanValueLocal [BEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) : VarName → Option (PanValue α) :=
  fun current => if current == name then oldValue else locals current

def evalPanValueProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α) :
    Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α))
  | .skip => some (locals, globals, memory, [])
  | .dec name shape value body => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals memory primitive body
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .primitive name operator arguments => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      pure (locals, globals, updatePanValueMemory memory address value, [])
  | .store32 address value | .storeByte address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      pure (locals, globals, updatePanValueMemory memory address (.word value), [])
  | .return value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (locals, globals, memory, [value])
  | .seq first second => do
      let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive first
      if result.2.2.2.isEmpty then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 result.2.2.1 primitive second
      else pure result
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord condition
      let .word condition := condition | none
      if condition != 0 then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive thenBranch
      else
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive elseBranch
  | .shMemLoad _ kind name address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match kind with
      | .local => pure (updatePanValueMap locals name value, globals, memory, [])
      | .global => pure (locals, updatePanValueMap globals name value, memory, [])
  | .shMemStore _ address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      pure (locals, globals, updatePanValueMemory memory address (.word value), [])
  | .tick | .annot _ _ => some (locals, globals, memory, [])
  | _ => none
termination_by program => sizeOf program

def evalPanValueProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals memory (fun _ _ => none)

inductive PanValueControlResult (α : Type u) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))

def restorePanValueControlLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueControlResult α → PanValueControlResult α
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

def bindPanValueParameters (parameters : List VarName)
    (values : List (PanValue α)) :
    Option (VarName → Option (PanValue α)) :=
  if parameters.length != values.length then none
  else
    some ((parameters.zip values).foldl
      (fun locals (name, value) => updatePanValueMap locals name value)
      (fun _ => none))

def assignPanValueCallResult
    (locals : VarName → Option (PanValue α))
    (destination : Option (VarKind × VarName))
    (values : List (PanValue α)) :
    Option (VarName → Option (PanValue α)) :=
  match destination, values with
  | none, [] => some locals
  | some (.local, name), [value] => some (updatePanValueMap locals name value)
  | _, _ => none

abbrev PanValueFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
      Option (VarName → Option (PanValue α))

def evalPanValueExtCall [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext) (handler : PanValueFfiHandler α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × (α → Option (PanValue α))) := do
  let configuration ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configuration
  let configurationLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configurationLength
  let array ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord array
  let arrayLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord arrayLength
  let .word configuration := configuration | none
  let .word configurationLength := configurationLength | none
  let .word array := array | none
  let .word arrayLength := arrayLength | none
  let locals ← handler function configuration configurationLength array arrayLength locals
  pure (locals, globals, memory)

/-!
Fuel-bounded structured source semantics for calls, exceptions, and FFI.  This
is the structured-value counterpart of the scalar control-result evaluator in
`Semantics.lean`; unlike the earlier state evaluator, it keeps caller and
callee state separate and propagates matching exception handlers.
-/
mutual
  def evalPanValueCallWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanValueProgWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel calleeLocals globals memory body
        match result with
        | .normal _ _ _ => pure (.normal locals globals memory)
        | .returned _ _ _ values =>
            match info with
            | none => pure (.returned locals globals memory values)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals globals memory)
        | .raised _ _ _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanValueProgWithCallsAndFfi structs functions handler
                    baseAddress topAddress bytesInWord fuel
                    (updatePanValueMap locals handlerVariable value) globals memory
                    handlerProgram
                else pure (.raised locals globals memory exception value)
            | _ => pure (.raised locals globals memory exception value)
        | .broke _ _ _ => pure (.broke locals globals memory)
        | .continued _ _ _ => pure (.continued locals globals memory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α → Option (PanValueControlResult α)
    | 0, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | _fuel + 1, locals, globals, memory, .assign .global name value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .store address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        pure (.normal locals globals (updatePanValueMemory memory address value))
    | _fuel + 1, locals, globals, memory, .store32 address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | _fuel + 1, locals, globals, memory, .storeByte address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | fuel + 1, locals, globals, memory, .seq first second => do
        let result ← evalPanValueProgWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory first
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithCallsAndFfi structs functions handler
              baseAddress topAddress bytesInWord fuel locals globals memory second
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory thenBranch
        else
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory elseBranch
    | fuel + 1, locals, globals, memory, .call info function arguments =>
        evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory info function arguments
    | fuel + 1, locals, globals, memory,
        .decCall name _ function arguments body => do
        let result ← evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory
          (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithCallsAndFfi structs functions handler
              baseAddress topAddress bytesInWord fuel locals globals memory body
        | result => pure result
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength => do
        let (locals, globals, memory) ← evalPanValueExtCall structs handler
          locals globals memory baseAddress topAddress bytesInWord function
          configuration configurationLength array arrayLength
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory body
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithCallsAndFfi structs functions handler
                baseAddress topAddress bytesInWord fuel locals globals memory
                (.while conditionExp body)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.raised locals globals memory exception value)
    | _fuel + 1, locals, globals, memory, .return value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.returned locals globals memory [value])
    | _fuel + 1, locals, globals, memory,
        .shMemLoad _ kind name address => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let .word address := address | none
        let value ← memory address
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
        | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .shMemStore _ address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | _fuel + 1, locals, globals, memory, .tick | _fuel + 1, locals, globals, memory, .annot _ _ =>
        pure (.normal locals globals memory)
    | _, _, _, _, _ => none
    termination_by fuel _ _ _ _ => fuel
end

/-!
The combined source evaluator with an explicit primitive environment.  The
ordinary combined evaluator above is useful for programs without primitive
instructions; this version is the one used when a compiler correctness
statement includes `Primitive`, because primitive calls may occur inside
declarations, loops, callees, or exception handlers.
-/
mutual
  def evalPanValueCallWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          calleeLocals globals memory body
        match result with
        | .normal _ _ _ => pure (.normal locals globals memory)
        | .returned _ _ _ values =>
            match info with
            | none => pure (.returned locals globals memory values)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals globals memory)
        | .raised _ _ _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                    structs functions baseAddress topAddress bytesInWord fuel
                    (updatePanValueMap locals handlerVariable value) globals memory
                    handlerProgram
                else pure (.raised locals globals memory exception value)
            | _ => pure (.raised locals globals memory exception value)
        | .broke _ _ _ => pure (.broke locals globals memory)
        | .continued _ _ _ => pure (.continued locals globals memory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α → Option (PanValueControlResult α)
    | 0, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | _fuel + 1, locals, globals, memory, .assign .global name value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        pure (.normal locals globals (updatePanValueMemory memory address value))
    | _fuel + 1, locals, globals, memory, .store32 address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | _fuel + 1, locals, globals, memory, .storeByte address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | fuel + 1, locals, globals, memory, .seq first second => do
        let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory first
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory second
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory thenBranch
        else
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory elseBranch
    | fuel + 1, locals, globals, memory, .call info function arguments =>
        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory info function arguments
    | fuel + 1, locals, globals, memory, .decCall name _ function arguments body => do
        let result ← evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory body
        | result => pure result
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength => do
        let (locals, globals, memory) ← evalPanValueExtCall structs handler
          locals globals memory baseAddress topAddress bytesInWord function
          configuration configurationLength array arrayLength
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory body
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory (.while conditionExp body)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.raised locals globals memory exception value)
    | _fuel + 1, locals, globals, memory, .return value => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.returned locals globals memory [value])
    | _fuel + 1, locals, globals, memory,
        .shMemLoad _ kind name address => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let .word address := address | none
        let value ← memory address
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
        | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .shMemStore _ address value => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)))
    | _fuel + 1, locals, globals, memory,
        .tick | _fuel + 1, locals, globals, memory, .annot _ _ =>
        pure (.normal locals globals memory)
    termination_by fuel _ _ _ _ => fuel
end

theorem evalPanValueExp_rField_word
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (left right : α) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      (.rField 1 (.rStruct [.const left, .const right])) = some (.word right) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]

end Flapjack
