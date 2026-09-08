import Flapjack.PanProgramSemantics

/-!
Step-counted structured Pancake semantics.

The fuel argument of the existing evaluator in `PanValues` is a recursion
guard. It is deliberately not a cost: sequence evaluation restarts the guard
for its second component and loop evaluation restarts it for the next
iteration. This module keeps that evaluator intact and adds a parallel
evaluator whose successful result carries a compositional source-step count.

The count is the number of source evaluation rules visited. Every expression
node costs one step plus the costs of its recursively evaluated operands; list
traversal itself is free. Every statement/control constructor costs one step,
while a call contributes one step for the call plus argument, callee, and any
resumed handler/continuation steps. `fuel` remains only the bound needed to
make the recursive definition executable.
-/

namespace Flapjack

abbrev PanValueSteppedResult (α : Type u) :=
  PanValueControlResult α × Nat

private def evalPanValueExpSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) : Exp α →
    Option (PanValue α × Nat)
  | .const value => some (.word value, 1)
  | .var .local name => (locals name).map (fun value => (value, 1))
  | .var .global name => (globals name).map (fun value => (value, 1))
  | .rStruct fields => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord fields
      pure (.rStruct values, steps + 1)
  | .rField index expression => do
      let (value, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields =>
          let value ← fields[index]?
          pure (value, steps + 1)
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let (values, steps) ← evalPanValueExpSteps.evalFields structs locals globals
        memory baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values, steps + 1)
      else none
  | .nField name expression => do
      let (value, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            let value ← lookupPanValueField name fields
            pure (value, steps + 1)
          else none
      | _ => none
  | .load shape address => do
      let (address, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      if isWfShape structs shape && panShapeMatches (panValueShape structs value) shape then
        pure (value, steps + 1)
      else none
  | .load32 address | .loadByte address => do
      let (address, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match value with
      | .word value => pure (.word value, steps + 1)
      | _ => none
  | .op operator arguments => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] =>
          pure (.word (evalPanBinOp operator left right), steps + 1)
      | _ => none
  | .panOp .mul arguments => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => pure (.word (left * right), steps + 1)
      | _ => none
  | .cmp operator left right => do
      let (left, leftSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord left
      let (right, rightSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          pure (.word (evalPanCmp operator left right), leftSteps + rightSteps + 1)
      | _, _ => none
  | .shift operator left right => do
      let (left, leftSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord left
      let (right, rightSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          let value ← evalPanShift operator left right
          pure (.word value, leftSteps + rightSteps + 1)
      | _, _ => none
  | .baseAddr => some (.word baseAddress, 1)
  | .topAddr => some (.word topAddress, 1)
  | .bytesInWord => some (.word bytesInWord, 1)
termination_by expression => sizeOf expression
where
  evalExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) : List (Exp α) →
      Option (List (PanValue α) × Nat)
    | [] => some ([], 0)
    | expression :: expressions => do
        let (value, expressionSteps) ← evalPanValueExpSteps structs locals globals
          memory baseAddress topAddress bytesInWord expression
        let (values, restSteps) ← evalExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values, expressionSteps + restSteps)
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  evalFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α) × Nat)
    | [] => some ([], 0)
    | (name, expression) :: fields => do
        let (value, expressionSteps) ← evalPanValueExpSteps structs locals globals
          memory baseAddress topAddress bytesInWord expression
        let (values, restSteps) ← evalFields structs locals globals memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values, expressionSteps + restSteps)
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

private def evalPanValueExpsSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) : Option (List (PanValue α) × Nat) :=
  evalPanValueExpSteps.evalExps structs locals globals memory
    baseAddress topAddress bytesInWord expressions

private def evalPanValueFieldsSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) :
    Option (List (FieldName × PanValue α) × Nat) :=
  evalPanValueExpSteps.evalFields structs locals globals memory
    baseAddress topAddress bytesInWord fields

def panValueExpStepCost : Exp α → Nat
  | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
  | .rStruct fields => panValueExpStepCost.panValueExpsStepCost fields + 1
  | .rField _ expression | .nField _ expression | .load32 expression |
      .loadByte expression => panValueExpStepCost expression + 1
  | .nStruct _ fields => panValueExpStepCost.panValueFieldsStepCost fields + 1
  | .load _ address => panValueExpStepCost address + 1
  | .op _ arguments | .panOp _ arguments =>
      panValueExpStepCost.panValueExpsStepCost arguments + 1
  | .cmp _ left right | .shift _ left right =>
      panValueExpStepCost left + panValueExpStepCost right + 1
termination_by expression => sizeOf expression
where
  panValueExpsStepCost : List (Exp α) → Nat
    | [] => 0
    | expression :: expressions =>
        panValueExpStepCost expression + panValueExpsStepCost expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  panValueFieldsStepCost : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, expression) :: fields =>
        panValueExpStepCost expression + panValueFieldsStepCost fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def panValueExpsStepCost (expressions : List (Exp α)) : Nat :=
  panValueExpStepCost.panValueExpsStepCost expressions

def panValueFieldsStepCost (fields : List (FieldName × Exp α)) : Nat :=
  panValueExpStepCost.panValueFieldsStepCost fields

def evalPanValueExpCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α) :
    Option (PanValue α × Nat) :=
  (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression).map
    (fun value => (value, panValueExpStepCost expression))

def evalPanValueExpsCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α)) :
    Option (List (PanValue α) × Nat) :=
  (evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord expressions).map
    (fun values => (values, panValueExpsStepCost expressions))

def evalPanValueFieldsCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) :
    Option (List (FieldName × PanValue α) × Nat) :=
  (evalPanValueExp.evalPanValueFields structs locals globals memory
      baseAddress topAddress bytesInWord fields).map
    (fun values => (values, panValueFieldsStepCost fields))

theorem evalPanValueExpCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α) :
    (evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      expression).map Prod.fst =
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression := by
  simp [evalPanValueExpCounted, Function.comp_def]

theorem evalPanValueExpsCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α)) :
    (evalPanValueExpsCounted structs locals globals memory baseAddress topAddress
      bytesInWord expressions).map (fun result => result.1) =
      evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord expressions := by
  simp [evalPanValueExpsCounted, Function.comp_def]

theorem evalPanValueFieldsCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) :
    (evalPanValueFieldsCounted structs locals globals memory baseAddress topAddress
      bytesInWord fields).map (fun result => result.1) =
      evalPanValueExp.evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields := by
  simp [evalPanValueFieldsCounted, Function.comp_def]

def PanTerminates (evaluate : Nat → Option α) : Prop :=
  ∃ fuel result, evaluate fuel = some result

def PanSteppedTerminates (evaluate : Nat → Option (α × Nat)) : Prop :=
  ∃ fuel result steps, evaluate fuel = some (result, steps)

def PanDiverges (evaluate : Nat → Option α) : Prop :=
  ¬ PanTerminates evaluate

def PanSteppedDiverges (evaluate : Nat → Option (α × Nat)) : Prop :=
  ¬ PanSteppedTerminates evaluate

theorem panSteppedTerminates_iff_of_projection_agrees
    (evaluate : Nat → Option α)
    (steppedEvaluate : Nat → Option (α × Nat))
    (hagree : ∀ fuel,
      (steppedEvaluate fuel).map Prod.fst = evaluate fuel) :
    PanSteppedTerminates steppedEvaluate ↔ PanTerminates evaluate := by
  constructor
  · rintro ⟨fuel, result, steps, hsteps⟩
    refine ⟨fuel, result, ?_⟩
    rw [← hagree fuel, hsteps]
    rfl
  · rintro ⟨fuel, result, horiginal⟩
    have hprojected : (steppedEvaluate fuel).map Prod.fst = some result := by
      rw [hagree fuel]
      exact horiginal
    cases hstepped : steppedEvaluate fuel with
    | none => simp [hstepped] at hprojected
    | some pair =>
        cases pair with
        | mk actual steps =>
            simp [hstepped] at hprojected
            cases hprojected
            exact ⟨fuel, result, steps, hstepped⟩

theorem panSteppedDiverges_iff_of_projection_agrees
    (evaluate : Nat → Option α)
    (steppedEvaluate : Nat → Option (α × Nat))
    (hagree : ∀ fuel,
      (steppedEvaluate fuel).map Prod.fst = evaluate fuel) :
    PanSteppedDiverges steppedEvaluate ↔ PanDiverges evaluate := by
  exact not_congr (panSteppedTerminates_iff_of_projection_agrees
    evaluate steppedEvaluate hagree)

mutual
  def evalPanValueCallWithPrimitiveCallsAndFfiSteps
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
        Option (PanValueSteppedResult α)
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments => do
        let (values, argumentSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let (result, steps) ← evalPanValueProgWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          calleeLocals globals memory body
        match result with
        | .normal _ _ _ => pure (.normal locals globals memory, argumentSteps + steps)
        | .returned _ _ _ values =>
            match info with
            | none => pure (.returned locals globals memory values, argumentSteps + steps)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals globals memory, argumentSteps + steps)
        | .raised _ _ _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  let (result, handlerSteps) ←
                    evalPanValueProgWithPrimitiveCallsAndFfiSteps
                      primitive handler structs functions baseAddress topAddress bytesInWord fuel
                      (updatePanValueMap locals handlerVariable value) globals memory
                      handlerProgram
                  pure (result, argumentSteps + steps + handlerSteps)
                else pure (.raised locals globals memory exception value, argumentSteps + steps)
            | _ => pure (.raised locals globals memory exception value, argumentSteps + steps)
        | .broke _ _ _ => pure (.broke locals globals memory, argumentSteps + steps)
        | .continued _ _ _ => pure (.continued locals globals memory, argumentSteps + steps)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfiSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α → Option (PanValueSteppedResult α)
    | 0, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip =>
        some (.normal locals globals memory, 1)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let (result, steps) ← evalPanValueProgWithPrimitiveCallsAndFfiSteps
            primitive handler structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
          pure (restorePanValueControlLocal name oldValue result, valueSteps + steps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal (updatePanValueMap locals name evaluatedValue) globals memory, valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .assign .global name value => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.normal locals (updatePanValueMap globals name evaluatedValue) memory, valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments => do
        let (values, valueSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory, valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .store address value => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        pure (.normal locals globals (updatePanValueMemory memory address value),
          addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .store32 address value => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)), addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .storeByte address value => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let .word value := value | none
        pure (.normal locals globals
          (updatePanValueMemory memory address (.word value)), addressSteps + valueSteps + 1)
    | fuel + 1, locals, globals, memory, .seq first second => do
        let (firstResult, firstSteps) ←
          evalPanValueProgWithPrimitiveCallsAndFfiSteps
            primitive handler structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory first
        match firstResult with
        | .normal locals globals memory =>
            let (secondResult, secondSteps) ←
              evalPanValueProgWithPrimitiveCallsAndFfiSteps
                primitive handler structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory second
            pure (secondResult, firstSteps + secondSteps + 1)
        | result => pure (result, firstSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        let (result, steps) ←
          if condition != 0 then
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord _fuel
              locals globals memory thenBranch
          else
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord _fuel
              locals globals memory elseBranch
        pure (result, conditionSteps + steps + 1)
    | fuel + 1, locals, globals, memory, .call info function arguments => do
        let (result, steps) ← evalPanValueCallWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory info function arguments
        pure (result, steps + 1)
    | fuel + 1, locals, globals, memory,
        .decCall name _ function arguments body => do
        let (callResult, callSteps) ← evalPanValueCallWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory (some (some (.local, name), none)) function arguments
        match callResult with
        | .normal locals globals memory =>
            let (bodyResult, bodySteps) ←
              evalPanValueProgWithPrimitiveCallsAndFfiSteps
                primitive handler structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory body
            pure (bodyResult, callSteps + bodySteps + 1)
        | result => pure (result, callSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength => do
        let (values, expressionSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength]
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] :=
          values | none
        let locals ← handler function configuration configurationLength array arrayLength locals
        pure (.normal locals globals memory, expressionSteps + 1)
    | fuel + 1, locals, globals, memory, .while conditionExp body => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory, conditionSteps + 1)
        else
          let (bodyResult, bodySteps) ←
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory body
          match bodyResult with
          | .normal locals globals memory | .continued locals globals memory =>
              let (loopResult, loopSteps) ←
                evalPanValueProgWithPrimitiveCallsAndFfiSteps
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory (.while conditionExp body)
              pure (loopResult, conditionSteps + bodySteps + loopSteps + 1)
          | .broke locals globals memory =>
              pure (.normal locals globals memory, conditionSteps + bodySteps + 1)
          | result => pure (result, conditionSteps + bodySteps + 1)
    | _fuel + 1, locals, globals, memory, .break =>
        pure (.broke locals globals memory, 1)
    | _fuel + 1, locals, globals, memory, .continue =>
        pure (.continued locals globals memory, 1)
    | _fuel + 1, locals, globals, memory, .raise exception value => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.raised locals globals memory exception evaluatedValue, valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .return value => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        pure (.returned locals globals memory [evaluatedValue], valueSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .shMemLoad _ kind name address => do
        let (evaluatedAddress, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address
        let .word evaluatedAddress := evaluatedAddress | none
        let value ← memory evaluatedAddress
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name value) globals memory,
            addressSteps + 1)
        | .global => pure (.normal locals (updatePanValueMap globals name value) memory,
            addressSteps + 1)
    | _fuel + 1, locals, globals, memory, .shMemStore _ address value => do
        let (evaluatedAddress, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value
        let .word evaluatedAddress := evaluatedAddress | none
        let .word evaluatedValue := evaluatedValue | none
        pure (.normal locals globals
          (updatePanValueMemory memory evaluatedAddress (.word evaluatedValue)),
          addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .tick | _fuel + 1, locals, globals, memory, .annot _ _ =>
        pure (.normal locals globals memory, 1)
    termination_by fuel _ _ _ _ => fuel
end

def evalPanValueSteppedProg
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α) :
    Option (PanValueSteppedResult α) :=
  evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory program

def evalPanValueSteppedProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    Option (PanValueSteppedResult α) := do
  let state ← evalPanValueDeclarations initial declarations
  let result ← evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive ffi state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory
    (.call none entry arguments)
  match lookupInfo entry state.returnShapes, result with
  | some shape, (.returned locals globals memory [value], steps) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory [value], steps)
      else none
  | some _, (.returned _ _ _ _, _) => none
  | _, (result, steps) => some (result, steps)

end Flapjack
