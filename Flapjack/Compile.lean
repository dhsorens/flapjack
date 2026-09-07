import Flapjack.PanToCrep

/-!
Core statement lowering from Flapjack to Crepe.

This is the structured-local/control-flow portion of `pan_to_crep`. The
function is intentionally extraction-friendly: malformed shape lengths and
front-end constructs whose runtime environments are not ported yet lower to
`Skip`, matching the reference pass's defensive fallback style.
-/

namespace Flapjack

def compileArgs [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expressions : List (Exp α)) : List (CrepExp α) :=
  match expressions with
  | [] => []
  | expression :: expressions =>
      (compileExp context expression).1 ++ compileArgs context expressions
termination_by structural expressions

def allocatedNames (context : CompileContext α) (shape : Shape) : List Nat :=
  (List.range (Shape.shapeSize shape)).map (fun offset => context.maxVar + 1 + offset)

def freshNames (context : CompileContext α) (count start : Nat) : List Nat :=
  (List.range count).map (fun offset => context.maxVar + start + offset)

def functionReturnNames (context : CompileContext α) (function : FunName) : List Nat :=
  match lookupInfo function context.functions with
  | some (_, shape) => allocatedNames context shape
  | none => []

def loadMemOp : OpSize → CrepMemOp
  | .op8 => .load8
  | .opW => .load
  | .op32 => .load32
  | .op16 => .load16

def storeMemOp : OpSize → CrepMemOp
  | .op8 => .store8
  | .opW => .store
  | .op32 => .store32
  | .op16 => .store16

def firstCompiledExp [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExp context expression with
  | (compiled :: _, .one) => some compiled
  | _ => none

structure CompiledFunction (α : Type u) where
  name : FunName
  params : List Nat
  body : CrepProg α
  returnShape : Shape
  deriving Repr

def compileParamVars : List (VarName × Shape) → Nat →
    InfoMap (Shape × List Nat) × List Nat × Nat
  | [], offset => ([], [], offset)
  | (name, shape) :: params, offset =>
      let names := (List.range (Shape.shapeSize shape)).map (fun index => offset + index)
      let (restVars, restNames, nextOffset) := compileParamVars params
        (offset + Shape.shapeSize shape)
      ((name, (shape, names)) :: restVars, names ++ restNames, nextOffset)
termination_by params => sizeOf params

def functionInfos : List (Decl α) → InfoMap (List (VarName × Shape) × Shape)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, (declaration.params, declaration.returnShape)) ::
        functionInfos declarations
  | _ :: declarations => functionInfos declarations

def compileProg [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (program : Prog α) : CrepProg α :=
  match program with
  | .skip => .skip
  | .dec name shape value body =>
      let compiled := compileExp context value
      let names := allocatedNames context shape
      let nextContext := { context with
        vars := (name, (shape, names)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape }
      if names.length = compiled.1.length then
        nestedDecs names compiled.1 (compileProg nextContext body)
      else .skip
  | .assign .local name value =>
      match lookupInfo name context.vars, compileExp context value with
      | some (_, names), (expressions, _) =>
          if names.length = expressions.length then
            if distinctLists names (expressions.flatMap crepExpVars) then
              crepNestedSeq
                (names.zipWith (fun name expression => .assign name expression) expressions)
            else
              let temporaries := freshNames context names.length 1
              nestedDecs temporaries expressions
                (crepNestedSeq
                  (names.zipWith (fun name temporary => .assign name (.var temporary))
                    temporaries))
          else .skip
      | _, _ => .skip
  | .assign .global _ _ => .skip
  | .primitive name operator arguments =>
      match lookupInfo name context.vars with
      | some (_, names) =>
          let compiledArgs := compileArgs context arguments
          let temporaries := freshNames context compiledArgs.length 1
          nestedDecs temporaries compiledArgs (.primitive names operator temporaries)
      | none => .skip
  | .store address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (values, shape) =>
          let addressTemporary := context.maxVar + 1
          let temporaries := freshNames context values.length 2
          if values.length = Shape.shapeSize shape then
            nestedDecs (addressTemporary :: temporaries) (address :: values)
              (crepNestedSeq (stores (.var addressTemporary) (temporaries.map .var)
                0 context.bytesInWord))
          else .skip
      | _, _ => .skip
  | .store32 address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .store32 address value
      | _, _ => .skip
  | .storeByte address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .storeByte address value
      | _, _ => .skip
  | .seq first second => .seq (compileProg context first) (compileProg context second)
  | .ite condition thenBranch elseBranch =>
      match compileExp context condition with
      | (condition :: _, _) => .ite condition (compileProg context thenBranch)
          (compileProg context elseBranch)
      | _ => .skip
  | .while condition body =>
      match compileExp context condition with
      | (condition :: _, _) => .while condition (compileProg context body)
      | _ => .skip
  | .break => .break 0
  | .continue => .continue 0
  | .call info function arguments =>
      let args := compileArgs context arguments
      match info with
      | none => .call none function args
      | some (destination, handler) =>
          let returnNames :=
            match destination with
            | none => functionReturnNames context function
            | some (kind, name) =>
                match kind with
                | .local =>
                    match lookupInfo name context.vars with
                    | some (_, names) => names
                    | none => []
                | .global => []
          let compiledHandler :=
            match handler with
            | none => none
            | some (exception, handlerVar, handlerProgram) =>
                match lookupInfo exception context.exceptions with
                | none => none
                | some code =>
                    let handlerSetup :=
                      match lookupInfo handlerVar context.vars with
                      | some (_, names) => assignRet context.bytesInWord names
                      | none => .skip
                    some (code, .seq handlerSetup (compileProg context handlerProgram))
          .call (some (returnNames, compiledHandler)) function args
  | .decCall name shape function arguments body =>
      let names := allocatedNames context shape
      let nextContext := { context with
        vars := (name, (shape, names)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape }
      let call := .call (some (names, none)) function (compileArgs context arguments)
      nestedDecs names (names.map (fun _ => .const 0))
        (.seq call (compileProg nextContext body))
  | .extCall function configuration configurationLength array arrayLength =>
      match firstCompiledExp context configuration,
          firstCompiledExp context configurationLength,
          firstCompiledExp context array,
          firstCompiledExp context arrayLength with
      | some configuration, some configurationLength, some array, some arrayLength =>
          let configurationName := context.maxVar + 1
          let configurationLengthName := context.maxVar + 2
          let arrayName := context.maxVar + 3
          let arrayLengthName := context.maxVar + 4
          let names := [configurationName, configurationLengthName, arrayName, arrayLengthName]
          nestedDecs names [configuration, configurationLength, array, arrayLength]
            (.extCall function configurationName configurationLengthName arrayName arrayLengthName)
      | _, _, _, _ => .skip
  | .raise exception value =>
      match lookupInfo exception context.exceptions with
      | some code =>
          let compiled := compileExp context value
          let temporaries := freshNames context compiled.1.length 1
          if compiled.1.length = Shape.shapeSize compiled.2 then
            .seq
              (nestedDecs temporaries compiled.1
                (crepNestedSeq (storeGlobals 0 context.bytesInWord
                  (temporaries.map .var))))
              (.raise code)
          else .skip
      | none => .skip
  | .return value => .return (compileExp context value).1
  | .shMemLoad size .local name address =>
      match lookupInfo name context.vars, firstCompiledExp context address with
      | some (_, destination :: _), some address => .shMem (loadMemOp size) destination address
      | _, _ => .skip
  | .shMemLoad _ .global _ _ => .skip
  | .shMemStore size address value =>
      match firstCompiledExp context address, firstCompiledExp context value with
      | some address, some value =>
          let temporary := context.maxVar + 1
          nestedDecs [temporary] [value] (.shMem (storeMemOp size) temporary address)
      | _, _ => .skip
  | .tick => .tick
  | .annot _ _ => .skip

termination_by structural program

def compileFunDecl [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α) : CompiledFunction α :=
  let (vars, params, maxVar) := compileParamVars declaration.params 0
  let functionContext := { context with vars := vars, maxVar := maxVar }
  { name := declaration.name, params := params,
    body := compileProg functionContext declaration.body,
    returnShape := declaration.returnShape }

def compileFunctions [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : List (Decl α) → List (CompiledFunction α)
  | [] => []
  | .function declaration :: declarations =>
      compileFunDecl context declaration :: compileFunctions context declarations
  | _ :: declarations => compileFunctions context declarations
termination_by declarations => sizeOf declarations

def compileToCrepe [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    List (CompiledFunction α) :=
  let context := { context with functions := functionInfos declarations }
  compileFunctions context declarations

theorem compileProg_skip [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .skip = .skip := by
  simp [compileProg]

theorem compileProg_seq [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (first second : Prog α) :
    compileProg context (.seq first second) =
      .seq (compileProg context first) (compileProg context second) := by
  simp [compileProg]

theorem compileProg_return [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (value : Exp α) :
    compileProg context (.return value) = .return (compileExp context value).1 := by
  simp [compileProg]

theorem compileProg_extCall_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (configuration' configurationLength' array' arrayLength' : CrepExp α)
    (hconfiguration : firstCompiledExp context configuration = some configuration')
    (hconfigurationLength :
      firstCompiledExp context configurationLength = some configurationLength')
    (harray : firstCompiledExp context array = some array')
    (harrayLength : firstCompiledExp context arrayLength = some arrayLength') :
    compileProg context
        (.extCall function configuration configurationLength array arrayLength) =
      nestedDecs [context.maxVar + 1, context.maxVar + 2,
        context.maxVar + 3, context.maxVar + 4]
        [configuration', configurationLength', array', arrayLength']
        (.extCall function (context.maxVar + 1) (context.maxVar + 2)
          (context.maxVar + 3) (context.maxVar + 4)) := by
  simp [compileProg, hconfiguration, hconfigurationLength, harray, harrayLength,
    nestedDecs]

theorem compileProg_call_handler_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (returnShape : Shape)
    (exception handlerVar : VarName) (exceptionCode : α)
    (handlerProgram : Prog α) (handlerNames : List Nat)
    (compiledArguments : List (CrepExp α))
    (hfunction : lookupInfo function context.functions =
      some ([], returnShape))
    (hexception : lookupInfo exception context.exceptions = some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (none, some (exception, handlerVar, handlerProgram)))
          function arguments) =
      .call (some (allocatedNames context returnShape,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram))))
        function compiledArguments := by
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hfunction, hexception, hhandler, harguments,
    functionReturnNames, allocatedNames]

end Flapjack
