import Flapjack.PanSimp
import Flapjack.Static

/-!
The named-structure elimination pass from CakeML's `pan_structs` theory.

Named structures are converted to raw `Comb` shapes and `RStruct` values. The
context records the structure declarations and the source-level local/global
shapes needed to resolve field projections. Malformed names deliberately use
the same defensive defaults as the HOL pass (`One`, index zero, or an empty
field list); the static checker is responsible for rejecting such programs.
-/

namespace Flapjack

structure StructPassContext where
  structs : StructContext
  locals : InfoMap Shape
  globals : InfoMap Shape
  deriving Repr

def structFindFieldIndex [BEq String] (field : FieldName) :
    List (FieldName × Shape) → Option Nat
  | [] => none
  | (candidate, _) :: fields =>
      if candidate == field then some 0
      else (structFindFieldIndex field fields).map (· + 1)

def structCompileShapeFuel : Nat → StructContext → Shape → Shape
  | 0, _, _ => .one
  | _fuel + 1, _context, .one => .one
  | fuel + 1, context, .comb shapes =>
      .comb (shapes.map (structCompileShapeFuel fuel context))
  | fuel + 1, context, .named name =>
      match lookupInfo name context with
      | some info =>
          .comb ((info.fields.map Prod.snd).map (structCompileShapeFuel fuel context))
      | none => .one

def structCompileShape (context : StructContext) (shape : Shape) : Shape :=
  structCompileShapeFuel (context.length + Shape.shapeSize shape + 1) context shape

def structOldExpShape (context : StructPassContext) : Exp α → Shape
  | .var kind name =>
      match kind with
      | .local => (lookupInfo name context.locals).getD .one
      | .global => (lookupInfo name context.globals).getD .one
  | .rStruct fields => .comb (structOldExpShapes context fields)
  | .rField index value =>
      match structOldExpShape context value with
      | .comb shapes => shapes.getD index .one
      | _ => .one
  | .nStruct name _ => .named name
  | .nField field value =>
      match structOldExpShape context value with
      | .named name =>
          match lookupInfo name context.structs with
          | some info =>
              match lookupInfo field info.fields with
              | some shape => shape
              | none => .one
          | none => .one
      | _ => .one
  | .load shape _ => shape
  | _ => .one
termination_by expression => sizeOf expression
where
  structOldExpShapes (context : StructPassContext) : List (Exp α) → List Shape
    | [] => []
    | expression :: expressions =>
        structOldExpShape context expression :: structOldExpShapes context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structSelectFields [BEq String] (fields : List (FieldName × Shape))
    (compiled : InfoMap (Exp α)) : List (Exp α) :=
  match fields with
  | [] => []
  | (field, _) :: fields =>
      match lookupInfo field compiled with
      | some expression => expression :: structSelectFields fields compiled
      | none => structSelectFields fields compiled

def structCompileExp [BEq String] (context : StructPassContext) :
    Exp α → Exp α
  | .rStruct fields => .rStruct (structCompileExps context fields)
  | .rField index value => .rField index (structCompileExp context value)
  | .nStruct name fields =>
      let compiledFields := structCompileFields context fields
      match lookupInfo name context.structs with
      | some info => .rStruct (structSelectFields info.fields compiledFields)
      | none => .rStruct []
  | .nField field value =>
      let compiledValue := structCompileExp context value
      let index :=
        match structOldExpShape context value with
        | .named name =>
            match lookupInfo name context.structs with
            | some info => (structFindFieldIndex field info.fields).getD 0
            | none => 0
        | _ => 0
      .rField index compiledValue
  | .load shape address =>
      .load (structCompileShape context.structs shape) (structCompileExp context address)
  | .load32 address => .load32 (structCompileExp context address)
  | .loadByte address => .loadByte (structCompileExp context address)
  | .op operator arguments => .op operator (structCompileExps context arguments)
  | .panOp operator arguments => .panOp operator (structCompileExps context arguments)
  | .cmp operator left right =>
      .cmp operator (structCompileExp context left) (structCompileExp context right)
  | .shift operator left right =>
      .shift operator (structCompileExp context left) (structCompileExp context right)
  | expression => expression
termination_by expression => sizeOf expression
where
  structCompileExps [BEq String] (context : StructPassContext) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        structCompileExp context expression :: structCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  structCompileFields [BEq String] (context : StructPassContext) :
      List (FieldName × Exp α) → InfoMap (Exp α)
    | [] => []
    | (field, expression) :: fields =>
        (field, structCompileExp context expression) :: structCompileFields context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structCompileProg [BEq String] (context : StructPassContext) :
    Prog α → Prog α
  | .dec name shape value body =>
      .dec name (structCompileShape context.structs shape)
        (structCompileExp context value)
        (structCompileProg { context with locals := (name, shape) :: context.locals } body)
  | .assign kind name value => .assign kind name (structCompileExp context value)
  | .primitive name operator arguments =>
      .primitive name operator (structCompileExps context arguments)
  | .store address value =>
      .store (structCompileExp context address) (structCompileExp context value)
  | .store32 address value =>
      .store32 (structCompileExp context address) (structCompileExp context value)
  | .storeByte address value =>
      .storeByte (structCompileExp context address) (structCompileExp context value)
  | .seq first second =>
      .seq (structCompileProg context first) (structCompileProg context second)
  | .ite condition thenBranch elseBranch =>
      .ite (structCompileExp context condition)
        (structCompileProg context thenBranch) (structCompileProg context elseBranch)
  | .while condition body =>
      .while (structCompileExp context condition) (structCompileProg context body)
  | .call info function arguments =>
      let compiledInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, structCompileProg context handler))
      .call compiledInfo function (structCompileExps context arguments)
  | .decCall name shape function arguments body =>
      .decCall name (structCompileShape context.structs shape) function
        (structCompileExps context arguments)
        (structCompileProg { context with locals := (name, shape) :: context.locals } body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (structCompileExp context configuration)
        (structCompileExp context configurationLength) (structCompileExp context array)
        (structCompileExp context arrayLength)
  | .raise exception value => .raise exception (structCompileExp context value)
  | .return value => .return (structCompileExp context value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind name (structCompileExp context address)
  | .shMemStore size address value =>
      .shMemStore size (structCompileExp context address) (structCompileExp context value)
  | program => program
termination_by program => sizeOf program
where
  structCompileExps [BEq String] (context : StructPassContext) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        structCompileExp context expression :: structCompileExps context expressions
termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structGetNames (context : StructPassContext) (declarations : List (Decl α)) :
    StructPassContext :=
  declarations.foldl (fun context declaration =>
    match declaration with
    | .name name fields =>
        { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
    | _ => context) context

def structCompileDecls [BEq String] :
    List (Decl α) → StructPassContext → List (Decl α) × StructPassContext
  | [], context => ([], context)
  | .decl shape name value :: declarations, context =>
      let nextContext := { context with globals := (name, shape) :: context.globals }
      let (compiled, finalContext) := structCompileDecls declarations nextContext
      (.decl (structCompileShape context.structs shape) name (structCompileExp context value) :: compiled,
        finalContext)
  | .function declaration :: declarations, context =>
      let (compiled, finalContext) := structCompileDecls declarations context
      let parameters := declaration.params.map
        (fun (name, shape) => (name, structCompileShape context.structs shape))
      let functionContext := { finalContext with locals := declaration.params }
      let compiledDeclaration := { declaration with
        params := parameters
        body := structCompileProg functionContext declaration.body
        returnShape := structCompileShape context.structs declaration.returnShape }
      (.function compiledDeclaration :: compiled, finalContext)
  | .exnDecl exception shape :: declarations, context =>
      let (compiled, finalContext) := structCompileDecls declarations context
      (.exnDecl exception (structCompileShape context.structs shape) :: compiled, finalContext)
  | .name _ _ :: declarations, context => structCompileDecls declarations context

def structCompileTop (declarations : List (Decl α)) : List (Decl α) :=
  let initial : StructPassContext :=
    { structs := [], locals := [], globals := [] }
  (structCompileDecls declarations (structGetNames initial declarations)).1

@[simp] theorem structCompileShape_one (context : StructContext) :
    structCompileShape context .one = .one := by
  simp [structCompileShape, structCompileShapeFuel]

@[simp] theorem structCompileExp_const [BEq String]
    (context : StructPassContext) (value : α) :
    structCompileExp context (.const value) = .const value := by
  simp [structCompileExp]

theorem structCompileProg_seq [BEq String] (context : StructPassContext)
    (first second : Prog α) :
    structCompileProg context (.seq first second) =
      .seq (structCompileProg context first) (structCompileProg context second) := by
  simp [structCompileProg]

end Flapjack
