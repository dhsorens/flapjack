import Flapjack.PanStructs

/-!
The core of Pancake's `pan_globals` pass.

Global values are laid out in the heap from `TopAddr`. This module keeps the
word representation abstract and receives the natural-number-to-word map in
the context, allowing the same executable pass to be instantiated with
`BitVec` for the RISC-V backend or with `Nat` in small tests.
-/

namespace Flapjack

structure GlobalPassContext (α : Type u) where
  globals : InfoMap (Shape × α)
  globalsSize : α
  maxGlobalsSize : α
  bytesInWord : α
  fromNat : Nat → α

structure GlobalCompiledProgram (α : Type u) where
  initializers : List (Prog α)
  declarations : List (Decl α)
  context : GlobalPassContext α

def globalAddress [Add α] [Mul α] (context : GlobalPassContext α) (shape : Shape) : α :=
  context.globalsSize + context.bytesInWord * context.fromNat (Shape.shapeSize shape)

def globalCompileExp [BEq String] (context : GlobalPassContext α) : Exp α → Exp α
  | .var .local name => .var .local name
  | .var .global name =>
      match lookupInfo name context.globals with
      | some (shape, address) =>
          .load shape (.op .sub [.topAddr, .const address])
      | none => .const (context.fromNat 0)
  | .rStruct expressions => .rStruct (globalCompileExps context expressions)
  | .rField index expression => .rField index (globalCompileExp context expression)
  | .nStruct _ _ => .const (context.fromNat 0)
  | .nField _ _ => .const (context.fromNat 0)
  | .load shape address => .load shape (globalCompileExp context address)
  | .load32 address => .load32 (globalCompileExp context address)
  | .loadByte address => .loadByte (globalCompileExp context address)
  | .op operator expressions => .op operator (globalCompileExps context expressions)
  | .panOp operator expressions => .panOp operator (globalCompileExps context expressions)
  | .cmp operator left right =>
      .cmp operator (globalCompileExp context left) (globalCompileExp context right)
  | .shift operator left right =>
      .shift operator (globalCompileExp context left) (globalCompileExp context right)
  | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
  | expression => expression
termination_by expression => sizeOf expression
where
  globalCompileExps [BEq String] (context : GlobalPassContext α) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        globalCompileExp context expression :: globalCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalCompileProg [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape (globalCompileExp context value)
        (globalCompileProg context body)
  | .assign .global name value =>
      match lookupInfo name context.globals with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value)
      | none => .skip
  | .assign .local name value =>
      .assign .local name (globalCompileExp context value)
  | .primitive name operator arguments =>
      .primitive name operator (globalCompileExps context arguments)
  | .store address value =>
      .store (globalCompileExp context address) (globalCompileExp context value)
  | .store32 address value =>
      .store32 (globalCompileExp context address) (globalCompileExp context value)
  | .storeByte address value =>
      .storeByte (globalCompileExp context address) (globalCompileExp context value)
  | .seq first second =>
      .seq (globalCompileProg context first) (globalCompileProg context second)
  | .ite condition thenBranch elseBranch =>
      .ite (globalCompileExp context condition)
        (globalCompileProg context thenBranch) (globalCompileProg context elseBranch)
  | .while condition body =>
      .while (globalCompileExp context condition) (globalCompileProg context body)
  | .call info function arguments =>
      let compiledInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, globalCompileProg context handler))
      .call compiledInfo function (globalCompileExps context arguments)
  | .decCall name shape function arguments body =>
      .decCall name shape function (globalCompileExps context arguments)
        (globalCompileProg context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (globalCompileExp context configuration)
        (globalCompileExp context configurationLength) (globalCompileExp context array)
        (globalCompileExp context arrayLength)
  | .raise exception value => .raise exception (globalCompileExp context value)
  | .return value => .return (globalCompileExp context value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind name (globalCompileExp context address)
  | .shMemStore size address value =>
      .shMemStore size (globalCompileExp context address) (globalCompileExp context value)
  | program => program
termination_by program => sizeOf program
where
  globalCompileExps [BEq String] (context : GlobalPassContext α) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        globalCompileExp context expression :: globalCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalCollect [Add α] [Mul α] (context : GlobalPassContext α) :
    List (Decl α) → GlobalPassContext α
  | [] => context
  | .decl shape name _ :: declarations =>
      let address := globalAddress context shape
      globalCollect { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } declarations
  | _ :: declarations => globalCollect context declarations

def globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := globalCompileProg context declaration.body } ::
        globalCompileDecls context declarations
  | .exnDecl exception shape :: declarations =>
      .exnDecl exception shape :: globalCompileDecls context declarations
  | _ :: declarations => globalCompileDecls context declarations

def globalCompileInitializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Prog α)
  | [] => []
  | .decl _shape name value :: declarations =>
      let initializer :=
        match lookupInfo name context.globals with
        | some (_, address) =>
            .store (.op .sub [.topAddr, .const address])
              (globalCompileExp context value)
        | none => .skip
      initializer :: globalCompileInitializers context declarations
  | _ :: declarations => globalCompileInitializers context declarations

def globalCompileTop [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α)) :
    GlobalCompiledProgram α :=
  let initial : GlobalPassContext α :=
    { globals := []
      globalsSize := fromNat 0
      maxGlobalsSize := fromNat 0
      bytesInWord := bytesInWord
      fromNat := fromNat }
  let collected := globalCollect initial declarations
  let context := { collected with maxGlobalsSize := collected.globalsSize }
  { initializers := globalCompileInitializers context declarations
    declarations := globalCompileDecls context declarations
    context := context }

@[simp] theorem globalCompileExp_local [BEq String]
    (context : GlobalPassContext α) (name : VarName) :
    globalCompileExp context (.var .local name) = .var .local name := by
  simp [globalCompileExp]

theorem globalCompileExp_global [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (name : VarName) (shape : Shape) (address : α)
    (lookup : lookupInfo name context.globals = some (shape, address)) :
    globalCompileExp context (.var .global name) =
      .load shape (.op .sub [.topAddr, .const address]) := by
  simp [globalCompileExp, lookup]

theorem globalCompileProg_seq [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (first second : Prog α) :
    globalCompileProg context (.seq first second) =
      .seq (globalCompileProg context first) (globalCompileProg context second) := by
  simp [globalCompileProg]

theorem globalCollect_decl [Add α] [Mul α]
    (context : GlobalPassContext α) (shape : Shape) (name : String)
    (value : Exp α) :
    (globalCollect context [.decl shape name value]).globalsSize =
      globalAddress context shape := by
  simp [globalCollect]

end Flapjack
