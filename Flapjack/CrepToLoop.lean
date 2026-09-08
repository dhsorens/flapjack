import Flapjack.Loop
import Flapjack.Static
import Flapjack.RiscV.Model

/-!
Initial Crepe-to-Loop lowering for the direct executable fragment. This keeps
the IR close to CakeML's `crep_to_loopScript.sml`; expression side effects,
condition materialization, liveness, and arithmetic expansion are subsequent
passes.
-/

namespace Flapjack

abbrev NatInfoMap (α : Type u) := List (Nat × α)

def lookupNatInfo (name : Nat) : NatInfoMap α → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if candidate == name then some value else lookupNatInfo name entries

structure LoopContext (α : Type u) where
  vars : NatInfoMap Nat
  functions : InfoMap (Nat × Nat)
  maxVar : Nat
  target : RiscV.Architecture
  deriving Repr

def findLoopVar (context : LoopContext α) (name : Nat) : Nat :=
  match lookupNatInfo name context.vars with
  | some value => value
  | none => 0

def lowerLoopExp : CrepExp α → LoopExp α
  | .const value => .const value
  | .var name => .var name
  | .load address => .load (lowerLoopExp address)
  | .load32 address => .load (lowerLoopExp address)
  | .loadByte address => .load (lowerLoopExp address)
  | .loadGlob address => .lookup address
  | .op operator arguments => .op operator (arguments.map lowerLoopExp)
  | .crepOp operator arguments => .crepOp operator (arguments.map lowerLoopExp)
  | .cmp operator left right => .cmp operator (lowerLoopExp left) (lowerLoopExp right)
  | .shift operator left right => .shift operator (lowerLoopExp left) (lowerLoopExp right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
termination_by expression => sizeOf expression

def lowerLoopProg : CrepProg α → LoopProg α
  | .skip => .skip
  | .dec name value body =>
      .seq (.assign name (lowerLoopExp value)) (lowerLoopProg body)
  | .assign name value => .assign name (lowerLoopExp value)
  | .primitive names operator arguments => .primitive names operator arguments
  | .store _ _ => .fail
  | .store32 _ _ => .fail
  | .storeByte _ _ => .fail
  | .storeGlob address value => .setGlobal address (lowerLoopExp value)
  | .seq first second => .seq (lowerLoopProg first) (lowerLoopProg second)
  | .break label => .break label
  | .continue label => .continue label
  | .raise _ => .fail
  | .return _ => .fail
  | .shMem operator name address => .shMem operator name (lowerLoopExp address)
  | .tick => .tick
  | .call _ _ _ => .fail
  | .extCall function configuration configurationLength array arrayLength =>
      .ffi function configuration configurationLength array arrayLength []
  | .ite _ _ _ => .fail
  | .while _ _ => .fail
termination_by program => sizeOf program

theorem lowerLoopProg_skip :
    lowerLoopProg (.skip : CrepProg α) = .skip := by
  simp [lowerLoopProg]

theorem lowerLoopProg_seq (first second : CrepProg α) :
    lowerLoopProg (.seq first second) =
      .seq (lowerLoopProg first) (lowerLoopProg second) := by
  simp [lowerLoopProg]

/-!
Unlike `lowerLoopExp`, this compiler carries the temporary and liveness
state used by the HOL pass. In particular, `Load32`, `LoadByte`, and
comparisons become explicit Loop statements rather than remaining effectful
expressions.
-/

structure LoopCompileExpResult (α : Type u) where
  code : List (LoopProg α)
  expression : LoopExp α
  nextTemp : Nat
  live : List Nat
  deriving Repr

structure LoopCompileExpsResult (α : Type u) where
  expressions : List (LoopExp α)
  code : List (LoopProg α)
  nextTemp : Nat
  live : List Nat
  deriving Repr

def loopCompileExp [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat) :
    CrepExp α → LoopCompileExpResult α
  | .const value => { code := [], expression := .const value, nextTemp := tmp, live := live }
  | .var name => { code := [], expression := .var name, nextTemp := tmp, live := live }
  | .load address =>
      let result := loopCompileExp context tmp live address
      { result with expression := .load result.expression }
  | .load32 address =>
      let result := loopCompileExp context tmp live address
      { code := result.code ++ [.assign tmp result.expression, .load32 tmp tmp],
        expression := .var tmp, nextTemp := tmp + 1, live := tmp :: result.live }
  | .loadByte address =>
      let result := loopCompileExp context tmp live address
      { code := result.code ++ [.assign tmp result.expression, .loadByte tmp tmp],
        expression := .var tmp, nextTemp := tmp + 1, live := tmp :: result.live }
  | .loadGlob address =>
      { code := [], expression := .lookup address, nextTemp := tmp, live := live }
  | .op operator arguments =>
      let result := loopCompileExps context tmp live arguments
      { code := result.code, expression := .op operator result.expressions,
        nextTemp := result.nextTemp, live := result.live }
  | .crepOp operator arguments =>
      let result := loopCompileExps context tmp live arguments
      match operator, result.expressions with
      | .mul, [left, right] =>
          let leftTemp := result.nextTemp
          let rightTemp := leftTemp + 1
          let destination := rightTemp + 1
          { code := result.code ++
              [.assign leftTemp left, .assign rightTemp right,
               .arith (.longMul destination destination leftTemp rightTemp)]
            expression := .var destination
            nextTemp := destination + 1
            live := destination :: leftTemp :: rightTemp :: result.live }
      | _, _ =>
          { code := result.code, expression := .crepOp operator result.expressions,
            nextTemp := result.nextTemp, live := result.live }
  | .cmp operator left right =>
      let leftResult := loopCompileExp context tmp live left
      let rightResult := loopCompileExp context leftResult.nextTemp leftResult.live right
      let leftTemp := rightResult.nextTemp
      let rightTemp := leftTemp + 1
      { code := leftResult.code ++ rightResult.code ++
          [.assign leftTemp leftResult.expression,
           .assign rightTemp rightResult.expression,
           .ite operator leftTemp (.reg rightTemp)
             (.assign leftTemp (.const (by exact 1)))
             (.assign leftTemp (.const (by exact 0)))
             [leftTemp, rightTemp]],
        expression := .var leftTemp, nextTemp := rightTemp + 1,
        live := leftTemp :: rightTemp :: rightResult.live }
  | .shift operator left right =>
      let leftResult := loopCompileExp context tmp live left
      let rightResult := loopCompileExp context leftResult.nextTemp leftResult.live right
      { code := leftResult.code ++ rightResult.code,
        expression := .shift operator leftResult.expression rightResult.expression,
        nextTemp := rightResult.nextTemp, live := rightResult.live }
  | .baseAddr => { code := [], expression := .baseAddr, nextTemp := tmp, live := live }
  | .topAddr => { code := [], expression := .topAddr, nextTemp := tmp, live := live }
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  loopCompileExps (context : LoopContext α) (tmp : Nat) (live : List Nat) :
      List (CrepExp α) → LoopCompileExpsResult α
    | [] => { expressions := [], code := [], nextTemp := tmp, live := live }
    | expression :: expressions =>
        let first := loopCompileExp context tmp live expression
        let rest := loopCompileExps context first.nextTemp first.live expressions
        { expressions := first.expression :: rest.expressions,
          code := first.code ++ rest.code, nextTemp := rest.nextTemp, live := rest.live }
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def loopCompileExps [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (expressions : List (CrepExp α)) :
    LoopCompileExpsResult α :=
  loopCompileExp.loopCompileExps context tmp live expressions

def loopTempNames (start count : Nat) : List Nat :=
  (List.range count).map (fun offset => start + offset)

def loopAssignTemps (names : List Nat) (expressions : List (LoopExp α)) :
    List (LoopProg α) :=
  names.zipWith (fun name expression => .assign name expression) expressions

def loopCompileProg [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) : CrepProg α → LoopProg α
  | .skip => .skip
  | .dec name value body =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      let nextContext := { context with
        vars := (name, result.nextTemp) :: context.vars
        maxVar := result.nextTemp }
      .seq (loopNestedSeq result.code)
        (.seq (.assign name result.expression)
          (loopCompileProg nextContext (result.nextTemp :: result.live) body))
  | .assign name value =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      .seq (loopNestedSeq result.code) (.assign name result.expression)
  | .primitive names operator arguments => .primitive names operator arguments
  | .store address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let valueTemp := valueResult.nextTemp
      .seq (loopNestedSeq (addressResult.code ++ valueResult.code))
        (.seq (.assign valueTemp valueResult.expression)
          (.store addressResult.expression valueTemp))
  | .store32 address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let addressTemp := valueResult.nextTemp
      let valueTemp := addressTemp + 1
      .seq (loopNestedSeq (addressResult.code ++ valueResult.code))
        (.seq (.assign addressTemp addressResult.expression)
          (.seq (.assign valueTemp valueResult.expression)
            (.store32 addressTemp valueTemp)))
  | .storeByte address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let addressTemp := valueResult.nextTemp
      let valueTemp := addressTemp + 1
      .seq (loopNestedSeq (addressResult.code ++ valueResult.code))
        (.seq (.assign addressTemp addressResult.expression)
          (.seq (.assign valueTemp valueResult.expression)
            (.storeByte addressTemp valueTemp)))
  | .storeGlob address value =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      .seq (loopNestedSeq result.code) (.setGlobal address result.expression)
  | .seq first second => .seq (loopCompileProg context live first)
      (loopCompileProg context live second)
  | .ite condition thenBranch elseBranch =>
      let result := loopCompileExp context (context.maxVar + 1) live condition
      .seq (loopNestedSeq result.code)
        (.seq (.assign result.nextTemp result.expression)
          (.ite .notEqual result.nextTemp (.imm (by exact 0))
            (loopCompileProg context result.live thenBranch)
            (loopCompileProg context result.live elseBranch) result.live))
  | .while condition body =>
      let result := loopCompileExp context (context.maxVar + 1) live condition
      .loop live
        (loopNestedSeq (result.code ++
          [.assign result.nextTemp result.expression,
           .ite .notEqual result.nextTemp (.imm (by exact 0))
             (.seq (loopCompileProg context result.live body) (.continue 0))
             (.break 0) result.live]))
        result.live
  | .break label => .break label
  | .continue label => .continue label
  | .call returnInfo function arguments =>
      let result := loopCompileExps context (context.maxVar + 1) live arguments
      let argumentNames := loopTempNames result.nextTemp result.expressions.length
      let target := match lookupInfo function context.functions with
        | some (label, _) => some label
        | none => some 0
      let call := match returnInfo with
        | none => .call none target argumentNames none
        | some (returns, none) =>
            .call (some (returns, result.live)) target argumentNames none
        | some (returns, some (exception, handler)) =>
            let exceptionName := result.nextTemp + result.expressions.length
            let handlerCode := loopCompileProg context result.live handler
            .call (some (returns, result.live)) target argumentNames
              (some (exceptionName,
                .ite .notEqual exceptionName (.imm exception)
                  (.raise exceptionName) (.seq .tick handlerCode) result.live,
                .skip, result.live))
      .seq (loopNestedSeq (result.code ++ loopAssignTemps argumentNames result.expressions)) call
  | .extCall function configuration configurationLength array arrayLength =>
      .ffi function configuration configurationLength array arrayLength live
  | .raise exception =>
      let exceptionName := context.maxVar + 1
      .seq (.assign exceptionName (.const exception)) (.raise exceptionName)
  | .return values =>
      let result := loopCompileExps context (context.maxVar + 1) live values
      let names := loopTempNames result.nextTemp result.expressions.length
      .seq (loopNestedSeq (result.code ++ loopAssignTemps names result.expressions)) (.return names)
  | .shMem operator name address =>
      let result := loopCompileExp context (context.maxVar + 1) live address
      .seq (loopNestedSeq result.code) (.shMem operator name result.expression)
  | .tick => .tick
termination_by program => sizeOf program

theorem loopCompileProg_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    loopCompileProg context live (.skip : CrepProg α) = .skip := by
  simp [loopCompileProg]

theorem loopCompileProg_seq [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (first second : CrepProg α) :
    loopCompileProg context live (.seq first second) =
      .seq (loopCompileProg context live first) (loopCompileProg context live second) := by
  simp [loopCompileProg]

theorem loopCompileExp_const [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (value : α) :
    loopCompileExp context tmp live (.const value) =
      { code := [], expression := .const value, nextTemp := tmp, live := live } := by
  simp [loopCompileExp]

theorem loopCompileExp_load32 [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (address : CrepExp α) :
    (loopCompileExp context tmp live (.load32 address)).nextTemp = tmp + 1 := by
  simp [loopCompileExp]

end Flapjack
