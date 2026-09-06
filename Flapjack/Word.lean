import Flapjack.LoopAnalysis

/-!
The Word intermediate language used by CakeML's backend. This first port
keeps the register-level instruction set small but preserves the structure
needed by `loop_to_word`: words, register expressions, memory instructions,
calls, loops, and foreign calls.
-/

namespace Flapjack

inductive WordStore (α : Type u) where
  | temp (address : α)
  | nextFree
  | endOfHeap
  | triggerGC
  | currHeap
  | heapLength
  | progStart
  | bitmapBase
  | otherHeap
  | allocSize
  | globals
  | globReal
  | handler
  | genStart
  | codeBuffer
  | codeBufferEnd
  | bitmapBuffer
  | bitmapBufferEnd
  deriving Repr

inductive WordExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (store : WordStore α)
  | load (address : WordExp α)
  | op (operator : BinOp) (args : List (WordExp α))
  | shift (operator : Shift) (left right : WordExp α)
  deriving Repr

inductive WordRegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving Repr

inductive WordArith where
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | addCarry (destination resultCarry sourceLeft sourceRight carryIn : Nat)
  | div (destination dividend divisor : Nat)
  deriving DecidableEq, Repr

inductive WordMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

inductive WordInst where
  | arith (operation : WordArith)
  | mem (operator : WordMemOp) (destination address : Nat)
  deriving DecidableEq, Repr

inductive WordProg (α : Type u) where
  | skip
  | move (priority : Nat) (moves : List (Nat × Nat))
  | assign (name : Nat) (value : WordExp α)
  | inst (instruction : WordInst)
  | get (destination : Nat) (store : WordStore α)
  | store (address : WordExp α) (value : Nat)
  | set (store : WordStore α) (value : WordExp α)
  | seq (first second : WordProg α)
  | ite (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (thenBranch elseBranch : WordProg α)
  | loop (liveIn : List Nat) (body : WordProg α) (liveOut : List Nat)
  | mustTerminate (body : WordProg α)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (label : Nat) (values : List Nat)
  | tick
  | locValue (destination source : Nat)
  | call (returns : Option (List Nat × List Nat)) (target : Option Nat)
      (arguments : List Nat) (handler : Option (Nat × WordProg α))
  | alloc (destination : Nat) (cutsets : List Nat × List Nat)
  | storeConsts (source bitmap codeLength dataLength : Nat)
      (constants : List (Bool × α))
  | opCurrHeap (operator : BinOp) (destination source : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength : Nat)
      (cutsets : List Nat × List Nat)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : List Nat)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordExp α)
  deriving Repr

structure WordContext where
  vars : NatInfoMap Nat
  deriving Repr

def wordFindVar (context : WordContext) (name : Nat) : Nat :=
  match lookupNatInfo name context.vars with
  | some value => value
  | none => name

def wordMapVars (context : WordContext) : List Nat → List Nat
  | [] => []
  | name :: names => wordFindVar context name :: wordMapVars context names

def wordRegImm (context : WordContext) : RegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (wordFindVar context name)

def wordArith (context : WordContext) : LoopArith → WordArith
  | .longMul left right sourceLeft sourceRight =>
      .longMul (wordFindVar context left) (wordFindVar context right)
        (wordFindVar context sourceLeft) (wordFindVar context sourceRight)
  | .longDiv left right sourceLeft sourceRight quotient =>
      .longDiv (wordFindVar context left) (wordFindVar context right)
        (wordFindVar context sourceLeft) (wordFindVar context sourceRight)
        (wordFindVar context quotient)
  | .div destination dividend divisor =>
      .div (wordFindVar context destination) (wordFindVar context dividend)
        (wordFindVar context divisor)

def wordMemOp : CrepMemOp → Option WordMemOp
  | .load => some .load
  | .load8 => some .load8
  | .load16 => some .load16
  | .load32 => some .load32
  | .store => some .store
  | .store8 => some .store8
  | .store16 => some .store16
  | .store32 => some .store32

def loopToWordExp [OfNat α 1] : LoopExp α → Option (WordExp α)
  | .const value => some (.const value)
  | .var name => some (.var name)
  | .lookup address => some (.lookup (.temp address))
  | .load address => (loopToWordExp address).map .load
  | .op operator arguments =>
      (loopToWordExpList arguments).map (.op operator)
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .shift operator left right => do
      let left ← loopToWordExp left
      let right ← loopToWordExp right
      pure (.shift operator left right)
  | .baseAddr => some (.lookup .currHeap)
  | .topAddr => some (.op .add
      [.lookup .currHeap,
       .shift .lsl (.lookup .heapLength) (.const (by exact 1))])
termination_by expression => sizeOf expression
where
  loopToWordExpList [OfNat α 1] : List (LoopExp α) → Option (List (WordExp α))
    | [] => some []
    | expression :: expressions => do
        let expression ← loopToWordExp expression
        let expressions ← loopToWordExpList expressions
        pure (expression :: expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def loopToWordExpList [OfNat α 1] (expressions : List (LoopExp α)) :
    Option (List (WordExp α)) :=
  loopToWordExp.loopToWordExpList expressions

def wordCompileExp [OfNat α 1] (context : WordContext) :
    LoopExp α → Option (WordExp α)
  | .const value => some (.const value)
  | .var name => some (.var (wordFindVar context name))
  | .lookup address => some (.lookup (.temp address))
  | .load address => (wordCompileExp context address).map .load
  | .op operator arguments =>
      (wordCompileExpList context arguments).map (.op operator)
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .shift operator left right => do
      let left ← wordCompileExp context left
      let right ← wordCompileExp context right
      pure (.shift operator left right)
  | .baseAddr => some (.lookup .currHeap)
  | .topAddr => some (.op .add
      [.lookup .currHeap,
       .shift .lsl (.lookup .heapLength) (.const (by exact 1))])
termination_by expression => sizeOf expression
where
  wordCompileExpList [OfNat α 1] (context : WordContext) :
      List (LoopExp α) → Option (List (WordExp α))
    | [] => some []
    | expression :: expressions => do
        let expression ← wordCompileExp context expression
        let expressions ← wordCompileExpList context expressions
        pure (expression :: expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def wordCompileExpWithContext [OfNat α 1] (context : WordContext)
    (expression : LoopExp α) : Option (WordExp α) :=
  wordCompileExp context expression

def loopToWordProg [OfNat α 1] (context : WordContext) :
    LoopProg α → WordProg α
  | .skip => .skip
  | .assign name value =>
      match wordCompileExp context value with
      | some value => .assign (wordFindVar context name) value
      | none => .skip
  | .primitive [result, resultCarry] .addCarry [left, right, carryIn] =>
      /- Keep the carry input explicit at this boundary.  CakeML's
         loop_to_word pass lowers this to virtual scratch registers 1 and 3,
         but Flapjack has not yet ported the subsequent word allocator.  The
         RISC-V instruction selector can lower this five-register Word
         operation directly using its architectural x31 scratch, preserving
         the x1 link register for call-aware code. -/
      .inst (.arith (.addCarry (wordFindVar context result)
        (wordFindVar context resultCarry) (wordFindVar context left)
        (wordFindVar context right) (wordFindVar context carryIn)))
  | .primitive _ _ _ => .skip
  | .arith operation => .inst (.arith (wordArith context operation))
  | .store address value =>
      match wordCompileExp context address with
      | some address => .store address (wordFindVar context value)
      | none => .skip
  | .setGlobal address value =>
      match wordCompileExp context value with
      | some value => .set (.temp address) value
      | none => .skip
  | .load32 address destination =>
      .inst (.mem .load32 (wordFindVar context destination) (wordFindVar context address))
  | .loadByte address destination =>
      .inst (.mem .load8 (wordFindVar context destination) (wordFindVar context address))
  | .store32 address value =>
      .inst (.mem .store32 (wordFindVar context value) (wordFindVar context address))
  | .storeByte address value =>
      .inst (.mem .store8 (wordFindVar context value) (wordFindVar context address))
  | .seq first second => .seq (loopToWordProg context first) (loopToWordProg context second)
  | .ite operator condition right thenBranch elseBranch _ =>
      .seq (.ite operator (wordFindVar context condition) (wordRegImm context right)
        (loopToWordProg context thenBranch) (loopToWordProg context elseBranch)) .tick
  | .loop liveIn body liveOut =>
      .seq .tick (.seq (.loop (wordMapVars context liveIn)
        (loopToWordProg context body) (wordMapVars context liveOut)) .tick)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise (wordFindVar context exception)
  | .return values => .return 0 (wordMapVars context values)
  | .tick => .tick
  | .mark body => loopToWordProg context body
  | .fail => .skip
  | .locValue destination source =>
      .locValue (wordFindVar context destination) (wordFindVar context source)
  | .call returns target arguments none =>
      .call (returns.map (fun (values, live) =>
        (wordMapVars context values, wordMapVars context live))) target
        (wordMapVars context arguments)
        none
  | .call returns target arguments (some (exception, body, _, _)) =>
      .call (returns.map (fun (values, live) =>
        (wordMapVars context values, wordMapVars context live))) target
        (wordMapVars context arguments)
        (some (wordFindVar context exception, loopToWordProg context body))
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function (wordFindVar context configuration)
        (wordFindVar context configurationLength) (wordFindVar context array)
        (wordFindVar context arrayLength) (wordMapVars context live)
  | .shMem operator name address =>
      match wordMemOp operator, wordCompileExp context address with
      | some operator, some address =>
          .shareInst operator (wordFindVar context name) address
      | _, _ => .skip
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

theorem loopToWordProg_skip [OfNat α 1] (context : WordContext) :
    loopToWordProg context (.skip : LoopProg α) = .skip := by
  simp [loopToWordProg]

theorem loopToWordProg_seq [OfNat α 1] (context : WordContext)
    (first second : LoopProg α) :
    loopToWordProg context (.seq first second) =
      .seq (loopToWordProg context first) (loopToWordProg context second) := by
  simp [loopToWordProg]

end Flapjack
