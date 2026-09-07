import Flapjack.Word

/-!
# StackLang

The StackLang layer is the first stack-based intermediate representation in
CakeML's backend. It is deliberately kept separate from the RISC-V model:
StackLang still has structured control flow and an explicit handler stack, while
the later stack-to-lab pass is responsible for flattening these operations.

This file ports the call, exception, and FFI carriers from
`cakeml/compiler/backend/stackLangScript.sml` and the corresponding boundary
equations from `word_to_stackScript.sml`. Register allocation and the complete
word-to-stack compiler remain subsequent stages.
-/

namespace Flapjack

inductive StackStore where
  | nextFree
  | endOfHeap
  | triggerGC
  | heapLength
  | progStart
  | bitmapBase
  | currHeap
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
  | temp (index : Nat)
  deriving DecidableEq, Repr

inductive StackCallTarget where
  | label (name : Nat)
  | register (name : Nat)
  deriving DecidableEq, Repr

inductive StackProg (α : Type u) where
  | skip
  | const (destination value : Nat)
  | inst (instruction : WordInst)
  | shMem (operator : WordMemOp) (source address : Nat)
  | get (destination : Nat) (store : StackStore)
  | set (store : StackStore) (source : Nat)
  | arith (operator : BinOp) (destination left right : Nat)
  | shift (operator : Shift) (destination left right : Nat)
  | opCurrHeap (operator : BinOp) (destination source : Nat)
  | call (returnHandler : Option (StackProg α × Nat × Nat × Nat))
      (target : StackCallTarget) (handler : Option (StackProg α × Nat × Nat))
  | seq (first second : StackProg α)
  | ite (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (thenBranch elseBranch : StackProg α)
  | loop (body : StackProg α)
  | jumpLower (register target : Nat) (label : Nat)
  | alloc (words : Nat)
  | storeConsts (source bitmap : Nat) (stub : Option Nat)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | raise (exception : Nat)
  | return (value : Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (returnAddress : Nat)
  | tick
  | locValue (destination label entry : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
  | rawCall (target : Nat)
  | stackAlloc (words : Nat)
  | stackFree (words : Nat)
  | stackStore (register offset : Nat)
  | stackStoreAny (register offsetRegister : Nat)
  | stackLoad (register offset : Nat)
  | stackLoadAny (register offsetRegister : Nat)
  | stackGetSize (register : Nat)
  | stackSetSize (register : Nat)
  | bitmapLoad (destination address : Nat)
  | halt (register : Nat)
  deriving Repr

def stackSeq : List (StackProg α) → StackProg α
  | [] => .skip
  | [program] => program
  | program :: programs => .seq program (stackSeq programs)

def stackHandlerSlots (perf : Bool) : Nat :=
  if perf then 5 else 3

def stackPerfRsp : Nat := 14

def stackPerfRbp : Nat := 15

/- The CakeML stack argument move copies the stack-resident arguments into a
   fresh frame. `scratch` is the register used for the load/store pair. -/
def stackMove : Nat → Nat → Nat → Nat → StackProg α → StackProg α
  | 0, _, _, _, program => program
  | count + 1, start, offset, scratch, program =>
      .seq (stackMove count (start + 1) offset scratch program)
        (.seq (.stackLoad scratch (start + offset))
          (.stackStore scratch start))

def stackArgs (count frameOffset scratch : Nat) : StackProg α :=
  stackMove count 0 frameOffset scratch (.stackAlloc count)

def stackHandlerArgs (perf : Bool) (count frameOffset scratch : Nat) : StackProg α :=
  stackArgs count (frameOffset + stackHandlerSlots perf) scratch

/- The handler record layout follows `PushHandler_def` in CakeML:
   slot 0 = handler entry marker, slot 1 = handler PC, slot 2 = previous
   handler, and (in perf mode) slots 3 and 4 preserve stack/frame pointers. -/
def stackPushHandler (perf : Bool) (handlerLabel exceptionLabel register : Nat) :
    StackProg α :=
  stackSeq [
    .stackAlloc (stackHandlerSlots perf),
    .const register 1,
    .stackStore register 0,
    .locValue register handlerLabel exceptionLabel,
    .stackStore register 1,
    .get register .handler,
    .stackStore register 2,
    (if perf then
      stackSeq [
        .arith .or register stackPerfRsp stackPerfRsp,
        .stackStore register 3,
        .arith .or register stackPerfRbp stackPerfRbp,
        .stackStore register 4
      ]
    else .skip),
    .stackGetSize register,
    .set .handler register
  ]

def stackPopHandler (perf : Bool) (register : Nat) (program : StackProg α) :
    StackProg α :=
  stackSeq [
    .stackLoad register 2,
    .set .handler register,
    .stackFree (stackHandlerSlots perf),
    program
  ]

def stackRaiseStub (perf : Bool) (register : Nat) : StackProg α :=
  stackSeq [
    .get register .handler,
    .stackSetSize register,
    (if perf then
      stackSeq [
        .stackLoad register 3,
        .arith .or register stackPerfRsp register,
        .stackLoad register 4,
        .arith .or register stackPerfRbp register
      ]
    else .skip),
    .stackLoad register 2,
    .set .handler register,
    .stackLoad register 1,
    .stackFree (stackHandlerSlots perf),
    .raise register
  ]

/- The HOL development reserves the final stub location for the raise entry.
   The concrete target table will fill this in when stack-to-lab is ported. -/
def stackRaiseStubLocation : Nat := 0

/- The first three section labels are reserved by the executable Flapjack
   runtime-linked entry point: raise, StoreConsts, and the collector. -/
def stackStoreConstsStubLocation : Nat := 1

def stackGcStubLocation : Nat := 2

def stackFunctionFirstLabel : Nat := 3

def wordToStackFfi (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    StackProg α :=
  .ffi function configuration configurationLength array arrayLength 0

def wordToStackRaise (_exception : Nat) : StackProg α :=
  .call none (.label stackRaiseStubLocation) none

def wordToStackCallNoHandler (_perf : Bool) (target : Nat)
    (argumentCount frameOffset scratch : Nat)
    (returnValues : List Nat) (returnCode : StackProg α)
    (returnLabel entryLabel : Nat) : StackProg α :=
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target) none
  stackSeq [
    stackArgs (argumentCount + 1) frameOffset scratch,
    callCode,
    .stackFree (returnValues.length)
  ]

def wordToStackCallWithHandler (perf : Bool) (target : Nat)
    (argumentCount frameOffset scratch : Nat)
    (returnCode handlerCode : StackProg α)
    (returnLabel entryLabel handlerLabel exceptionLabel : Nat) : StackProg α :=
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target)
      (some (handlerCode, exceptionLabel, handlerLabel))
  stackSeq [
    stackPushHandler perf handlerLabel exceptionLabel scratch,
    stackHandlerArgs perf (argumentCount + 1) frameOffset scratch,
    callCode
  ]

theorem stackSeq_single (program : StackProg α) :
    stackSeq [program] = program := by
  rfl

theorem wordToStackFfi_shape (α : Type u) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    wordToStackFfi (α := α) function configuration configurationLength array arrayLength =
      .ffi function configuration configurationLength array arrayLength 0 := by
  rfl

theorem wordToStackRaise_shape (α : Type u) (exception : Nat) :
    wordToStackRaise (α := α) exception =
      .call none (.label stackRaiseStubLocation) none := by
  rfl

end Flapjack
