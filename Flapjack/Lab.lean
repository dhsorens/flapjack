import Flapjack.Stack
import Flapjack.StackRemove

/-!
# LabLang

LabLang is CakeML's target-neutral, labelled assembly layer.  This is the
structured-to-flat portion of `stack_to_labScript.sml`: StackLang control
flow is flattened into labels and jumps, while target instruction encoding is
left to the RISC-V backend.
-/

namespace Flapjack

structure LabRef where
  sectionId : Nat
  label : Nat
  deriving DecidableEq, Repr

inductive LabAsm (α : Type u) where
  | jump (target : LabRef)
  | jumpCmp (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (target : LabRef)
  | call (target : LabRef)
  | locValue (register : Nat) (target : LabRef)
  | callFfi (function : FunName)
  | heapAlloc (words : Nat)
  | install
  | halt
  deriving Repr

inductive LabJump where
  | direct (target : LabRef)
  | register (register : Nat)
  deriving DecidableEq, Repr

inductive LabPlain (α : Type u) where
  | word (instruction : WordInst)
  | const (destination value : Nat)
  | arith (operator : BinOp) (destination left right : Nat)
  | shift (operator : Shift) (destination left right : Nat)
  | tick
  | jumpReg (register : Nat)
  | codeBufferWrite (address value : Nat)
  | shareMem (operator : WordMemOp) (register address : Nat)
  deriving Repr

inductive LabLine (α : Type u) where
  | label (sectionId label length : Nat)
  | asm (operation : LabPlain α) (bytes : List (BitVec 8)) (length : Nat)
  | labAsm (operation : LabAsm α) (bytes : List (BitVec 8)) (length : Nat)
  deriving Repr

structure LabSection (α : Type u) where
  name : Nat
  lines : List (LabLine α)
  deriving Repr

abbrev LabProgram (α : Type u) := List (LabSection α)

def labSectionNumber : LabSection α → Nat
  | .mk name _ => name

def labSectionLines : LabSection α → List (LabLine α)
  | .mk _ lines => lines

def labIsSequence : StackProg α → Bool
  | .seq _ _ => true
  | _ => false

def labFindLabel (label : Nat) : List Nat → Nat
  | [] => 0
  | candidate :: labels =>
      match label with
      | 0 => candidate
      | label + 1 => labFindLabel label labels

def labNegateCmp : Cmp → Cmp
  | .less => .notLess
  | .equal => .notEqual
  | .lower => .notLower
  | .test => .notTest
  | .notLess => .less
  | .notEqual => .equal
  | .notLower => .lower
  | .notTest => .test

def labCompileJump : StackCallTarget → LabJump
  | .label target => .direct ⟨target, 0⟩
  | .register register => .register register

def labIsSkip : StackProg α → Bool
  | .skip => true
  | _ => false

structure FlattenResult (α : Type u) where
  lines : List (LabLine α)
  terminal : Bool
  nextLabel : Nat
  deriving Repr

def labLabel (sectionId label : Nat) : LabLine α :=
  .label sectionId label 0

def labJump (sectionId label : Nat) : LabLine α :=
  .labAsm (.jump ⟨sectionId, label⟩) [] 0

def labJumpCmp (operator : Cmp) (condition : Nat) (right : WordRegImm α)
    (sectionId label : Nat) : LabLine α :=
  .labAsm (.jumpCmp operator condition right ⟨sectionId, label⟩) [] 0

def labFlatten (tail : Bool) (sectionId counter : Nat)
    (continues breaks : List Nat) : StackProg α → FlattenResult α
  | .skip => ⟨[], false, counter⟩
  | .inst instruction => ⟨[.asm (.word instruction) [] 0], false, counter⟩
  | .shMem operator source address =>
      ⟨[.asm (.shareMem operator source address) [] 0], false, counter⟩
  | .arith operator destination left right =>
      ⟨[.asm (.arith operator destination left right) [] 0], false, counter⟩
  | .shift operator destination left right =>
      ⟨[.asm (.shift operator destination left right) [] 0], false, counter⟩
  | .const destination value =>
      ⟨[.asm (.const destination value) [] 0], false, counter⟩
  | .tick => ⟨[.asm .tick [] 0], false, counter⟩
  | .raise register | .return register =>
      ⟨[.asm (.jumpReg register) [] 0], true, counter⟩
  | .break label =>
      ⟨[labJump sectionId (labFindLabel label breaks)], true, counter⟩
  | .continue label =>
      ⟨[labJump sectionId (labFindLabel label continues)], true, counter⟩
  | .rawCall _target =>
      ⟨[.labAsm (.jump ⟨sectionId, 1⟩) [] 0], true, counter⟩
  | .jumpLower register target label =>
      ⟨[labJumpCmp .lower register (.reg target) label 0], false, counter⟩
  | .install _ _ _ _ returnAddress =>
      ⟨[.labAsm (.locValue returnAddress ⟨sectionId, counter⟩) [] 0,
        .labAsm .install [] 0, labLabel sectionId counter], false, counter + 1⟩
  | .codeBufferWrite address value =>
      ⟨[.asm (.codeBufferWrite address value) [] 0], false, counter⟩
  | .ffi function _ _ _ _ returnAddress =>
      ⟨[.labAsm (.locValue returnAddress ⟨sectionId, counter⟩) [] 0,
        .labAsm (.callFfi function) [] 0, labLabel sectionId counter],
        false, counter + 1⟩
  | .alloc words =>
      ⟨[.labAsm (.heapAlloc words) [] 0], false, counter⟩
  | .locValue register label entry =>
      ⟨[.labAsm (.locValue register ⟨label, entry⟩) [] 0], false, counter⟩
  | .halt _register =>
      ⟨[.labAsm .halt [] 0], true, counter⟩
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _
    | .storeConsts _ _ _ | .stackAlloc _ | .stackFree _ | .stackStore _ _
    | .stackStoreAny _ _
    | .stackLoad _ _ | .stackLoadAny _ _ | .stackGetSize _ | .stackSetSize _
    | .bitmapLoad _ _ | .dataBufferWrite _ _ =>
      ⟨[], false, counter⟩
  | .call none target none =>
      ⟨[match labCompileJump target with
        | .direct target => .labAsm (.jump target) [] 0
        | .register register => .asm (.jumpReg register) [] 0], true, counter⟩
  | .call (some (returnCode, linkRegister, returnLabel, _entryLabel)) target handler =>
      let returnResult := labFlatten false sectionId counter continues breaks returnCode
      let callPrefix : List (LabLine α) :=
        [.labAsm (.locValue linkRegister ⟨sectionId, returnLabel⟩) [] 0,
         match labCompileJump target with
         | .direct target => .labAsm (.jump target) [] 0
         | .register register => .asm (.jumpReg register) [] 0,
         labLabel sectionId returnLabel]
      match handler with
      | none =>
          ⟨callPrefix ++ returnResult.lines, returnResult.terminal, returnResult.nextLabel⟩
      | some (handlerCode, handlerLabel, exceptionLabel) =>
          let handlerResult :=
            labFlatten false sectionId returnResult.nextLabel continues breaks handlerCode
          ⟨callPrefix ++ returnResult.lines ++
            [labJump sectionId handlerResult.nextLabel,
             labLabel sectionId handlerLabel] ++ handlerResult.lines ++
            [labLabel sectionId handlerResult.nextLabel],
            returnResult.terminal && handlerResult.terminal,
            handlerResult.nextLabel + 1⟩
  | .call _ _ _ =>
      ⟨[], false, counter⟩
  | .seq first second =>
      let firstResult := labFlatten false sectionId counter continues breaks first
      let secondResult :=
        labFlatten false sectionId firstResult.nextLabel continues breaks second
      let separator :=
        if tail then [labLabel sectionId 1] else []
      ⟨firstResult.lines ++ separator ++ secondResult.lines,
        firstResult.terminal || secondResult.terminal, secondResult.nextLabel⟩
  | .ite operator condition right thenBranch elseBranch =>
      let thenResult := labFlatten false sectionId counter continues breaks thenBranch
      let elseResult :=
        labFlatten false sectionId thenResult.nextLabel continues breaks elseBranch
      if labIsSkip thenBranch && labIsSkip elseBranch then
        ⟨[], false, counter⟩
      else if labIsSkip thenBranch then
        ⟨[labJumpCmp operator condition right sectionId counter] ++
          elseResult.lines ++ [labLabel sectionId counter],
          false, elseResult.nextLabel + 1⟩
      else if labIsSkip elseBranch then
        ⟨[labJumpCmp (labNegateCmp operator) condition right sectionId counter] ++
          thenResult.lines ++ [labLabel sectionId counter],
          false, thenResult.nextLabel + 1⟩
      else if thenResult.terminal then
        ⟨[labJumpCmp (labNegateCmp operator) condition right sectionId counter] ++
          thenResult.lines ++ [labLabel sectionId counter] ++ elseResult.lines,
          elseResult.terminal, elseResult.nextLabel + 1⟩
      else if elseResult.terminal then
        ⟨[labJumpCmp operator condition right sectionId counter] ++
          elseResult.lines ++ [labLabel sectionId counter] ++ thenResult.lines,
          thenResult.terminal, thenResult.nextLabel + 1⟩
      else
        ⟨[labJumpCmp operator condition right sectionId counter] ++
          elseResult.lines ++ [labJump sectionId (elseResult.nextLabel + 1),
            labLabel sectionId counter] ++ thenResult.lines ++
          [labLabel sectionId (elseResult.nextLabel + 1)],
          thenResult.terminal && elseResult.terminal, elseResult.nextLabel + 2⟩
  | .loop body =>
      let continueLabel := counter
      let breakLabel := counter + 1
      let bodyResult :=
        labFlatten false sectionId (counter + 2)
          (continueLabel :: continues) (breakLabel :: breaks) body
      ⟨[labLabel sectionId continueLabel] ++ bodyResult.lines ++
        [labJump sectionId continueLabel, labLabel sectionId breakLabel],
        false, bodyResult.nextLabel⟩
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def labProgramToSection (sectionId initialLabel : Nat) (program : StackProg α) :
    LabSection α :=
  let result := labFlatten true sectionId initialLabel [] [] program
  let finalLabel := if labIsSequence program then result.nextLabel else 1
  ⟨sectionId, result.lines ++ [labLabel sectionId finalLabel]⟩

/-! Function sections have a public entry label.  The single-section helper
    above predates cross-function linking and deliberately omits that label
    for non-sequences; generated calls target the entry label, so the
    multi-section linker uses this explicit form. -/
def labProgramToEntrySection (sectionId entryLabel initialLabel : Nat)
    (program : StackProg α) : LabSection α :=
  let sectionData := labProgramToSection sectionId initialLabel program
  { sectionData with
    lines := labLabel sectionId entryLabel :: sectionData.lines }

/- The backend-facing composition applies the stack-removal pass before
   flattening.  Keeping this as a separate entry point preserves the raw
   StackLang boundary for pass-by-pass proofs. -/
def labProgramToSectionAfterStackRemove [OfNat α 0] [OfNat α 1]
    (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg α) : LabSection α :=
  labProgramToSection sectionId initialLabel
    (stackRemoveComplete config program)

theorem labFlatten_skip (sectionId counter : Nat) (continues breaks : List Nat) :
    labFlatten false sectionId counter continues breaks (.skip : StackProg α) =
      ⟨[], false, counter⟩ := by
  simp [labFlatten]

theorem labFlatten_ffi (function : FunName) (sectionId counter returnAddress : Nat) :
    (labFlatten false sectionId counter [] []
      (.ffi function 1 2 3 4 returnAddress : StackProg Nat)).lines =
      [.labAsm (.locValue returnAddress ⟨sectionId, counter⟩) [] 0,
       .labAsm (.callFfi function) [] 0, .label sectionId counter 0] := by
  simp [labFlatten, labLabel]

end Flapjack
