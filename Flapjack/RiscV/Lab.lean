import Flapjack.Lab
import Flapjack.StackAlloc
import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.WordToStack

/-!
# LabLang to RISC-V

This module is the first concrete assembler boundary after StackLang
flattening. It computes byte positions for local labels, resolves symbolic
jumps, and lowers the LabLang operations supported by the current RISC-V
model. Unsupported target operations fail through Option rather than being
silently emitted.
-/

namespace Flapjack.RiscV

def labConditionPreludeCount (operator : Cmp)
    (right : WordRegImm (Word width)) : Nat :=
  match right with
  | .reg _ => match operator with | .test | .notTest => 1 | _ => 0
  | .imm value =>
      if value == 0 then
        match operator with | .test | .notTest => 1 | _ => 0
      else 1

def labLineInstructionCount : LabLine (Word width) → Nat
  | .label _ _ _ => 0
  | .asm operation _ _ =>
      match operation with
      | .shift .ror _ _ _ => 5
      | .word (.arith (.longMul _ _ _ _)) => 2
      | .word (.arith (.addCarry _ _ _ _ _)) => 6
      | _ => 1
  | .labAsm operation _ _ =>
      match operation with
      | .jump _ | .call _ | .locValue _ _ | .install | .halt => 1
      | .jumpCmp operator _ right _ => 1 + labConditionPreludeCount operator right
      | .callFfi _ => 2
      | .heapAlloc _ => 1

def labCollectLabels (_sectionId : Nat) (position : Nat) :
    List (LabLine (Word width)) → List (Nat × Nat)
  | [] => []
  | .label _ label _ :: lines =>
      (label, position) :: labCollectLabels _sectionId position lines
  | line :: lines =>
      labCollectLabels _sectionId
        (position + 4 * labLineInstructionCount line) lines

def labLookupPosition (label : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (candidate, position) :: labels =>
      if label == candidate then some position
      else labLookupPosition label labels

def labResolveRef (sectionId : Nat) (labels : List (Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  if ref.sectionId == sectionId then labLookupPosition ref.label labels
  else none

def labOffset [NeZero width] (target position : Nat) : Word width :=
  if target >= position then
    BitVec.ofNat width (target - position)
  else
    0 - BitVec.ofNat width (position - target)

def labBranch [NeZero width] (operator : Cmp) (left right : Fin 32)
    (offset : Word width) : Instruction width :=
  match operator with
  | .equal => .branchNe left right offset
  | .notEqual => .branchEq left right offset
  | .less => .branchGe left right offset
  | .notLess => .branchLt left right offset
  | .lower => .branchGeU left right offset
  | .notLower => .branchLtU left right offset
  | .test => .branchNe left right offset
  | .notTest => .branchEq left right offset

def labBinOpInstruction [NeZero width] (operator : BinOp)
    (destination left right : Nat) : Option (Instruction width) := do
  let destination ← registerOfNat destination
  let left ← registerOfNat left
  let right ← registerOfNat right
  pure (match operator with
    | .add => .add destination left right
    | .sub => .sub destination left right
    | .and => .and destination left right
    | .or => .or destination left right
    | .xor => .xor destination left right)

def labShiftInstructions [NeZero width] (operator : Shift)
    (destination left right : Nat) : Option (List (Instruction width)) := do
  if operator == .ror &&
      [destination, left, right].any (· == 31) then
    none
  else
    let destination ← registerOfNat destination
    let left ← registerOfNat left
    let right ← registerOfNat right
    match operator with
    | .lsl => pure [.sll destination left right]
    | .lsr => pure [.srl destination left right]
    | .asr => pure [.sra destination left right]
    | .ror => pure [
        .ori 31 0 (BitVec.ofNat width width),
        .sub 31 31 right,
        .sll 31 left 31,
        .srl destination left right,
        .or destination destination 31]

def labCompilePlain [NeZero width] :
    LabPlain (Word width) → Option (List (Instruction width))
  | .word (.arith operation) => wordArithToInstructions operation
  | .word instruction => (wordInstToInstruction instruction).map List.singleton
  | .const destination value => do
      let destination ← registerOfNat destination
      pure [.addi destination 0 (BitVec.ofNat width value)]
  | .arith operator destination left right =>
      (labBinOpInstruction operator destination left right).map List.singleton
  | .shift operator destination left right =>
      labShiftInstructions operator destination left right
  | .tick => pure [.addi 0 0 0]
  | .jumpReg register => do
      let register ← registerOfNat register
      pure [.jalr 0 register 0]
  | .shareMem operator register address =>
      wordShareInstToInstructions operator register (.var address)
  | .codeBufferWrite _ _ => none

def labCompileAsm [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let target ← labResolveRef sectionId labels target
      pure [.jal 0 (labOffset target position)]
  | .call target => do
      let target ← labResolveRef sectionId labels target
      pure [.jal 1 (labOffset target position)]
  | .locValue register target => do
      let register ← registerOfNat register
      let target ← labResolveRef sectionId labels target
      pure [.addi register 0 (BitVec.ofNat width target)]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveRef sectionId labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let service ← lookupWordFfiService function context.services
      pure [.addi 14 0 (BitVec.ofNat width service), .ecall]
  | .heapAlloc _ | .install | .halt => none

def labCompileLines [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileLines context sectionId labels position lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsm context sectionId labels position operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines
      pure (code ++ rest)

def compileLabSection [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection (Word width)) : Option (List (Instruction width)) :=
  let labels := labCollectLabels sectionData.name 0 sectionData.lines
  labCompileLines context sectionData.name labels 0 sectionData.lines

/-! The first executable StackLang-to-RISC-V composition.  StackRemove lowers
    the stack and runtime-store operations, LabLang flattens the remaining
    control flow, and this boundary selects concrete RISC-V instructions. -/
def compileStackProgramToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg (Word width)) :
    Option (List (Instruction width)) :=
  compileLabSection context
    (labProgramToSectionAfterStackRemove config sectionId initialLabel program)

/-! The current concrete Word-to-Stack compiler uses `Nat` for constants,
    while the target backend uses width-indexed words.  Since only conditional
    immediates carry the StackProg type parameter, this adapter is deliberately
    small and explicit. -/
def labAsmNatToWord [NeZero width] : LabAsm Nat → LabAsm (Word width)
  | .jump target => .jump target
  | .jumpCmp operator condition (.imm value) target =>
      .jumpCmp operator condition (.imm (BitVec.ofNat width value)) target
  | .jumpCmp operator condition (.reg register) target =>
      .jumpCmp operator condition (.reg register) target
  | .call target => .call target
  | .locValue register target => .locValue register target
  | .callFfi function => .callFfi function
  | .heapAlloc words => .heapAlloc words
  | .install => .install
  | .halt => .halt

def labPlainNatToWord [NeZero width] : LabPlain Nat → LabPlain (Word width)
  | .word instruction => .word instruction
  | .const destination value => .const destination value
  | .arith operator destination left right =>
      .arith operator destination left right
  | .shift operator destination left right =>
      .shift operator destination left right
  | .tick => .tick
  | .jumpReg register => .jumpReg register
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .shareMem operator register address =>
      .shareMem operator register address

def labLineNatToWord [NeZero width] : LabLine Nat → LabLine (Word width)
  | .label sectionId label length => .label sectionId label length
  | .asm operation bytes length =>
      .asm (labPlainNatToWord operation) bytes length
  | .labAsm operation bytes length =>
      .labAsm (labAsmNatToWord operation) bytes length

def labSectionNatToWord [NeZero width] (sectionData : LabSection Nat) :
    LabSection (Word width) :=
  { name := sectionData.name
    lines := sectionData.lines.map labLineNatToWord }

def compileLabSectionNat [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection Nat) : Option (List (Instruction width)) :=
  compileLabSection context (labSectionNatToWord sectionData)

def compileStackProgramNatToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg Nat) :
    Option (List (Instruction width)) :=
  compileLabSectionNat context
    (labProgramToSectionAfterStackRemove config sectionId initialLabel program)

def compileWordProgramNatToRiscV [NeZero width] [BEq Nat]
    (context : WordFfiContext) (wordConfig : WordStackConfig)
    (removeConfig : StackRemoveConfig) (sectionId initialLabel : Nat)
    (program : WordProg Nat) : Option (List (Instruction width)) := do
  let stackProgram ← wordToStackProgNat wordConfig program
  compileStackProgramNatToRiscV context removeConfig sectionId initialLabel
    stackProgram

def compileWordProgramToRiscV [NeZero width]
    (context : WordFfiContext) (wordConfig : WordStackConfig)
    (removeConfig : StackRemoveConfig) (sectionId initialLabel : Nat)
    (program : WordProg (Word width)) : Option (List (Instruction width)) := do
  let stackProgram ← wordToStackProgWord wordConfig program
  compileStackProgramNatToRiscV context removeConfig sectionId initialLabel
    stackProgram

def labSectionInstructionCount (sectionData : LabSection (Word width)) : Nat :=
  sectionData.lines.foldl
    (fun count line => count + labLineInstructionCount line) 0

def labCollectProgramLabels (base : Nat) :
    LabProgram (Word width) → List (Nat × Nat × Nat)
  | [] => []
  | sectionData :: sections =>
      let localLabels := labCollectLabels sectionData.name 0 sectionData.lines
      let globalLabels := localLabels.map
        (fun (label, position) => (sectionData.name, label, base + position))
      globalLabels ++ labCollectProgramLabels
        (base + 4 * labSectionInstructionCount sectionData) sections

def labLookupProgramPosition (sectionId label : Nat) :
    List (Nat × Nat × Nat) → Option Nat
  | [] => none
  | (candidateSection, candidateLabel, position) :: labels =>
      if sectionId == candidateSection && label == candidateLabel then some position
      else labLookupProgramPosition sectionId label labels

def labResolveProgramRef (labels : List (Nat × Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  labLookupProgramPosition ref.sectionId ref.label labels

def labCompileAsmProgram [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let target ← labResolveProgramRef labels target
      pure [.jal 0 (labOffset target position)]
  | .call target => do
      let target ← labResolveProgramRef labels target
      pure [.jal 1 (labOffset target position)]
  | .locValue register target => do
      let register ← registerOfNat register
      let target ← labResolveProgramRef labels target
      pure [.addi register 0 (BitVec.ofNat width target)]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveProgramRef labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let service ← lookupWordFfiService function context.services
      pure [.addi 14 0 (BitVec.ofNat width service), .ecall]
  | .heapAlloc _ | .install | .halt => none

def labCompileProgramLines [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLines context labels position lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLines context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmProgram context labels position operation
      let rest ← labCompileProgramLines context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines
      pure (code ++ rest)

def labCompileProgramSections [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (base : Nat) :
    LabProgram (Word width) → Option (List (Instruction width))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLines context labels base sectionData.lines
      let rest ← labCompileProgramSections context labels
        (base + 4 * labSectionInstructionCount sectionData) sections
      pure (code ++ rest)

def compileLabProgram [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (Instruction width)) :=
  let labels := labCollectProgramLabels 0 program
  labCompileProgramSections context labels 0 program

/-! CakeML's target assembler turns `Halt` into a jump to the target's halt
    PC.  The existing ordinary compiler intentionally rejects that pseudo-op;
    this parallel path computes a halt PC immediately after the linked image,
    emits the jump, and appends a self-loop at that PC. -/
def labCompileAsmWithHalt [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position haltPc : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let target ← labResolveProgramRef labels target
      pure [.jal 0 (labOffset target position)]
  | .call target => do
      let target ← labResolveProgramRef labels target
      pure [.jal 1 (labOffset target position)]
  | .locValue register target => do
      let register ← registerOfNat register
      let target ← labResolveProgramRef labels target
      pure [.addi register 0 (BitVec.ofNat width target)]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveProgramRef labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let service ← lookupWordFfiService function context.services
      pure [.addi 14 0 (BitVec.ofNat width service), .ecall]
  | .halt => pure [.jal 0 (labOffset haltPc position)]
  | .heapAlloc _ | .install => none

def labCompileProgramLinesWithHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position haltPc : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLinesWithHalt context labels position haltPc lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLinesWithHalt context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) haltPc lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmWithHalt context labels position haltPc operation
      let rest ← labCompileProgramLinesWithHalt context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) haltPc lines
      pure (code ++ rest)

def labCompileProgramSectionsWithHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base haltPc : Nat) :
    LabProgram (Word width) → Option (List (Instruction width))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLinesWithHalt context labels base haltPc
        sectionData.lines
      let rest ← labCompileProgramSectionsWithHalt context labels
        (base + 4 * labSectionInstructionCount sectionData) haltPc sections
      pure (code ++ rest)

def labProgramInstructionCount : LabProgram (Word width) → Nat
  | [] => 0
  | sectionData :: sections =>
      labSectionInstructionCount sectionData + labProgramInstructionCount sections

def compileLabProgramWithHalt [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (Instruction width)) := do
  let labels := labCollectProgramLabels 0 program
  let haltPc := 4 * labProgramInstructionCount program
  let code ← labCompileProgramSectionsWithHalt context labels 0 haltPc program
  pure (code ++ [.jal 0 0])

def executeLabProgramWithHalt [NeZero width] (fuel : Nat)
    (context : WordFfiContext) (program : LabProgram (Word width))
    (state : State width) : Option (State width) :=
  let haltPc := BitVec.ofNat width (4 * labProgramInstructionCount program)
  match compileLabProgramWithHalt context program with
  | some code =>
      executeCodeUntil fuel 0 haltPc code { state with pc := 0 }
  | none => none

/-! A linker result that keeps section entry addresses alongside the flattened
    image. The plain `compileLabProgram` API is convenient for consumers that
    only need code; correctness proofs need the section boundary to initialize
    a function runner at the generated entry address. -/
def compileLabProgramLinkedAux [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base : Nat) : LabProgram (Word width) →
      Option (List (Nat × Word width × List (Instruction width)))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLines context labels base sectionData.lines
      let rest ← compileLabProgramLinkedAux context labels
        (base + 4 * labSectionInstructionCount sectionData) sections
      pure ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinked [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let labels := labCollectProgramLabels 0 program
  compileLabProgramLinkedAux context labels 0 program

def compileStackProgramListToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg (Word width))) :
    Option (List (Instruction width)) :=
  compileLabProgram context
    (programs.map (fun (sectionId, program) =>
      labProgramToEntrySection sectionId entryLabel initialLabel
        (stackRemoveComplete config program)))

def compileStackProgramNatListToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileLabProgram context
    ((programs.map (fun (sectionId, program) =>
      labProgramToEntrySection sectionId entryLabel initialLabel
        (stackRemoveComplete config program))).map labSectionNatToWord)

def compileStackProgramNatListWithHaltToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileLabProgramWithHalt context
    ((programs.map (fun (sectionId, program) =>
      labProgramToEntrySection sectionId entryLabel initialLabel
        (stackRemoveComplete config program))).map labSectionNatToWord)

/-! StackAlloc-aware composition.  CakeML's allocator pass installs a runtime
    collector stub as a separate section and rewrites heap allocation into a
    call to that section. -/
def compileStackProgramNatListWithStackAllocToRiscV [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  let programs := stackAllocCompile allocConfig programs
  compileStackProgramNatListToRiscV context removeConfig entryLabel initialLabel programs

def compileStackProgramNatListWithSimpleGcToRiscV [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileStackProgramNatListWithHaltToRiscV context removeConfig
    entryLabel initialLabel
    (stackAllocCompileWithSimpleGc allocConfig gcConfig programs)

def compileStackProgramNatListLinkedToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  compileLabProgramLinked context
    ((programs.map (fun (sectionId, program) =>
      labProgramToEntrySection sectionId entryLabel initialLabel
        (stackRemoveComplete config program))).map labSectionNatToWord)

theorem labLineInstructionCount_ffi :
    labLineInstructionCount
        (.labAsm (.callFfi "sum") [] 0 : LabLine (Word width)) = 2 := by
  rfl

theorem compileLabSection_ffi [NeZero width] :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.addi 14 0 (BitVec.ofNat width 7), .ecall] := by
  simp [compileLabSection, labCollectLabels, labCompileLines,
    labLineInstructionCount, labCompileAsm, lookupWordFfiService]

theorem compileLabProgram_cross_section_jump [NeZero width] :
    compileLabProgram (width := width) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
      some [.jal 0 (BitVec.ofNat width 4),
        .addi 1 0 (BitVec.ofNat width 7)] := by
  have hcount :
      labLineInstructionCount
          (.labAsm (.jump ⟨2, 0⟩) [] 0 : LabLine (Word width)) = 1 := by
    rfl
  simp [compileLabProgram, labCollectProgramLabels,
    labCollectLabels, labSectionInstructionCount, labCompileProgramSections,
    labCompileProgramLines, labCompileAsmProgram,
    labCompilePlain, labLookupProgramPosition, labResolveProgramRef,
    labOffset, registerOfNat, hcount]

end Flapjack.RiscV
