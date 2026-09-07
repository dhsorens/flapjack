import Flapjack.PanGlobals
import Flapjack.Compile
import Flapjack.CrepToLoop
import Flapjack.Word
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Loops
import Flapjack.RiscV.Link
import Flapjack.RiscV.Lab

/-!
An executable composition of the currently ported Pancake passes.

The result keeps each intermediate representation visible so the eventual
simulation theorem can be proved pass by pass. This composition covers the
front-end normalization and structure/global passes, Pancake-to-Crepe,
Crepe-to-Loop, and Loop-to-Word. The typed RISC-V artifact boundary is also
exposed, while instruction selection remains partial in
`Flapjack.RiscV.Backend`.
-/

namespace Flapjack

def pipelineExceptionCodes (fromNat : Nat → α) : Nat → List (Decl α) → InfoMap α
  | _, [] => []
  | index, .exnDecl exception _ :: declarations =>
      (exception, fromNat index) :: pipelineExceptionCodes fromNat (index + 1) declarations
  | index, _ :: declarations => pipelineExceptionCodes fromNat (index + 1) declarations

def pipelineCrepeContext [BEq α] [Add α]
    (bytesInWord : α) (fromNat : Nat → α)
    (program : GlobalCompiledProgram α) : CompileContext α :=
  { vars := []
    functions := []
    exceptions := pipelineExceptionCodes fromNat 0 program.declarations
    maxVar := 0
    bytesInWord := bytesInWord }

def pipelineFunctionInfos (firstLabel : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat)
  | [] => []
  | function :: functions =>
      (function.name, (firstLabel, function.params.length)) ::
        pipelineFunctionInfos (firstLabel + 1) functions

def pipelineLoopFunctionsAux [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction α) → List (Nat × List Nat × LoopProg α)
  | _, [] => []
  | label, function :: functions =>
      let context : LoopContext α :=
        { vars := []
          functions := functionInfos
          maxVar := function.params.length
          target := architecture }
      (label, function.params, loopCompileProg context [] function.body) ::
        pipelineLoopFunctionsAux architecture functionInfos (label + 1) functions

def pipelineLoopFunctions [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction α)) :
    List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctionsAux architecture (pipelineFunctionInfos firstLabel functions)
    firstLabel functions

def pipelineWordFunctions [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × List Nat × WordProg α) :=
  functions.map (fun (label, parameters, body) =>
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    (label, parameters.map (fun name => name + 2), loopToWordProg context body))

/-! StackLang view of the register-coloured Word pipeline.  This is the
    executable bridge used by the RISC-V-only backend path below; functions
    that require spills or unsupported Word constructors remain explicit
    `none` results until those allocator cases are ported. -/
def pipelineWordFunctionsToStack [NeZero width] :
    List (Nat × List Nat × WordProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let config := { RiscV.wordStackIdentityConfig body with
        handlerLabel := label }
      let stackBody ← RiscV.wordToStackProgWord config body
      let rest ← pipelineWordFunctionsToStack functions
      pure ((label, parameters, stackBody) :: rest)

/-! The allocator-aware counterpart of `pipelineWordFunctionsToStack`.  The
    coloured Word program uses concrete register names, so the StackLang
    boundary can use the same identity location map while still rejecting
    programs that the allocator cannot colour. -/
def pipelineAllocatedWordFunctionsToStack [NeZero width] :
    List (Nat × List Nat × WordProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat)) :=
  pipelineWordFunctionsToStack

/-! Spill-aware allocator pipeline.  This path retains the SSA-renamed Word
    program and passes the CakeML-shaped clash-tree/preference allocator's
    concrete register/stack locations directly to `word_to_stack`.  The
    reserved x31 scratch register is outside the allocator's register pool,
    and x29 is reserved independently for spilled addresses. -/
def pipelineWordFunctionsAllocatedWithSpills [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody :=
        loopToWordProg context body
      let (_, renamedParameters, renamedBody, allocation) ←
        wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
          wordParameters unallocatedBody
      let config : RiscV.WordStackConfig :=
        { locations := allocation.locations
          scratch := 31
          stackBase := 0
          addressScratch := 29
          handlerLabel := label }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config renamedParameters
        renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithSpills functions
      pure ((label, wordParameters, stackBody) :: rest)

/-! Spill-aware pipeline with CakeML's append-only bitmap state.  The
    location-aware Word-to-Stack boundary derives GC roots from the concrete
    spill slots produced by the allocator and carries the updated bitmap
    table into the next function. -/
def pipelineWordFunctionAllocatedWithSpillsAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState)
    (function : Nat × List Nat × LoopProg (RiscV.Word width)) :
    Option ((Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState) :=
  let (label, parameters, body) := function
  do
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    let wordParameters := parameters.map (fun name => name + 2)
    let unallocatedBody := loopToWordProg context body
    let (_, renamedParameters, renamedBody, allocation) ←
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
        wordParameters unallocatedBody
    let config : RiscV.WordStackConfig :=
      { locations := allocation.locations
        scratch := 31
        stackBase := 0
        addressScratch := 29
        handlerLabel := label }
    let (stackBody, bitmaps) ←
      RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
        renamedParameters wordAllocatableRegisters.length config.scratch
        allocation.nextSpill (some 1) bitmaps renamedBody
    pure ((label, wordParameters, stackBody), bitmaps)

def pipelineWordFunctionsAllocatedWithSpillsAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option
        (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState)
  | [] => some ([], bitmaps)
  | function :: functions => do
      let (compiled, bitmaps) ←
        pipelineWordFunctionAllocatedWithSpillsAndBitmaps bitmaps function
      let (rest, bitmaps) ←
        pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps functions
      pure (compiled :: rest, bitmaps)

/-! The bitmap accumulator is threaded through function compilation in source
    order.  This equation makes that sequencing explicit for callers that
    split a declaration list into independently compiled chunks. -/
theorem pipelineWordFunctionsAllocatedWithSpillsAndBitmaps_append [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState)
    (first second : List (Nat × List Nat × LoopProg (RiscV.Word width))) :
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps (first ++ second) =
      match pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps first with
      | none => none
      | some (firstCode, middleBitmaps) =>
          match pipelineWordFunctionsAllocatedWithSpillsAndBitmaps middleBitmaps second with
          | none => none
          | some (secondCode, finalBitmaps) =>
              some (firstCode ++ secondCode, finalBitmaps) := by
  induction first generalizing bitmaps with
  | nil =>
      cases hsecond : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps second <;>
        simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hsecond]
  | cons function functions ih =>
      cases hfunction : pipelineWordFunctionAllocatedWithSpillsAndBitmaps bitmaps function with
      | none => simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction]
      | some compiled =>
          cases hrest : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps compiled.2 functions with
          | none =>
              have htail := ih (bitmaps := compiled.2)
              simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction, hrest, htail]
          | some rest =>
              cases hsecond : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps rest.2 second <;>
                simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction, hrest,
                  hsecond, ih compiled.2]

/-! Graph-coloured Word-to-Stack pipeline.

This is the first pipeline entry point that consumes the CakeML-shaped graph
allocator rather than the earlier greedy spill allocator.  The allocator
returns the SSA-renamed program together with its graph; `wordGraphLocations`
then turns the graph colours into the register/stack locations expected by
`word_to_stack`.  The old spill path remains available while the full
spill-aware SSA metadata and all Word constructors are being ported.
-/
def pipelineWordFunctionsAllocatedWithGraph [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := loopToWordProg context body
      let (_, renamedParameters, allocation, renamedBody) ←
        wordAllocateGraphFunctionWithStackOnlyRenamed wordParameters unallocatedBody
          [] 13 14
      let config : RiscV.WordStackConfig :=
        { locations := wordGraphLocations allocation 13 14
          scratch := 31
          stackBase := 0
          addressScratch := 29 }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config
        renamedParameters renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithGraph functions
      pure ((label, wordParameters, stackBody) :: rest)

/-!
An allocation-aware variant of the Word-function boundary.  The historical
`pipelineWordFunctions` definition remains available for existing artifact
equations; this variant makes register exhaustion explicit and uses the
reserved-register-aware allocator before instruction selection.
-/
def pipelineWordFunctionsAllocated [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context ← wordAllocateContext slots
      let rest ← pipelineWordFunctionsAllocated functions
      pure ((label, wordMapVars context parameters, loopToWordProg context body) :: rest)

/-! Allocation-aware variant that derives clashes from the generated Word
program.  It is still separate from the historical artifact boundary while
the full CakeML branch/loop SSA and spill pass are being ported. -/
def pipelineWordFunctionsAllocatedWithAnalysis [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let unallocatedBody := loopToWordProg ({ vars := [] } : WordContext) body
      let context ← wordAllocateProgramWithSlots slots unallocatedBody
      let rest ← pipelineWordFunctionsAllocatedWithAnalysis functions
      pure ((label, wordMapVars context parameters, loopToWordProg context body) :: rest)

/-! Variant that consumes the same analysis boundary but returns the coloured
    Word program directly.  This is the form expected by the target selector;
    the context is retained alongside the code for later state-relation proofs. -/
def pipelineWordFunctionsAllocatedWithAnalysisAndColour [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let unallocatedBody := loopToWordProg ({ vars := [] } : WordContext) body
      let (context, allocatedBody) ←
        wordAllocateProgramWithSlotsAndColour slots unallocatedBody
      let rest ← pipelineWordFunctionsAllocatedWithAnalysisAndColour functions
      pure ((label, wordMapVars context parameters, allocatedBody) :: rest)

theorem lookupNatInfo_map_add_two_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    lookupNatInfo name (slots.map (fun value => (value, value + 2))) =
      some (name + 2) := by
  induction slots with
  | nil => simp at hname
  | cons head tail ih =>
      simp only [List.mem_cons] at hname
      rcases hname with rfl | hname
      · simp [lookupNatInfo]
      · by_cases heq : head == name
        · have : head = name := by simpa using heq
          subst head
          simp [lookupNatInfo]
        · simp [lookupNatInfo, heq, ih hname]

def pipelineWordContext (slots : List Nat) : WordContext :=
  { vars := slots.map (fun name => (name, name + 2)) }

theorem wordFindVar_pipelineWordContext_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    wordFindVar (pipelineWordContext slots) name = name + 2 := by
  simp [pipelineWordContext, wordFindVar,
    lookupNatInfo_map_add_two_of_mem slots name hname]

def pipelinePrependInitializers (initializers : List (Prog α)) :
    List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      if declaration.name = "main" then
        .function { declaration with body :=
          (.seq (nestedSeq initializers) declaration.body) } :: declarations
      else
        .function declaration :: pipelinePrependInitializers initializers declarations
  | declaration :: declarations =>
      declaration :: pipelinePrependInitializers initializers declarations

/-! `pan_to_target` makes the entry-point convention explicit: a user-written
    `main` is moved to the front of the declaration list, while a program with
    no `main` receives a generated function returning zero.  Keep this
    preparation separate from `compileFlapjack`, whose lower-level form is
    also useful for pass-local fixtures that intentionally omit `main`. -/
def pipelineGeneratedMain [OfNat α 0] : Decl α :=
  .function
    { name := "main"
      inline := false
      exported := false
      params := []
      body := .return (.const 0)
      returnShape := .one }

def pipelineEnsureMainAux [OfNat α 0] (seen : List (Decl α)) :
    List (Decl α) → List (Decl α)
  | [] => pipelineGeneratedMain :: seen.reverse
  | .function declaration :: declarations =>
      if declaration.name = "main" then
        .function declaration :: seen.reverse ++ declarations
      else
        pipelineEnsureMainAux (.function declaration :: seen) declarations
  | declaration :: declarations =>
      pipelineEnsureMainAux (declaration :: seen) declarations
termination_by declarations => sizeOf declarations

def pipelineEnsureMain [OfNat α 0] (declarations : List (Decl α)) : List (Decl α) :=
  pipelineEnsureMainAux [] declarations

def pipelineRiscVFunctions [NeZero width]
    (functions : List (Nat × List Nat × WordProg (RiscV.Word width))) :
    List (Nat × List Nat × Option (List (RiscV.Instruction width) × List (Fin 32))) :=
  functions.map (fun (label, parameters, body) =>
    (label, parameters, RiscV.wordFunctionToRiscVWithLoops body))

def pipelineRiscVFunctionsWithFfi [NeZero width]
    (services : List (FunName × Nat))
    (functions : List (Nat × List Nat × WordProg (RiscV.Word width))) :
    List (Nat × List Nat × Option (List (RiscV.Instruction width) × List (Fin 32))) :=
  let targets := match RiscV.wordFunctionTargetSignaturesWithCalls functions with
    | some targets => targets
    | none => []
  let context : RiscV.WordCallFfiContext width :=
    { targets := targets, services := services }
  functions.map (fun (label, parameters, body) =>
    (label, parameters,
      RiscV.wordFunctionToRiscVWithCallsAndFfiAndLoops context body))

structure FlapjackPipelineResult (α : Type u) where
  simplified : List (Decl α)
  structured : List (Decl α)
  globals : GlobalCompiledProgram α
  crepe : List (CompiledFunction α)
  loop : List (Nat × List Nat × LoopProg α)
  word : List (Nat × List Nat × WordProg α)

def compileFlapjack [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  let simplified := panSimpDecls declarations
  let structured := structCompileTop simplified
  let globals := globalCompileTop bytesInWord fromNat structured
  let crepeContext := pipelineCrepeContext bytesInWord fromNat globals
  let declarations := pipelinePrependInitializers globals.initializers globals.declarations
  let crepe := compileToCrepe crepeContext declarations
  let loop := pipelineLoopFunctions architecture 1 crepe
  let word := pipelineWordFunctions loop
  { simplified := simplified
    structured := structured
    globals := globals
    crepe := crepe
    loop := loop
    word := word }

def compileFlapjackTarget [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  compileFlapjack architecture bytesInWord fromNat (pipelineEnsureMain declarations)

def compileFlapjackRiscVViaStack [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsToStack pipeline.word
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! End-to-end RISC-V entry point using the executable Word allocator before
    the Word-to-Stack and StackRemove boundaries.  This is deliberately a
    separate API because the historical entry point above is useful for
    register-coloured fixtures that do not exercise allocation failure. -/
def compileFlapjackRiscVViaAllocatedStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpills pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! Bitmap-carrying variant of the allocator-aware RISC-V entry point.  The
    returned bitmap table is part of the artifact because the later runtime
    initialization pass must place it in the bitmap buffer before execution. -/
def compileFlapjackRiscVViaAllocatedStackWithBitmaps [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
      (RiscV.wordStackInitialBitmaps false) pipeline.loop
  let instructions ←
    RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
      removeConfig 0 0
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

/-! End-to-end entry point using the graph-coloured allocator.  This keeps the
graph allocator selectable while its complete CakeML spill metadata is still
being filled in. -/
def compileFlapjackRiscVViaGraphAllocatedStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraph pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! Linked graph-allocator artifact.  Keep the section labels and byte entry
    addresses produced by LabLang so callers can choose an exported function
    and establish the machine-state relation at its actual entry point. -/
def compileFlapjackRiscVViaGraphAllocatedStackLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraph pipeline.loop
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 0 (functions.map (fun (label, _, body) => (label, body)))

/-! Linked form of the allocator-aware entry point.  The flat instruction
    stream remains available above; this form additionally records each
    function's byte entry address so an execution harness can select an
    exported function and install its generated sections in memory. -/
def compileFlapjackRiscVViaAllocatedStackLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpills pipeline.loop
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 0 (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackChecked [BEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    StaticResult (FlapjackPipelineResult α) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjack architecture bytesInWord fromNat declarations))

structure FlapjackRiscVResult (width : Nat) [NeZero width] where
  pipeline : FlapjackPipelineResult (RiscV.Word width)
  functions : List (Nat × List Nat ×
    Option (List (RiscV.Instruction width) × List (Fin 32)))
  linkedFunctions : Option (List (Nat × RiscV.Word width × List Nat ×
    List (RiscV.Instruction width) × List (Fin 32)))
  callLinkedFunctions : Option (List (Nat × RiscV.Word width × List Nat ×
    List (RiscV.Instruction width) × List (Fin 32)))

def compileFlapjackRiscV [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctions pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctions 0 pipeline.word }

def compileFlapjackRiscVTarget [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctions pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctions 0 pipeline.word }

def compileFlapjackRiscVWithFfi [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctionsWithFfi services pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctionsWithFfi 0 services pipeline.word }

def compileFlapjackRiscVTargetWithFfi [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctionsWithFfi services pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctionsWithFfi 0 services pipeline.word }

def compileFlapjackRiscVChecked [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) :
    StaticResult (FlapjackRiscVResult width) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjackRiscV architecture bytesInWord fromNat declarations))

theorem compileFlapjack_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    (architecture : RiscV.Architecture) (bytesInWord : α) (fromNat : Nat → α) :
    (compileFlapjack architecture bytesInWord fromNat []).simplified = [] := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, 
    pipelineLoopFunctions, pipelineWordFunctions, pipelinePrependInitializers]

end Flapjack
