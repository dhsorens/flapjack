import Flapjack.Stack

/-!
# StackLang allocation insertion

This module ports the structural part of CakeML's `stack_alloc` pass.  The
pass replaces heap `Alloc` and stub-backed `StoreConsts` operations with calls
to runtime labels and recursively transforms all structured children,
including return continuations and exception handlers.

The generated call carries CakeML's `(Skip, 0, n, m)` return metadata.  The
full copying collector body is intentionally kept behind the explicit
`stackAllocStub` boundary for the next increment; this module therefore makes
the runtime dependency visible instead of silently dropping heap allocation.
-/

namespace Flapjack

structure StackAllocConfig where
  gcStubLocation : Nat := 0
  returnLabel : Nat := 0
  firstFreshLabel : Nat := 2
  deriving Repr

def stackAllocRuntimeCall (config : StackAllocConfig) (nextLabel : Nat)
    (target : Nat) : StackProg α :=
  .call (some (.skip, 0, config.returnLabel, nextLabel)) (.label target) none

def stackAllocProgDepth : StackProg α → Nat
  | .call returnHandler _ handler =>
      1 + max
        (match returnHandler with
        | none => 0
        | some (program, _, _, _) => stackAllocProgDepth program)
        (match handler with
        | none => 0
        | some (program, _, _) => stackAllocProgDepth program)
  | .seq first second => 1 + max (stackAllocProgDepth first) (stackAllocProgDepth second)
  | .ite _ _ _ thenBranch elseBranch =>
      1 + max (stackAllocProgDepth thenBranch) (stackAllocProgDepth elseBranch)
  | .loop body => 1 + stackAllocProgDepth body
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def stackAllocCompFuel : Nat → StackAllocConfig → Nat → StackProg α →
    StackProg α × Nat
  | 0, _, nextLabel, program => (program, nextLabel)
  | fuel + 1, config, nextLabel, .seq first second =>
      let (first, nextLabel) := stackAllocCompFuel fuel config nextLabel first
      let (second, nextLabel) := stackAllocCompFuel fuel config nextLabel second
      (.seq first second, nextLabel)
  | fuel + 1, config, nextLabel, .ite operator condition right thenBranch elseBranch =>
      let (thenBranch, nextLabel) :=
        stackAllocCompFuel fuel config nextLabel thenBranch
      let (elseBranch, nextLabel) :=
        stackAllocCompFuel fuel config nextLabel elseBranch
      (.ite operator condition right thenBranch elseBranch, nextLabel)
  | fuel + 1, config, nextLabel, .loop body =>
      let (body, nextLabel) := stackAllocCompFuel fuel config nextLabel body
      (.loop body, nextLabel)
  | fuel + 1, config, nextLabel,
      .call returnHandler target handler =>
      let (returnHandler, nextLabel) := match returnHandler with
        | none => (none, nextLabel)
        | some (program, link, returnLabel, entryLabel) =>
            let (program, nextLabel) :=
              stackAllocCompFuel fuel config nextLabel program
            (some (program, link, returnLabel, entryLabel), nextLabel)
      let (handler, nextLabel) := match handler with
        | none => (none, nextLabel)
        | some (program, exceptionLabel, handlerLabel) =>
            let (program, nextLabel) :=
              stackAllocCompFuel fuel config nextLabel program
            (some (program, exceptionLabel, handlerLabel), nextLabel)
      (.call returnHandler target handler, nextLabel)
  | fuel + 1, config, nextLabel, .alloc _ =>
      (stackAllocRuntimeCall config nextLabel config.gcStubLocation, nextLabel + 1)
  | fuel + 1, config, nextLabel, .storeConsts source bitmap stub =>
      match stub with
      | none => (.storeConsts source bitmap none, nextLabel)
      | some target =>
          (stackAllocRuntimeCall config nextLabel target, nextLabel + 1)
  | _, _, nextLabel, program => (program, nextLabel)

/-! CakeML's `next_lab` reserves labels already embedded in return and
    exception continuations before the allocation pass starts generating
    labels.  The argument order follows the HOL definition: the second
    sequence child is visited first so that labels in the first child are
    allocated above the complete suffix. -/
def stackAllocNextLab : StackProg α → Nat → Nat
  | .seq first second, nextLabel =>
      stackAllocNextLab first (stackAllocNextLab second nextLabel)
  | .ite _ _ _ thenBranch elseBranch, nextLabel =>
      stackAllocNextLab thenBranch (stackAllocNextLab elseBranch nextLabel)
  | .loop body, nextLabel => stackAllocNextLab body nextLabel
  | .call none _ none, nextLabel => nextLabel
  | .call none _ (some (_, _, handlerLabel)), nextLabel =>
      max nextLabel (handlerLabel + 2)
  | .call (some (program, _, _, entryLabel)) _ none, nextLabel =>
      stackAllocNextLab program (max nextLabel (entryLabel + 2))
  | .call (some (program, _, _, entryLabel)) _ (some (handler, _, handlerLabel)),
      nextLabel =>
      stackAllocNextLab program
        (stackAllocNextLab handler (max (max entryLabel handlerLabel + 2) nextLabel))
  | _, nextLabel => nextLabel
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! The exact structural compiler from `stack_allocScript.sml`.  In
    particular, the return continuation is compiled before the exception
    continuation, and a call with no return continuation cannot enter an
    exception handler in CakeML's representation. -/
def stackAllocComp (config : StackAllocConfig) (nextLabel : Nat) :
    StackProg α → StackProg α × Nat
  | .seq first second =>
      let (first, nextLabel) := stackAllocComp config nextLabel first
      let (second, nextLabel) := stackAllocComp config nextLabel second
      (.seq first second, nextLabel)
  | .ite operator condition right thenBranch elseBranch =>
      let (thenBranch, nextLabel) := stackAllocComp config nextLabel thenBranch
      let (elseBranch, nextLabel) := stackAllocComp config nextLabel elseBranch
      (.ite operator condition right thenBranch elseBranch, nextLabel)
  | .loop body =>
      let (body, nextLabel) := stackAllocComp config nextLabel body
      (.loop body, nextLabel)
  | .call none target _ =>
      (.call none target none, nextLabel)
  | .call (some (program, link, returnLabel, entryLabel)) target none =>
      let (program, nextLabel) := stackAllocComp config nextLabel program
      (.call (some (program, link, returnLabel, entryLabel)) target none, nextLabel)
  | .call (some (program, link, returnLabel, entryLabel)) target
      (some (handler, exceptionLabel, handlerLabel)) =>
      let (program, nextLabel) := stackAllocComp config nextLabel program
      let (handler, nextLabel) := stackAllocComp config nextLabel handler
      (.call (some (program, link, returnLabel, entryLabel)) target
        (some (handler, exceptionLabel, handlerLabel)), nextLabel)
  | .alloc _ =>
      (stackAllocRuntimeCall config nextLabel config.gcStubLocation, nextLabel + 1)
  | .storeConsts source bitmap stub =>
      match stub with
      | none => (.storeConsts source bitmap none, nextLabel)
      | some target =>
          (stackAllocRuntimeCall config nextLabel target, nextLabel + 1)
  | program => (program, nextLabel)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def stackAllocWithNext (config : StackAllocConfig) (program : StackProg α) :
    StackProg α × Nat :=
  stackAllocComp config (stackAllocNextLab program config.firstFreshLabel) program

def stackAlloc (config : StackAllocConfig) (program : StackProg α) : StackProg α :=
  (stackAllocWithNext config program).1

/- The complete CakeML pass emits a collector implementation at this label.
   Until that collector is ported, the stub remains an explicit runtime
   boundary and is not mistaken for an executable collector. -/
def stackAllocStub (_config : StackAllocConfig) : StackProg α :=
  .return 0

def stackAllocStubs (config : StackAllocConfig) : List (Nat × StackProg α) :=
  [(config.gcStubLocation, stackAllocStub config)]

/-! Section-level form corresponding to CakeML's `prog_comp` and `compile`.
    The initial label seed is two in the reference compiler; the public
    single-program wrapper above retains its configurable seed for focused
    tests and clients that already own a label namespace. -/
def stackAllocProgram (config : StackAllocConfig)
    (program : Nat × StackProg α) : Nat × StackProg α :=
  let (sectionId, program) := program
  let (program, _) :=
    stackAllocComp config (stackAllocNextLab program 2) program
  (sectionId, program)

def stackAllocCompile (config : StackAllocConfig)
    (programs : List (Nat × StackProg α)) : List (Nat × StackProg α) :=
  stackAllocStubs config ++ programs.map (stackAllocProgram config)

theorem stackAllocCompFuel_alloc (config : StackAllocConfig) (nextLabel words : Nat) :
    stackAllocCompFuel 1 config nextLabel (.alloc words : StackProg α) =
      (.call (some (.skip, 0, config.returnLabel, nextLabel))
        (.label config.gcStubLocation) none, nextLabel + 1) := by
  rfl

theorem stackAllocCompFuel_storeConsts (config : StackAllocConfig)
    (nextLabel source bitmap target : Nat) :
    stackAllocCompFuel 1 config nextLabel
        (.storeConsts source bitmap (some target) : StackProg α) =
      (.call (some (.skip, 0, config.returnLabel, nextLabel))
        (.label target) none, nextLabel + 1) := by
  rfl

theorem stackAllocCompFuel_seq_threads_labels (config : StackAllocConfig)
    (nextLabel firstWords secondWords : Nat) :
    (stackAllocCompFuel 2 config nextLabel
      (.seq (.alloc firstWords) (.alloc secondWords) : StackProg α)).2 =
        nextLabel + 2 := by
  rfl

theorem stackAllocComp_alloc (config : StackAllocConfig)
    (nextLabel words : Nat) :
    stackAllocComp config nextLabel (.alloc words : StackProg α) =
      (.call (some (.skip, 0, config.returnLabel, nextLabel))
        (.label config.gcStubLocation) none, nextLabel + 1) := by
  simp [stackAllocComp, stackAllocRuntimeCall]

theorem stackAllocComp_storeConsts (config : StackAllocConfig)
    (nextLabel source bitmap target : Nat) :
    stackAllocComp config nextLabel
        (.storeConsts source bitmap (some target) : StackProg α) =
      (.call (some (.skip, 0, config.returnLabel, nextLabel))
        (.label target) none, nextLabel + 1) := by
  simp [stackAllocComp, stackAllocRuntimeCall]

theorem stackAllocComp_drops_handler_without_return (config : StackAllocConfig)
    (nextLabel target handler exceptionLabel handlerLabel : Nat)
    (body : StackProg α) :
    stackAllocComp config nextLabel
      (.call none (.label target) (some (body, exceptionLabel, handlerLabel))) =
      (.call none (.label target) none, nextLabel) := by
  simp [stackAllocComp]

theorem stackAllocNextLab_reserves_call_labels
    (program handler : StackProg α) (returnLabel entryLabel exceptionLabel handlerLabel nextLabel : Nat) :
    stackAllocNextLab
      (.call (some (program, returnLabel, exceptionLabel, entryLabel)) (.label nextLabel)
        (some (handler, exceptionLabel, handlerLabel)))
      2 =
      stackAllocNextLab program
        (stackAllocNextLab handler (max (max entryLabel handlerLabel + 2) 2)) := by
  simp [stackAllocNextLab]

theorem stackAllocCompile_emits_stub (config : StackAllocConfig)
    (programs : List (Nat × StackProg α)) :
    (stackAllocCompile config programs).head? =
      some (config.gcStubLocation, stackAllocStub config) := by
  simp [stackAllocCompile, stackAllocStubs]

end Flapjack
