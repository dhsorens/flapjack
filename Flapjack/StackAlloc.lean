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

def stackAllocWithNext (config : StackAllocConfig) (program : StackProg α) :
    StackProg α × Nat :=
  stackAllocCompFuel (stackAllocProgDepth program + 1) config
    config.firstFreshLabel program

def stackAlloc (config : StackAllocConfig) (program : StackProg α) : StackProg α :=
  (stackAllocWithNext config program).1

/- The complete CakeML pass emits a collector implementation at this label.
   Until that collector is ported, the stub remains an explicit runtime
   boundary and is not mistaken for an executable collector. -/
def stackAllocStub (_config : StackAllocConfig) : StackProg α :=
  .return 0

def stackAllocStubs (config : StackAllocConfig) : List (Nat × StackProg α) :=
  [(config.gcStubLocation, stackAllocStub config)]

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

end Flapjack
