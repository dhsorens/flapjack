# Flapjack

Flapjack is beginning as a Lean 4 port of the formally verified Pancake
compiler. It is an early-stage project: the current Lean code covers the
front-end syntax and declaration-level checking foundations, the first Pancake-to-Crepe and
Crepe-to-Loop compiler slices, executable semantic fragments, and an initial
RISC-V model. The CakeML HOL development is included as the `cakeml`
submodule; its Pancake sources are in [`cakeml/pancake`](cakeml/pancake).

The Lean library currently contains the core Pancake syntax in
[`Flapjack/Language.lean`](Flapjack/Language.lean) and the static-checker
data/context layer plus shape-aware core expression and structured-program
checkers in [`Flapjack/Static.lean`](Flapjack/Static.lean), as well as
the Crepe IR and expression lowerer in [`Flapjack/Crepe.lean`](Flapjack/Crepe.lean)
and [`Flapjack/PanToCrep.lean`](Flapjack/PanToCrep.lean).
The first HOL `pan_simp` normalization pass is in
[`Flapjack/PanSimp.lean`](Flapjack/PanSimp.lean); the HOL notice for the
front-end port is in [`Flapjack/COPYRIGHT`](Flapjack/COPYRIGHT).
Named-structure elimination is in
[`Flapjack/PanStructs.lean`](Flapjack/PanStructs.lean).
The global heap-rewriting core is in
[`Flapjack/PanGlobals.lean`](Flapjack/PanGlobals.lean).
The composed pass pipeline is in
[`Flapjack/Pipeline.lean`](Flapjack/Pipeline.lean).
It exposes both the lower-level pass pipeline and an explicit
`compileFlapjackTarget` boundary matching CakeML's target convention: a user
`main` is placed first, or a zero-returning `main` is generated when absent;
the corresponding RISC-V entry points are `compileFlapjackRiscVTarget` and
`compileFlapjackRiscVTargetWithFfi`.

The target-entry call regression in `Flapjack.Test.CorrectnessTarget` checks a
reordered `main` plus callee through source evaluation, the call-aware Word
evaluator, and the linked RISC-V execution harness.
Core structured statement lowering and top-level function assembly are in
[`Flapjack/Compile.lean`](Flapjack/Compile.lean).
The first executable local/memory semantics and preservation lemmas are in
[`Flapjack/Semantics.lean`](Flapjack/Semantics.lean).
The Loop intermediate language and Crepe-to-Loop compiler are in
[`Flapjack/Loop.lean`](Flapjack/Loop.lean) and
[`Flapjack/CrepToLoop.lean`](Flapjack/CrepToLoop.lean). The compiler now
threads fresh temporaries through expression lowering and handles the main
memory, control-flow, call, exception, return, shared-memory, and FFI
equations; the earlier structural helper remains available for comparison.
The first Loop data-flow analyses are in
[`Flapjack/LoopAnalysis.lean`](Flapjack/LoopAnalysis.lean).
The first fuel-bounded Loop evaluator and its control-result semantics,
including a call-aware recursive function-table bridge, are in
[`Flapjack/LoopSemantics.lean`](Flapjack/LoopSemantics.lean).
That module also exposes an explicit host-handler boundary for FFI effects.
Its executable arithmetic fragment includes word division and the RISC-V
LongMul lowering; long division and the remaining target-specific arithmetic
cases are still staged separately.
The Loop semantics additionally provides a unified call-and-FFI evaluator so
callee bodies and caller continuations can cross both explicit environments.
The initial Word IR and Loop-to-Word lowering are in
[`Flapjack/Word.lean`](Flapjack/Word.lean); its backend subdirectory carries
the HOL notice at [`Flapjack/Word/COPYRIGHT`](Flapjack/Word/COPYRIGHT).
The initial RISC-V target vocabulary, register/memory primitives, and
`ADD`/`ADDI` transition slice are in [`Flapjack/RiscV/Model.lean`](Flapjack/RiscV/Model.lean).
The model also includes HOL-aligned unsigned `DIVU`/`REMU` transitions,
including the architectural divide-by-zero results; Word division selects
`DIVU` in the current target slice.
The model and selector also cover the immediate bitwise forms `ANDI`, `ORI`,
and `XORI`, as well as subtraction by an immediate via `ADDI`; immediate
`SLLI`, `SRLI`, and `SRAI` shifts are also modeled and selected.
HOL’s multi-instruction rotate-right lowering is also selected for immediate
and register shift counts, using `x31` as a reserved scratch register and
rejecting source/destination aliases with that register.
The Word evaluator now implements immediate ROR and the backend proves that
the emitted immediate sequence agrees with that evaluator at the destination
register, including the target’s masked shift-count normalization.
Nonzero immediate conditional operands use the corresponding HOL `ORI` or
`ANDI` scratch materialization; conditions that would clobber `x31` are
rejected in this partial target boundary.
The Word arithmetic selector also includes the HOL two-instruction `LongMul`
lowering (`MULHU` followed by `MUL`) and the six-instruction `AddCarry`
lowering. `WordProg.shareInst` with a register-valued address, or a supported
register-plus-constant address expression, now lowers the six HOL memory
operators to the corresponding RISC-V load/store instruction; the same cases
are available in the executable evaluator and call-aware function selector.
The first Word-to-RISC-V selector, PC-aware code runner, and soundness lemmas
for the supported straight-line and register/zero-conditional fragments are
in [`Flapjack/RiscV/Backend.lean`](Flapjack/RiscV/Backend.lean). Equality,
signed ordering, and unsigned ordering branches are modeled; the remaining
bit-test conditions use the condition register as a dead temporary, and the
Loop-to-Word ticks use an `ADDI x0,x0,0` no-op, and the remaining Word
instructions are still explicitly partial. The memory selector now includes
HOL-aligned unsigned halfword `LHU`/`SH` operations alongside byte, 32-bit,
and full-word operations. Function-level conditionals with
matching branch return layouts now cross this artifact boundary. The HOL notice is in
[`Flapjack/RiscV/COPYRIGHT`](Flapjack/RiscV/COPYRIGHT).
The selector’s function artifact records both emitted instructions and return
registers for the supported straight-line fragment. `executeFunction` in the
backend initializes parameter registers and collects return registers; the
pipeline exposes an end-to-end Pancake-to-artifact wrapper for that fragment.
Normalized ordinary `WordProg.store` operations use the same register or
register-plus-constant address materialization as `shareInst`; global
`TopAddr`/pseudo-store resolution remains a later target-configuration step.
The first library-level source-to-RISC-V correctness theorem for this composed
pipeline is in [`Flapjack/Correctness.lean`](Flapjack/Correctness.lean).
The RISC-V flat source adapter in
[`Flapjack/RiscV/PanMemory.lean`](Flapjack/RiscV/PanMemory.lean) also exposes
a fuel-bounded structured evaluator for loops, calls, exceptions, primitive
dispatch, FFI, and byte-addressed memory; its source-to-target simulation
theorem remains a later milestone.
The bounded StackLang frame boundary is in
[`Flapjack/StackAlloc/FrameMachine.lean`](Flapjack/StackAlloc/FrameMachine.lean):
it models CakeML's stack-space checks, dynamic aligned accesses, and bitmap
loads, and executes the generated Simple collector on a bounded zero-heap
state. The general collector machine simulation theorem remains open.
Its immediate-pointer case is now related by theorem to the pure Nat
`stackGcNatMove` specification; the one-word non-forwarded copy case is also
proved, while forwarding and arbitrary-length copying still require the
corresponding machine-state invariants.
The frame state also carries explicit main/shared memory domains, with
out-of-domain access rejected at the evaluator boundary.
Its RISC-V memory instructions expose little-endian byte, halfword, and
32-bit adapter equations and reject unaligned accesses.
The bounded machine also has the zero-word collector memcpy base-case
equation, preserving the complete frame state.
Reusable sequence and conditional equations expose the evaluator’s
fuel-consuming composition rules for later collector simulation proofs.
The named memcpy body now has an exact state-transition theorem, and its
one-word loop case composes that theorem with the bounded loop evaluator.
The collector address/header prefix, copy preparation, and copy finalization
are named machine transitions; their composition now proves the complete
one-word non-forwarded copy branch at the bounded machine-state boundary.
The forwarding suffix is likewise factored and its full branch composition is
proved, including the unchanged memory and threaded frame components.
The pure Nat collector specification also exposes copy-case equations for
the copied value, next destination address, forwarding-header write, and
success condition.
That module now also contains the first compositional Loop-to-Word agreements:
constant and register-register ADD assignments are related at the destination
local/register observation, under the explicit architectural x0 invariant.
It also checks a complete constant multiplication through the composed RV64
pipeline against the source evaluator; this exercises the context-aware
register mapping for the HOL `LongMul` operation.
The correctness module separately proves the corresponding generic
Loop-to-Word destination-register agreement.
Word-level function-table call semantics are in
[`Flapjack/WordSemantics.lean`](Flapjack/WordSemantics.lean).
The Word call carrier now follows CakeML's exact return cut-set, embedded
return-program, and handler-label shape, and FFI carries its paired cut sets.
That module also exposes a fuel-bounded Word FFI evaluator whose host handler
is explicit in the semantic interface; complete recursive handler lowering and
the final target FFI proof remain staged.
It also exposes a control-result evaluator for handler-aware calls, making the
normal, returned, and raised paths explicit and testing exception-handler
resumption independently of target calling-convention lowering.
The initial explicit RISC-V call convention is in
[`Flapjack/RiscV/Calls.lean`](Flapjack/RiscV/Calls.lean); function-label
linking and label resolution are in
[`Flapjack/RiscV/Link.lean`](Flapjack/RiscV/Link.lean).
The linker now performs a provisional signature/layout pass followed by a
label-resolving code-generation pass for handler-free Word calls. Ordinary
calls save and restore the `x1` link register through reserved
downward-growing stack pointer `x30`, while calls without result destinations
use a true tail call; the tests execute a linked multi-function image through
`JALR`.
The composed pipeline now exposes its linked function table on
`FlapjackRiscVResult.linkedFunctions` and its call-aware table on
`FlapjackRiscVResult.callLinkedFunctions`.

The first library-level source-to-RISC-V correctness theorems are in
[`Flapjack/Correctness.lean`](Flapjack/Correctness.lean). They include
concrete RV64 addition, multiplication, and a declaration-call regression
that checks the Word call semantics against execution of the linked image.

Build it with:

```sh
lake build
```

The staged port is documented in [`PLAN.md`](PLAN.md).
