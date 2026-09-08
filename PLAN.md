# Flapjack: Pancake Lean port plan

## Goal

Build a usable Lean 4 development of Pancake, including its executable
compiler pipeline and compiler-correctness theorems. The CakeML checkout in
`cakeml` is the reference implementation and remains useful for cross-checking
definitions, pass ordering, examples, and proof obligations.

## Principles

- Keep the Lean AST close to CakeML's `panLang`/`crepLang`/`loopLang` syntax so
  translation and theorem statements can be compared directly.
- Preserve polymorphism over machine-word values at the syntax boundary; make
  word width and target configuration explicit in later layers.
- Port executable definitions first, then state invariants and correctness
  proofs for each pass. Every ported layer should have small computation tests
  before its proof interface is expanded.
- Keep the CakeML submodule untouched from the parent project. HOL builds can
  be run in the submodule independently with Holmake.

## Stages

1. **Project and syntax foundation**
   - Initialize Lake and pin the Lean toolchain.
   - Port the core declarations from `cakeml/pancake/panLangScript.sml`.
   - Port structural helpers such as shape size and nested sequencing.
   - Add Lean examples/tests for constructors and helper behavior.

2. **Static data and front-end support**
   - Port shape well-formedness, struct contexts, declarations, and the
     Pancake static-checker result/error types.
   - Port parser-facing syntax only after the AST and diagnostics are stable.
   - Establish executable validation examples corresponding to CakeML's
     `static_checker` examples.

3. **Semantics**
   - Define a deterministic big-step/trace semantics for Pancake, including
     memory, calls, exceptions, loops, and foreign calls.
   - State and prove preservation of well-formedness and basic determinism.

4. **Compiler passes**
   - Port `pan_to_crep`, then the simplification/struct/global passes.
   - Port `crep_to_loop`, loop optimisations, liveness, and `loop_to_word`.
   - For each pass, add a simulation relation and a correctness theorem before
     composing it into the full compiler.

5. **Target and end-to-end correctness**
   - Port the word-level/target interface and one concrete backend first.
   - Use `/home/zksecurity/HOL/examples/l3-machine-code/riscv/model/riscv.sml`
     as the RISC-V architectural reference; copy `/home/zksecurity/HOL/COPYRIGHT`
     into the Lean RISC-V model subdirectory when that port starts.
   - Connect the compiled result to a Lean execution model and prove the
     end-to-end compiler-correctness statement.
   - Add regression programs and differential checks against CakeML/HOL where
     practical.

## Progress

- [x] Initialize Lake with a pinned Lean 4.33.1 toolchain.
- [x] Port the core `panLang` syntax, shape sizing, and nested sequencing.
- [x] Port nested-recursion local/global expression variable-use helpers.
- [x] Port static-checker data types, structural shape validation, and
  declaration-level shape validation.
- [x] Add a shape-aware executable checker for core expressions and
  diagnostics.
- [x] Check scoped tail/handler-free calls and local return destinations,
  including recursive argument-expression shape matching.
- [x] Port the Crepe IR and executable expression lowering used by
  `pan_to_crep`.
- [x] Port core structured statement lowering and initial pass equations.
- [x] Add parameter-slot allocation and top-level function/declaration
  assembly for the Pancake-to-Crepe pass.
- [x] Materialize primitive arguments and multi-word store/exception payloads
  through fresh Crepe locals.
- [x] Begin the RISC-V target-model port with HOL-derived architectural
  vocabulary, parameterized words, register/memory primitives, and alignment
  traps; preserve the HOL copyright notice in `Flapjack/RiscV/COPYRIGHT`.
- [x] Add an option-valued RISC-V execution boundary that enforces the HOL
  halfword, 32-bit, and machine-word memory-alignment checks, while retaining
  the total transition used by the existing backend equations.
- [x] Add an explicit privilege-sensitive ECALL and memory-alignment trap
  classifier, and connect checked execution to that classifier.
- [x] Port the HOL RV64 word-width arithmetic and shift transitions
  (`ADDW`, `SUBW`, `ADDIW`, `MULW`, and W-shifts), including sign-extension
  back to the architectural register width.
- [x] Add executable `ADD`/`ADDI` transitions with PC-advance and
  zero-register preservation theorems.
- [x] Port HOL's signed `LB`/`LH` load value paths alongside the existing
  unsigned byte/halfword operations, with destination-register theorems.
- [x] Port HOL's signed `SLT`/`SLTI` integer comparison value paths and prove
  their destination-register behavior, including x0 handling.
- [x] Port HOL's unsigned immediate `SLTIU` comparison path and prove its
  destination-register behavior, including x0 handling.
- [x] Port HOL's U-type `LUI` and PC-relative `AUIPC` paths, including
  sign-extended 20-bit immediates and destination-register contracts.
- [x] Correct the mixed-sign two's-complement ordering predicate and add
  negative/positive `SLT` and branch regressions.
- [x] Add executable deterministic semantics and preservation theorems for
  the supported constant/return/sequence fragment, including scalar local
  assignment state updates.
- [x] Add local-plus-memory semantics and a store/load preservation theorem
  for the scalar compiler fragment.
- [x] Extend the initial lowering with handler-free calls, local return
  destinations, declaration calls, and mapped exceptions.
- [x] Lower calls with known exception handlers to Crepe continuation metadata
  and compile the handler body.
- [x] Lower foreign calls and shared-memory operations through explicit Crepe
  temporaries and memory-operation mappings.
- [x] Port the Loop intermediate-language vocabulary and begin Crepe-to-Loop
  lowering, with structural expression preservation and explicit unsupported
  cases.
- [x] Port Loop variable-use, assigned-variable, and accumulated-variable
  analyses as executable list-based prerequisites for liveness.
- [x] Port the temporary-threaded Crepe-to-Loop expression and program
  equations for materialized loads, comparisons, memory, control flow,
  calls, exceptions, returns, shared memory, and FFI.
- [x] Add the initial Word IR and Loop-to-Word lowering for register mapping,
  expressions, memory instructions, loops, calls, returns, and FFI.
- [x] Port the HOL `pan_simp` sequence-association and tail-call normalization
  pass, including recursive call-handler traversal.
- [x] Port the core `pan_structs` named-shape, field-reordering, expression,
  statement, and declaration transformations.
- [x] Port the context-sensitive `pan_globals` expression and statement core,
  including heap-relative global loads/stores and adjusted `TopAddr`.
- [x] Add global declaration address collection and explicit initializer
  programs for composing the global pass with later compiler stages.
- [x] Compose the ported front-end, global, Crepe, Loop, and Word passes in an
  executable pipeline that exposes every intermediate artifact.
- [x] Match CakeML `pan_to_target` entry preparation by moving a user `main`
  to the front or synthesizing a zero-returning `main`, with explicit RISC-V
  target wrappers and executable regressions.
- [x] Add a target-entry declaration-call correctness regression that checks
  the reordered linked image, the call-aware Word result, and execution at
  the generated `main` entry against the source call semantics.
- [x] Add an executable call-aware Crepe evaluator and a declaration-call
  source-to-Crepe agreement regression before Loop lowering.
- [x] Add a unified fuel-bounded Crepe control-result evaluator covering
  memory, loops, primitives, declaration-call handlers, and explicit FFI and
  shared-memory handler boundaries.
- [x] Prove the first generic source-to-full-Crepe result agreements for
  compiled skip and constant-return programs.
- [x] Prove source-to-full-Crepe agreement for a compiled binary addition
  expression over constants.
- [x] Extend generic source-to-full-Crepe agreement through a compiled
  constant store/load and its state-memory projection.
- [x] Extend generic source-to-full-Crepe agreement through constant
  conditional control flow.
- [x] Prove the compiled external-call temporary sequence preserves full
  Crepe state for a no-op FFI and agrees with the source FFI boundary.
- [x] Port a fuel-bounded observable Crepe evaluator with CakeML-style code,
  globals, memory domains, clock timeout, calls, handlers, and `FinalFFI`
  propagation, with executable boundary regressions.
- [x] Port CakeML's byte-level FFI oracle/state/result boundary, including
  observable input/output events, length-failure handling, terminal outcomes,
  and the empty external-call identity case.
- [x] Port the Loop-side byte-array FFI boundary for mapped shared memory and
  external calls, including endian-aware decoding, memory-domain checks,
  host-state/event updates, and `FinalFFI` propagation.
- [x] Connect the exact Loop FFI boundary to `LoopProg` address evaluation and
  program dispatch, including CakeML's live-local `cut_state` and reusable
  semantic equations for both FFI constructors.
- [x] Prove the first environment-sensitive source-to-full-Crepe agreement
  for a local assignment followed by a compiled slot return.
- [x] Prove the first environment-sensitive source-to-full-Crepe agreement
  for returning a source local through its compiled slot.
- [x] Add a return-aware RISC-V function artifact and evaluator for the
  straight-line Word assignment/return fragment.
- [x] Add a partial Word-to-RISC-V instruction selector for constants, moves,
  and the register-register ADD/SUB/AND/OR/XOR fragment, with a straight-line
  semantic soundness theorem.
- [x] Make the RISC-V x0 invariant explicit and prove that the instruction
  transition preserves it.
- [x] Connect the composed Word pipeline to a typed, option-valued RISC-V
  function artifact stage for the currently supported straight-line fragment.
- [x] Port byte load/store transitions from the HOL RISC-V model and connect
  the Word load8/store8 operations to them with evaluator agreement.
- [x] Add little-endian 32-bit load/store transitions and connect the Word
  load32/store32 operations to them with evaluator agreement.
- [x] Add full-word register-based store lowering and prove its evaluator
  agreement with the RISC-V byte-memory fold.
- [x] Add declaration-level static checking: structure discovery, global and
  exception environments, function headers, duplicate checks, and missing or
  wrongly shaped returns.
- [x] Extend Pancake/Crepe executable semantics to store32/storeByte and prove
  preservation for constant store-then-load programs.
- [x] Exercise the concrete composed compiler from a Pancake `main` through
  the option-valued RISC-V artifact boundary.
- [x] Integrate static checking into checked compiler entry points that return
  diagnostics instead of compiling malformed declaration lists.
- [x] Extend the RISC-V backend with full-word byte-fold memory operations and
  prove evaluator agreement for register-based Word stores.
- [x] Port equality and inequality branch instructions from the HOL RISC-V
  vocabulary and prove their conditional PC transitions.
- [x] Match HOL `pan_to_crep` for `BytesInWord` and alias-sensitive local
  assignments, including regression tests for both cases.
- [x] Add fuel-bounded conditional and sequencing semantics for Pancake and
  Crepe and prove preservation for a constant conditional program.
- [x] Port the RISC-V low-word multiplication path for HOL `CrepOp.mul` and
  `LoopArith.longMul`, with intermediate and end-to-end tests, and prove the
  emitted `MULHU`/`MUL` pair computes the high and low product words.
- [x] Port RISC-V register shifts (`SLL`, `SRL`, and `SRA`) with masked shift
  amounts, plus the HOL scratch-register lowering for `ROR`.
- [x] Extend Pancake/Crepe executable expression semantics with `PanOp.mul` and
  prove constant multiplication preservation through `pan_to_crep`.
- [x] Add a fuel-bounded Loop state/control-result evaluator for assignments,
  memory, returns, break/continue, conditionals, and loop execution.
- [x] Prove the first Crepe-to-Loop semantic bridge for constant return
  lowering through the generated temporary assignment.
- [x] Extend that bridge through Crepe `mul`/Loop `longMul` expansion and
  preserve the returned product.
- [x] Extend the source-to-Loop bridge through a constant Pancake binary
  addition, including executable RV64 regression coverage.
- [x] Extend the source-to-Loop bridge through constant Pancake multiplication
  and its Crepe-to-Loop `longMul` expansion, with executable RV64 coverage.
- [x] Extend the source-to-Loop bridge through constant equality comparison
  lowering and Loop branch execution, with true and false RV64 regressions.
- [x] Compose constant Pancake conditionals through comparison materialization,
  Loop branching, and selected returns, with true and false RV64 regressions.
- [x] Prove source-to-Loop agreement for a local assignment followed by a
  source-local return, including slot-mapped RV64 execution coverage.
- [x] Prove source-to-Loop agreement for returning an existing local under an
  explicit source/slot state relation, with a bound-local RV64 regression.
- [x] Prove source-to-Loop agreement for a scoped declaration followed by a
  local return, including the compiler's context extension and Loop binding.
- [x] Extend scoped declaration agreement through binary addition before the
  bound local is returned, with an executable RV64 regression.
- [x] Correct Loop declaration binding for temporary-consuming expressions and
  verify scoped multiplication declarations through source-to-Loop execution.
- [x] Prove RISC-V instruction-selection and evaluator agreement for the
  emitted constant-return artifact.
- [x] Lower register-based equality and inequality conditionals to RISC-V,
  including generated branch offsets and a PC-aware code executor.
- [x] Prove concrete taken and fall-through conditional execution paths for
  the generated RISC-V artifact under the fixed-width x0 invariant.
- [x] Prove compositional `executeCode` control-flow correctness for the
  generated conditional layout, including the post-conditional termination PC.
- [x] Connect that control-flow proof to a generated Word conditional with
  branch-selected assignment results and the RV64 x0 invariant.
- [x] Connect immediate-zero Word conditions to RISC-V x0 and test the
  resulting conditional function artifact.
- [x] Port unsigned `Lower`/`NotLower` Word conditions to RISC-V `BLTU`/`BGEU`
  and prove their PC transitions.
- [x] Port signed `Less`/`NotLess` Word conditions to RISC-V `BLT`/`BGE` with
  explicit two's-complement ordering and concrete execution proofs.
- [x] Port `Test`/`NotTest` Word conditions through an `AND`/x0 sequence,
  with an explicit dead-condition-register contract and execution proofs.
- [x] Lower Loop-to-Word `Tick` to an architectural `ADDI x0,x0,0` so
  generated conditional function artifacts can cross the RISC-V boundary.
- [x] Lower function-level conditionals with recursively compiled return
  branches, requiring both branches to expose the same return-register layout.
- [x] Preserve terminal function returns when compiling or evaluating a
  sequence with unreachable trailing code.
- [x] Add the pipeline’s initial register context, mapping Loop slots to
  RISC-V registers from x2 and remapping parameter metadata consistently.
- [x] Add an executable RISC-V function harness that initializes parameter
  registers and collects declared return registers, with an `ADD` proof.
- [x] Add a Word-level FFI evaluator with an explicit host-handler boundary,
  its single-call semantic equation, and a concrete handler regression.
- [x] Generalize the combined Loop-to-Word FFI simulation boundary to any
  positive fuel budget, so it composes with fuel-bounded call-aware proofs.
- [x] Add the normal-path combined sequence simulation rule and exercise an
  FFI followed by a resumed Word tick continuation.
- [x] Add Word control-result semantics for handler-aware calls, including
  normal, returned, and raised paths with handler resumption.
- [x] Add homogeneous BitVec shift instances for the Word semantic bridge.
- [x] Prove the first Loop-to-Word state-observation agreements for constant
  and register-register ADD assignments, with the RISC-V x0 invariant explicit.
- [x] Make the Loop-to-Word register observation context-parametric for
  mapped constant and register-register ADD assignments.
- [x] Prove a generic Loop-to-Word register-observation agreement for
  context-mapped `LongMul`.
- [x] Exercise that harness on an artifact produced by the composed
  Pancake-to-RISC-V pipeline for a two-parameter addition function.
- [x] Connect Word full-word stores to function artifacts and prove a
  store/load function through the RISC-V byte-memory model.
- [x] Port the direct RISC-V `JAL` PC-transfer/link-register transition as
  the machine-model foundation for later function calls.
- [x] Port the direct RISC-V `JALR` register-target transition, including
  link-register behavior and the architectural low-bit clear.
- [x] Add a return-address-aware RISC-V function runner and execute a callee
  returning through `JALR x0, ra, 0`.
- [x] Add the first call-aware Loop semantic bridge: function lookup,
  argument binding, return assignment, tail-call propagation, and handler
  entry for top-level calls.
- [x] Extend call-aware Loop evaluation through nested and recursive function
  bodies with fuel decreasing across the call graph.
- [x] Thread call-aware evaluation through Loop repetition and break/continue
  handling.
- [x] Add Loop shared-memory load/store semantics for all modeled widths,
  using the executable memory state.
- [x] Add an explicit fuel-bounded Loop FFI environment bridge with evaluated
  word arguments and host-controlled state updates.
- [x] Add a RISC-V ECALL FFI ABI boundary with service-name resolution,
  argument marshalling, option-valued host execution, and executable
  instruction-level regressions.
- [x] Prove that FFI-aware RISC-V selection preserves the ordinary
  call-aware selector on the straight-line Word fragment.
- [x] Extend the FFI selector contract through loop-capable lowering for
  straight-line programs, including an explicit ECALL leaf.
- [x] Compose loop-capable FFI lowering with the one-step ECALL machine
  simulation theorem at the named RISC-V correctness boundary.
- [x] Port the StackLang handler/FFI carriers and initial `word_to_stack`
  call, raise, and foreign-call boundary equations, with a local HOL
  copyright notice and structural regressions.
- [x] Port the core StackLang-to-LabLang flattening pass for calls, handlers,
  loops, exceptions, labels, and FFI, with executable label-counter
  regressions and a local HOL copyright notice.
- [x] Add a concrete LabLang-to-RISC-V resolver for local label positions,
  symbolic jumps, conditional branches, and ECALL service names, with
  explicit failure for unsupported target operations and executable tests.
- [x] Extend LabLang linking across multiple sections with byte-base layout,
  section-qualified labels, and an executable cross-section jump regression.
- [x] Port the core StackLang-to-LabLang flattening pass for calls, handlers,
  loops, exceptions, labels, and FFI, with executable label-counter
  regressions and a local HOL copyright notice.
- [x] Add a unified fuel-bounded Loop evaluator that composes function calls
  and host-controlled FFI effects in one control-result semantics.
- [x] Extend the unified Loop evaluator with an explicit primitive handler, so
  primitives compose with calls, callee FFI, loops, and exception handlers;
  expose named equations for the combined semantic boundary.
- [x] Preserve a static-check success while diagnosing unreachable sequence
  tails after a definite function exit.
- [x] Add a library-level end-to-end correctness theorem for the composed
  RV64 Pancake-to-RISC-V addition pipeline, parameterized over inputs.
- [x] Add a composed RV64 Pancake-to-RISC-V multiplication artifact shape and
  executable correctness theorem, including context-aware LongMul operands.
- [x] Add a fuel-bounded Word function-table evaluator with nested calls,
  return-register assignment, tail calls, and memory-state propagation.
- [x] Add the first RISC-V call-sequence selector and execute its linked
  argument-move, `JALR`, return, and result-move convention.
- [x] Add RISC-V function-artifact linking by byte length and resolve Word
  call labels to linked entry addresses.
- [x] Add recursive Word call instruction selection for handler-free calls,
  using linked callee signatures and the explicit call convention.
- [x] Add a two-pass Word function linker that derives return signatures,
  computes byte-addressed function layout, resolves call labels, and
  re-emits the final linked artifacts.
- [x] Relate the generated linked call artifact to its executable image and
  prove execution of that generated image, rather than only a hand-written
  instruction list.
- [x] Give ordinary linked calls a stack-preserved `x1` link register and
  reserve `x30` as the downward-growing stack pointer; lower no-destination
  calls as true tail calls.
- [x] Expose linked RISC-V function artifacts directly from the composed
  pipeline result.
- [x] Expose the call-aware two-pass linked artifacts alongside the original
  straight-line artifact table, preserving the first correctness theorem.
- [x] Carry cross-section function identities into handler-address lowering,
  and regress the emitted RISC-V setup address for a linked raised call.
- [x] Port complete program checking, context transitions, and diagnostics for
  the current AST, including declaration environments, missing returns,
  unreachable-tail warnings, and location annotations. The diagnostic surface
  remains intentionally smaller than CakeML's rich structured messages.
- [x] Add a fuel-bounded, structurally recursive loop evaluator for the
  currently modeled Loop fragment.
- [x] Extend the Loop evaluator with executable word division and preserve
  the result through a fuel-bounded arithmetic-program regression.
- [x] Port unsigned RISC-V `DIVU`/`REMU`, including their divide-by-zero
  behavior, and select `DIVU` for Word division.
- [x] Add immediate RISC-V bitwise transitions (`ANDI`, `ORI`, `XORI`) and
  select them for normalized Word expressions, with subtract-immediate via
  `ADDI`.
- [x] Add immediate RISC-V shift transitions (`SLLI`, `SRLI`, `SRAI`) and
  select them for normalized Word shift expressions.
- [x] Port the HOL RISC-V rotate-right lowering as a scratch-register
  instruction sequence, including immediate and register-count forms and the
  reserved `x31` alias contract.
- [x] Extend Word-level ROR evaluation and prove immediate ROR compiler
  agreement at the destination-register observation boundary, including
  immediate shift-count normalization.
- [x] Lower nonzero immediate RISC-V conditional operands using HOL-aligned
  `ORI`/`ANDI` scratch materialization, with an explicit `x31` condition guard.
- [x] Thread the immediate-condition and multi-instruction expression
  lowering through the call-aware RISC-V function selector.
- [x] Thread normalized register and offset-addressed memory lowering through
  the call-aware RISC-V function selector.
- [x] Lower Word expression-level full-word loads through the reserved
  address scratch register, with evaluator agreement and pipeline coverage.
- [x] Port the HOL RISC-V `AddCarry` lowering through Word instruction
  selection and execution, including its reserved `x31` scratch contract.
- [x] Keep Loop-to-Word `AddCarry` as a five-register operation until
  instruction selection, and prove a structured primitive through the
  call-linked RISC-V artifact without clobbering the `x1` link register.
- [x] Add an executable Option-valued Word allocator boundary that preserves
  existing low-numbered mappings and rejects reserved-register exhaustion.
- [x] Add an executable undirected clash-edge checker and
  preferred-register-aware greedy colouring boundary for Word variables.
- [x] Add straight-line Word liveness and clash construction feeding the
  executable colouring boundary.
- [x] Add straight-line SSA renaming for Word writes and reads, including
  multi-result arithmetic instructions.
- [x] Extend straight-line Word SSA through memory operations, `locValue`,
  returns, exceptions, FFI arguments, and handler-free call metadata, while
  matching liveness reads and writes to those data-flow conventions.
- [x] Extend Word SSA through handler-bearing calls, recursively renaming the
  handler body, reconciling its normal continuation with the call path, and
  advancing fresh names across both paths; cover the transformation with an
  executable Word control-result regression.
- [x] Feed actual WordProg sequencing into backwards liveness and conservative
  control-flow clash construction.
- [x] Expose a program-analysis-driven Word pipeline allocation boundary for
  straight-line and conservatively analysed control-flow programs.
- [x] Add branch-aware Word SSA version reconciliation and tighten program
  clash analysis to write/live interference for the supported control-flow
  fragment.
- [x] Include recursively analysed exception-handler bodies and handler-entry
  interference edges in Word program clash analysis.
- [x] Add CakeML-aligned loop SSA setup for Word live-in/live-out names, with
  refreshed loop frames and explicit back-edge plus `break`/`continue`
  reconciliation moves.
- [x] Port recursive Word register-colouring over expressions, instructions,
  nested handlers, loops, and call metadata, and expose the coloured pipeline
  boundary.
- [x] Add an explicit spill-aware Word allocation result with fresh stack-slot
  assignment and a register/spill clash-validation contract; stack access
  rewriting remains a separate backend pass.
- [x] Encode the RISC-V forced-clash constraints for multi-result `LongMul`
  and `AddCarry` in both linear and program-level allocation analyses.
- [x] Enforce the currently supported special-instruction layout at the
  spill-aware allocator and Word-to-Stack boundary, rejecting spilled or
  aliased special values before instruction selection; both AddCarry and
  LongMul are normalized through reserved scratch registers when spilled.
- [x] Lower spill-aware `LongMul` through reserved scratch registers, preserve
  the register-resident fast path, and prove the generated StackLang fragment
  on a concrete machine state.
- [x] Lower spill-aware AddCarry through reserved scratch registers, preserve
  the register-resident fast path, and prove both result words on a concrete
  StackLang machine state.
- [x] Prove abstract Stack-machine preservation for lowered Word binary
  operations, including spilled operand materialization and scratch
  non-alias conditions.
- [x] Prove abstract Stack-machine preservation for lowered Word shifts,
  including register-resident and fully spilled operand materialization.
- [x] Expose an SSA-driven spill allocation boundary that derives spill
  locations from the renamed Word program and its analysed clash graph.
- [x] Wire the available SSA/spill allocation, graph-derived concrete locations,
  and graph-backed entry point into the allocated RISC-V path; the full CakeML
  allocator remains separate.
- [x] Prove that call-aware RISC-V selection agrees with the base
  straight-line selector and preserves the Word function result.
- [x] Prove that the loop-capable call-aware selector reduces to the
  call-aware straight-line selector on the straight-line Word fragment.
- [x] Connect the call-aware RISC-V selector to source-level `AddCarry`
  and `LongMul` results through parameterized emitted-code contracts.
- [x] Connect call-aware `DIVU` lowering to the source-level Word division
  result under its nonzero-divisor precondition.
- [x] Connect call-aware return-carrier shapes to the Word evaluator while
  preserving failure when a returned register name is not encodable.
- [x] Port the CakeML-shaped RISC-V Word clash-tree boundary and its backward
  live-set analysis, including `Delta`, sequencing, branch live sets, loop cut
  sets, handler paths, and a tree-driven spill-allocation entry point.
- [x] Port the executable CakeML-style partial-colouring and clash-tree
  acceptance oracle, prove its list-set invariant, and enforce it at the
  preference-aware SSA spill-allocation boundary.
- [x] Port the CakeML graph allocator data model for RISC-V: Fixed/Atemp/Stemp
  tags, source-to-node bijections, and clash-tree clique graph construction;
  the worklist colouring operations remain part of the full allocator item.
- [x] Port the executable two-pass Atemp/Stemp colouring transition, including
  available-colour removal, stack-range colour selection, and edge-safety
  regressions.
- [x] Add the first IRC-style graph worklist state: degree tracking,
  low-degree simplification, forced spill selection, and reverse-stack
  colouring with executable edge-safety regressions.
- [x] Port move consistency filtering, canonical move orientation,
  coalesced-node parent compression, and a conservative safe coalescing step.
- [x] Port repeated safe coalescing with parent resolution and rebuilt pending
  move worklists.
- [x] Bridge graph colours back to source variables with CakeML total-colour
  doubling and validate the graph allocation through the clash-tree oracle.
- [x] Derive forced clashes from Word special instructions and expose a
  checked graph allocator that rewrites complete Word programs.
- [x] Separate CakeML’s initial fixed-colour budget check from later move
  consistency checks and enforce it at graph allocator initialization.
- [x] Port CakeML’s exact George/Briggs coalescing threshold and route safe
  move selection through the source-faithful criterion.
- [x] Preserve CakeML move priorities by sorting available and unavailable
  move worklists before coalescing.
- [x] Add CakeML-shaped freeze candidates and move retirement after failed
  coalescing, with recomputed move-relatedness and executable stack evidence.
- [x] Add a function-level graph-allocation boundary seeded with renamed formal
  parameters, retaining unused ABI formals in the graph and colouring output.
- [x] Port CakeML's backward stack-only/forced-stack analysis for Word moves,
  branches, calls, loops, and terminal clashes, and feed forced sources into
  the graph-function boundary.
- [x] Match CakeML's stride-four SSA fresh-name convention and branch
  reconciliation counter, preserving the physical/allocatable/stack residue
  classes used by the RISC-V graph allocator.
- [x] Carry explicit CakeML-style prioritized Word move programs through SSA
  renaming, clash/preferences, colouring, stack lowering, and RISC-V
  execution, including cycle-safe scheduling with the reserved x29/x31
  temporaries; full allocator integration remains a separate item.
- [x] Prove that colouring preserves the WordLang `break` and `continue`
  control labels through structured programs and call metadata.
- [x] Port CakeML's `extract_labels` contract for return and exception handler
  label pairs, including recursive call metadata and structured subprograms.
- [x] Add a clash-tree-backed Word allocation boundary with explicit success
  witnesses for physical registers, clash safety, and label preservation.
- [x] Expose success contracts for the SSA and function-level spill allocators,
  including parameter coverage, special-location safety, and clash-tree checks.
- [x] Extend the preference-aware SSA success witnesses from formal parameters
  to every renamed program variable.
- [x] Port the CakeML oracle-colouring acceptance boundary for function-level
  Word allocation, checking the clash tree, forced clashes, and stack colours
  before applying total colours.
- [x] Compose oracle acceptance with the SSA, stack-only, forced-clash, and
  graph-colouring fallback at the function-level allocation boundary.
- [x] Expose the spill-aware clash-tree allocator as the final checked fallback
  and preserve its special-location and spill-tree witnesses.
- [x] Port CakeML's five-counter Word heuristic summary and preserve explicit
  move priorities at the graph-allocation boundary.
- [x] Port CakeML spill-cost weighting, move canonicalization, and odd/even
  heuristic worklist selection.
- [x] Wire the heuristic worklist into a function-level stack-aware graph
  allocation entry point.
- [x] Compose oracle, heuristic graph, and checked spill allocation at the
  function boundary.
- [x] Prove fixed-tag, graph-edge, and clash-tree soundness for the prioritized
  heuristic graph allocator.
- [x] Lift prioritized graph soundness through the composed oracle/heuristic
  function driver.
- [x] Thread heuristic allocation through the RISC-V Word-to-Stack pipeline
  and expose an end-to-end StackRemove entry point.
- [x] Port CakeML's linear-scan live-tree representation, backward liveness,
  register extraction, and executable colouring check.
- [x] Port CakeML's linear-scan interval start/end construction, including
  earliest-start/latest-end updates and interval intersection.
- [x] Port the executable linear-scan active-set state machine, including
  colour reuse, physical-register reservations, stealing, and spill slots.
- [x] Connect linear-scan intervals, forced colours, and move preferences to a
  program-level clash-tree allocation entry point.
- [x] Add an executable linear-scan acceptance boundary requiring complete
  locations, live-tree safety, and forced-clash separation.
- [x] Integrate checked linear-scan allocation at the SSA function and RISC-V
  Word-to-Stack/StackRemove pipeline boundaries.
- [x] Port CakeML numeric allocation-mode decoding and dispatch modes 4+ to
  the checked linear-scan RISC-V pipeline.
- [x] Thread formal-entry moves through the linear-scan function allocator and
  pipeline, with safety and parameter-location contracts.
- [x] Prove the checked linear-scan safety predicate and lift it through the
  SSA-renamed function allocation boundary.
- [x] Expose linear-scan location coverage for every renamed formal parameter
  at the function allocator boundary.
- [x] Port linear-scan domination repair and the executable number-property,
  start-live, point-inside-interval, and interval-colouring checks.
- [x] Port linear-scan source-variable normalization, clash-tree traversal,
  and forced-clash/move remapping.
- [x] Expose CakeML-shaped linear-scan pass-one/pass-two states, adjacency
  filtering, stack extraction, and the two-pass runner.
- [x] Port source-faithful interval-order register sorting and move-priority
  sorting before the linear-scan passes.
- [x] Compose source normalization, interval preprocessing, two-pass allocation,
  and inverse-colour extraction into a witness-carrying allocator result.
- [x] Port CakeML's clash-tree interval pass with boundary live-set closure,
  including `Delta`, `Set`, branch cut sets, and sequencing.
- [x] Port the source register-colour exchange between linear-scan passes and
  apply it to the low/high physical-register partitions.
- [x] Prove the executable register-colouring correspondence for straight-line
  Word programs built from variable assignments and sequencing.
- [x] Extend the executable colouring simulation to constant assignments and
  immediate register materialization.
- [x] Extend the executable colouring simulation to binary variable expressions
  and arithmetic/bitwise RISC-V operations.
- [x] Extend the executable colouring simulation to variable-plus-constant
  binary expressions and immediate RISC-V operations.
- [x] Extend the executable colouring simulation to variable shifts and their
  SLL/SRL/SRA lowering.
- [x] Extend the executable colouring simulation to immediate shifts and their
  SLLI/SRLI/SRAI lowering.
- [x] Add coloring simulation for a non-cyclic singleton parallel move,
  including the reserved-x31 side condition at both colored endpoints.
- [x] Integrate the singleton move case into the reusable straight-line
  coloring simulation induction under an explicit no-x31 coloring invariant.
- [x] Prove two-entry non-cyclic parallel-move coloring simulation by composing
  singleton move correspondence with the executable instruction-sequence
  evaluator.
- [x] Integrate the two-entry move case into the reusable straight-line
  coloring simulation induction, with an entry-shaped regression.
- [x] Prove source-ordered lowering for arbitrary acyclic parallel-move lists,
  covering the fresh full-SSA formal-entry case without scratch-register use.
- [x] Prove the RISC-V execution of an arbitrary acyclic move list writes each
  destination from its original source value.
- [x] Compose acyclic move-list lowering with the register-state relation,
  proving semantic coloring simulation for arbitrary fresh full-SSA entries.
- [x] Compose arbitrary acyclic full-SSA entry moves with a straight-line
  colored Word body, retaining the state relation across the entry boundary.
- [x] Expose the clash-tree allocator's coloured-program result as a semantic
  straight-line simulation contract at the Word allocator boundary.
- [x] Connect the executable graph allocator output to the reusable straight-line
  colouring simulation contract.
- [x] Lift the graph-colouring simulation contract to the SSA-renamed function
  allocator boundary.
- [x] Lift graph-colouring simulation through the full-SSA formal-entry move
  prefix.
- [x] Prove register-coloured condition preservation and conditional-branch
  simulation for executable Word `ite` programs.
- [x] Relate straight-line handler-aware Word evaluation to the executable
  state-only evaluator, preserving an explicit empty return carrier.
- [x] Lift straight-line colouring simulation to handler-aware Word evaluation,
  including preservation of the empty return carrier.
- [x] Match CakeML Simple/IRC distinction in graph allocation modes: modes
  0--1 omit move preferences during coalescing but retain the original move table for coloring, while modes 2--3 use the prioritized list for coalescing and the original move table for coloring.
- [x] Preserve SSA-renamed virtual names at the heuristic allocator's
  location-aware StackLang boundary; color only the register-semantic result.
- [x] Prove the reserved-x31 five-instruction rotate-right colouring boundary
  under explicit scratch non-aliasing hypotheses.
- [ ] Port CakeML's full SSA/clash-colouring Word allocator and its spill-aware
  RISC-V contracts before claiming general call-aware allocation correctness.
- [x] Package the entry-inclusive spill allocator's clash, special-location,
  tree, variable-coverage, and ABI-parameter witnesses for downstream lowering.
- [x] Thread coalescing and freeze stack entries into the subsequent Atemp/Stemp
  coloring phase, preserving CakeML's push_stack order.
- [x] Initialize residual coloring over the active subgraph after prior stack
  removals, so stacked-node degrees do not affect later spill selection.
- [x] Run the initial low-degree simplification phase before coalescing and
  retire moves touching nodes already placed on the allocator stack.
- [x] Port and test CakeML do_prefreeze cleanup: retire invalid unavailable
  moves and simplify newly non-move-related low-degree nodes before freezing.
- [x] Wire the prefreeze worklist phase into both graph-backed Word-to-Stack
  pipelines while retaining the original allocator API for existing proofs.
- [x] Port unavailable-move revival after coalescing, including priority sorting
  and freeze-worklist refresh, with a focused regression.
- [x] Make register-side unspill explicit: lower-degree spill candidates move
  to the simplify worklist when graph nodes are removed.
- [x] Port move-state spill worklists and respill cleanup after coalescing and
  freezing, with explicit regressions for both transitions.
- [x] Thread active-node sets and dynamic degrees through move coalescing and
  freezing, matching CakeML case1/case2 degree updates.
- [x] Add the spill step loop: choose the highest-degree spill candidate, update
  neighboring degrees, and recurse through unspill/freeze before coloring.
- [x] Expose the ABI-correct full-SSA spill allocator at the location-aware
  Word-to-Stack entry boundary, retaining renamed parameters and allocation slots.
- [x] Route the legacy flat full-SSA spill pipeline through state-threaded
  location-aware lowering, so `Alloc` and `StoreConsts` are supported instead
  of being rejected by the stateless compiler.
- [x] Port CakeML odd-mode spill-cost candidate selection into the graph
  worklist, preserving checked allocation soundness.
- [x] Port CakeML no-cost highest-degree spill candidate selection into the
  graph worklist, preserving checked allocation soundness.
- [x] Remap source-keyed CakeML heuristic moves through the graph-node
  bijection before coalescing, coloring, and spill-aware allocation.
- [x] Port CakeML get_stack_only exactly for Word Move, branch, loop, and
  handler-aware call cases, with clash-tree fallback for ordinary instructions.
- [x] Preserve Atemp candidates through spill-worklist selection and defer
  Stemp conversion until the register-coloring phase exhausts ABI colors.
- [x] Apply sorted CakeML move preferences during Atemp and Stemp graph
  coloring, with the existing safe fallback when no preference matches.
- [x] Preserve CakeML allocation order by coloring all Atemps before the
  second Stemp preference pass.
- [x] Thread CakeML-shaped formal-entry moves through the heuristic
  allocation pipeline so its Simple/IRC path consumes full-SSA functions.
- [x] Prove graph-colouring soundness for the full-SSA heuristic allocator,
  including its Simple and prioritized-move branches.
- [x] Route both ordinary and full-SSA heuristic wrappers through the shared
  Simple/IRC spill-cost dispatcher, keeping coalescing and coloring preferences
  separate while reusing its allocation soundness contract.
- [x] Expose the full-SSA oracle/heuristic/spill decision boundary with a
  graph-allocation soundness contract.
- [x] Prove that a successful Word-to-Stack move preserves every unrelated
  spilled or register-backed value under explicit scratch and destination
  non-alias conditions.
- [x] Package unrelated-value preservation as a reusable location-indexed
  Word-to-Stack state relation for subsequent spill-aware instruction proofs.
- [x] Prove binary expression lowering preserves the reusable spill relation,
  including explicit destination, scratch, and address-scratch non-aliasing.
- [x] Prove shift expression lowering preserves the reusable spill relation
  when both operands are spilled and both temporary registers are clobbered.
- [x] Prove load expression lowering preserves the reusable spill relation
  when the address is spilled and the address scratch is materialized.
- [x] Prove store expression lowering preserves every mapped value while
  materializing spilled source and address operands in temporary registers.
- [x] Prove constant assignment lowering preserves unrelated mapped values
  when writing a register or a spilled destination through `scratch`.
- [x] Prove StackStore lookup assignment preserves unrelated mapped values,
  including a spilled destination and an explicit store-name mapping.
- [x] Prove StackStore Set lowering preserves the complete mapped-value
  relation while materializing a spilled source through `scratch`.
- [x] Prove shared-load lowering preserves unrelated mapped values while
  reading through a spilled address from the separate shared-memory state.
- [x] Lift the existing division value theorem with a full location-matrix
  non-interference contract for unrelated spill and register values.
- [x] Prove the direct WordProg `get` lowering preserves unrelated mapped
  values for a spilled destination and explicit StackStore mapping.
- [x] Prove direct WordProg memory load/store lowering preserves the spill
  relation, including separate address and value scratch materialization.
- [x] Prove the public WordProg `set` lowering preserves the complete mapped
  relation while materializing a spilled source.
- [x] Compose public WordProg arithmetic division with the spill relation,
  including its reserved-location safety guard.
- [x] Compose public WordProg memory loads and stores with the spill relations.
- [x] Compose public shared-memory loads with the shared spill relation.
- [x] Prove public shared-memory stores preserve the mapped spill relation.
- [x] Compose public assign and locValue moves with the spill relation.
- [x] Prove fully spilled AddCarry lowering preserves unrelated register and
  stack values.
- [x] Compose public fully spilled AddCarry lowering with its spill relation.
- [x] Prove fully spilled LongMul lowering preserves unrelated values.
- [x] Compose public fully spilled LongMul lowering with its spill relation.
- [x] Prove register-resident LongMul lowering preserves unrelated values.
- [x] Compose public register-resident LongMul lowering with its state relation.
- [x] Prove register-resident AddCarry lowering preserves unrelated values.
- [x] Compose public register-resident AddCarry lowering with its state relation.
- [x] Cover mixed-source LongMul lowering with spilled destinations.
- [x] Compose public mixed-source LongMul lowering with its state relation.
- [x] Prove the linker’s cumulative byte-offset equation for resolved prefixes.
- [x] Expose the ordinary and FFI-aware linked-function artifact shape,
  including the return jump appended by linking.
- [x] Connect a successfully linked head function to its resolved entry lookup.
- [x] Connect linked head lookup to the call-sequence compiler at its entry.
- [x] Add call-aware and FFI-aware lowering for allocator-generated register
  moves.
- [x] Expose soundness of the entry-aware SSA spill allocator, including its
  clash, special-location, and clash-tree checks.
- [x] Expose location coverage for every variable in the entry-aware SSA spill
  allocator's renamed program.
- [x] Compose the oracle, graph, and spill allocator outcomes behind one
  result-level correctness witness for downstream lowering.
- [x] Expose renamed formal-parameter locations through the composed spill
  fallback driver.
- [x] Name the source-level FFI-to-RISC-V machine execution and agreement
  theorem instead of leaving the end-to-end result as an anonymous guard.
- [x] Add a reusable parameterized Word call/return semantic contract for the
  stack-based RISC-V calling convention.
- [x] Expose the arbitrary-list Loop-to-Word argument-reading agreement used
  at the call-entry boundary.
- [x] Generalize Loop-to-Word tail-call dispatch to arbitrary argument and
  parameter lists with explicit Loop and Word callee binding witnesses.
- [x] Generalize the Loop-to-Word exception-handler call boundary to arbitrary
  argument and parameter lists, retaining explicit exception-register and
  handler-body simulation obligations.
- [x] Add the corresponding parameterized Word tail-call semantic contract.
- [x] Generalize FrameMachine call equations from leaf callees to explicit
  evaluated callee-state witnesses, with compound return and handler tests.
- [x] Mirror the arbitrary-callee call equations at the abstract StackLang
  boundary, with compound return and handler regressions.
- [x] Add returned-callee and raised-handler equations for the combined Word
  evaluator, with compound callee and handler regressions.
- [x] Add a combined graph-allocation soundness contract exposing fixed tags,
  edge safety, and the clash-tree witness at the function boundary.
- [x] Add the spill-aware function allocator contract exposing clash safety,
  special-instruction safety, and the spill clash-tree witness.
- [x] Expose location witnesses for every renamed program variable at the
  preference-aware spill allocator boundary, in addition to formal parameters.
- [x] Extend variable-location coverage to the ABI-pinned, entry-inclusive
  full-SSA spill allocator.
- [x] Port the CakeML `full_ssa_cc_trans` function-entry sequence, retaining
  fresh formal names and the explicit priority-1 parameter moves in the Lean
  Word program returned to allocation clients.
- [x] Compose the full-SSA entry sequence with the graph allocator, retaining
  fixed ABI source names and returning the coloured entry-inclusive program.
- [x] Expose full-SSA graph allocation soundness and formal-parameter coverage
  contracts for the renamed entry-inclusive program.
- [x] Connect the full-SSA graph allocator to a public end-to-end
  Word-to-Stack/StackRemove/RISC-V entry point with an execution regression.
- [x] Compose the full-SSA entry sequence with the clash-tree spill allocator,
  retaining entry moves in its locations, preferences, and returned program.
- [x] Pin full-SSA ABI source names to their architectural registers in the
  spill allocator before lowering entry moves.
- [x] Prove that seeded full-SSA ABI source locations are preserved by the
  spill allocation worklist.
- [x] Prove that the fixed-source spill allocator maps every requested SSA
  slot, while retaining the architectural locations of ABI source names.
- [x] Expose fixed-source function-level contracts for ABI parameter
  preservation and renamed formal-parameter location coverage.
- [x] Align the executable Word clash tree with CakeML’s source equations for
  calls, return continuations, allocation, constant storage, install, and FFI
  live sets, with structural regressions for each corrected case.
- [x] Expose a graph-backed Word-to-Stack pipeline that consumes the complete
  full-SSA entry-inclusive function program.
- [x] Expose the corresponding ABI-correct spill-backed Word-to-Stack pipeline
  for entry-inclusive full-SSA functions.
- [x] Expose an end-to-end Flapjack-to-RISC-V compiler entry point using the
  full-SSA spill pipeline.
- [x] Expose the linked full-SSA RISC-V artifact with section entry addresses
  for downstream execution and correctness clients.
- [x] Prove concrete machine execution of the linked full-SSA artifact for a
  constant-return `main`, including the linked raise-stub image.
- [x] Exercise full-SSA FFI lowering through the linked RISC-V host boundary,
  and prove source-level FFI results agree with generated machine execution.
- [x] Route the spill-aware RISC-V pipeline through the implemented
  clash-tree/preference allocator and retain its allocation witness at the
  Word-to-Stack boundary.
- [x] Connect the spill allocator's location map directly to the
  location-aware Word-to-Stack bitmap entry point.
- [x] Connect the SSA/graph allocator's renamed output and graph-derived
  locations to the location-aware StackLang function entry point.
- [x] Prove compositional Word-to-RISC-V correctness for the straight-line
  instruction-list fragment, including sequential code composition.
- [x] Prove that register-based branch condition preludes preserve Word
  comparisons and bit tests under the RISC-V zero-register invariant.
- [x] Reduce zero-immediate branch conditions to the verified register-zero
  condition boundary.
- [x] Prove immediate Word condition lowering soundness for nonzero values,
  including `ORI`/`ANDI` scratch materialization and the scratch alias guard.
- [x] Prove the machine-level PC contract for the branch instruction selected
  by every Word comparison, and compose it with the verified condition
  prelude under the RISC-V zero-register invariant.
- [x] Preserve CakeML WordLang's `MustTerminate` wrapper through Word
  semantics, SSA/clash analysis, colouring, Word-to-Stack, and RISC-V lowering,
  with focused regressions.
- [x] Lower CakeML/Loop-to-Word tail calls (`Call NONE`) through Word-to-Stack,
  preserving the even-numbered ABI argument moves and terminal call carrier.
- [x] Expose witness-level allocator contracts showing every successfully
  coloured SSA slot maps to an allocatable RISC-V register.
- [x] Port CakeML-style move preference edges for Word copy nodes and feed
  them into a reserved-register-aware preference colourer with soundness
  regressions.
- [x] Thread Word move preferences through the spill-aware clash-tree allocator,
  including coalescing, clash override, and a checked tree-driven entry point.
- [x] Expose the same preference-aware clash-tree spill allocator at the
  function boundary, retaining renamed ABI formal parameters as allocation
  slots and covering an unused-formal regression.
- [x] Prove the preference-aware function boundary exposes a concrete
  location witness for every renamed ABI formal.
- [x] Reserve the RISC-V address scratch register x29 from Word allocation and
  cover the allocator/backend separation with executable regressions.
- [x] Reserve the RISC-V LongMul normalization scratch register x28 from Word
  allocation and cover the resulting register contract with regressions.
- [x] Reserve the spill-aware AddCarry scratch register x27 from Word
  allocation and cover the resulting register contract with regressions.
- [x] Prove spill-aware allocation assigns every requested slot a concrete
  register or stack location.
- [x] Extend the concrete-location witness contract to preference-aware
  spill allocation, including the recursive lookup-preservation proof.
- [x] Connect successful preference-aware function allocation to its
  initialized source-to-node bijection, proving every renamed formal has a
  concrete node witness (including unused formals).
- [x] Prove every successfully allocated SSA function formal receives a
  concrete register or stack location for its ABI entry move.
- [x] Prove every successfully allocated SSA program variable receives a
  concrete register or stack location at the renamed-program boundary.
- [x] Prove successful SSA program allocation preserves the renamed program's
  analyzed clash invariant.
- [x] Port the first CakeML `word_to_stack` spill-move boundary, including all
  register/stack source and destination combinations.
- [x] Give generated spill moves an executable StackLang semantics and prove
  source-value preservation under the reserved-scratch contract.
- [x] Prove concrete Stack-machine preservation for generated Word-to-Stack
  variable moves, including a spilled-destination regression.
- [x] Lower spilled Word load/store instructions through independent address
  and data scratch registers in the StackLang boundary.
- [x] Lower spilled Word division operands and destinations through the
  StackLang arithmetic boundary.
- [x] Prove abstract Stack-machine preservation for lowered Word loads and
  stores, including spill locations and scratch-register alias conditions.
- [x] Prove abstract Stack-machine preservation for lowered Word division,
  including the nonzero-divisor source contract and spilled operands.
- [x] Prove abstract Stack-machine preservation for lowered shared-memory
  loads and stores, including spilled operands and scratch-register alias
  conditions.
- [x] Prove Stack-machine preservation for concrete Word store lookups and
  updates, including spilled source materialization.
- [x] Extend the Word-to-Stack boundary through conditions, loops, returns,
  calls, exception handlers, special stores, and FFI operations.
- [x] Marshal Word-to-Stack FFI arguments into the x10--x13 ABI registers,
  including spilled sources and an explicit clobber-safety boundary.
- [x] Prove the individual Word-to-Stack FFI argument move preserves its
  source value for both register and spill locations.
- [x] State a concrete end-to-end FFI theorem relating source call-aware
  evaluation to execution of the generated linked RISC-V image.
- [x] Separate StackLang continuation metadata from the RISC-V x1 ABI at the
  LabLang boundary: ordinary calls write dedicated x1 links, returns use
  `JALR x0,x1,0`, and FFI's logical return-address field retains its original
  non-link behavior.
- [x] Allocate fresh return labels for lowered calls and keep handler bodies
  in a non-overlapping label range, preserving linked cross-section targets.
- [x] Correct LabLang conditional polarity to match the Lean branch semantics
  and restore the concrete 244-byte handler-address regression.
- [x] Avoid scratch-register aliasing in StackLang stack-size get/set lowering
  and cover the x31 edge cases with executable tests.
- [x] Validate the current port increment with a complete no-cache build of
  all 238 Lake targets.
- [x] Add concrete `Nat` Word-to-Stack expression lowering for constants,
  register/stack atoms, binary operations, loads, stores, and stack-backed
  destinations, with separate value/address scratch registers.
- [x] Add executable concrete StackLang semantics for registers, frame slots,
  stores, and abstract full-word memory, with a constant-assignment
  preservation theorem.
- [x] Add a StackLang shift carrier and lower register/immediate Word shifts,
  including spilled operands, through the concrete Nat expression compiler.
- [x] Prove concrete Stack-machine preservation for atomized variable loads,
  including a fully spilled destination/address regression.
- [x] Prove concrete Stack-machine preservation for constant-address loads,
  including a spilled destination regression.
- [x] Prove concrete Stack-machine preservation for atomized variable stores,
  including a fully spilled source/address regression.
- [x] Preserve StackLang arithmetic and shifts through LabLang and lower them
  to executable RISC-V instructions, including sized rotate-right expansion.
- [x] Preserve `ShMemOp` as a distinct StackLang operation through LabLang
  and the RISC-V shared-memory selector.
- [x] Port the HOL RISC-V `LongMul` lowering with executable unsigned high-half
  multiplication (`MULHU`) followed by low-half multiplication (`MUL`),
  including the target's high-destination/source non-aliasing precondition and
  a register-parametric machine execution contract.
- [x] Port CakeML's normalized fixed-register `LongDiv` Word-to-Stack
  lowering, including divisor spill materialization and fixed-register guards.
- [x] Carry register-resident `LongMul` and `AddCarry` Word arithmetic through
  Word-to-Stack and multi-instruction LabLang expansion; spilled multi-result
  arithmetic remains part of the allocator/backend work.
- [x] Port register-addressed and simple offset-addressed `WordProg.shareInst`
  memory lowering for all currently modeled HOL word load/store operators,
  including evaluator and call-aware selector coverage.
- [x] Reuse the normalized address materialization for ordinary `WordProg.store`
  operations, covering the store form emitted by global rewriting.
- [x] Lower `WordProg.locValue` through the plain and call-aware RISC-V
  selectors, with executable evaluator agreement.
- [x] Port unsigned RISC-V halfword (`LHU`/`SH`) memory operations through the
  model, Word IR, selector, evaluator, and executable round-trip regression.
- [x] Port CakeML flat-memory byte and aligned 32-bit load/store operations
  over RISC-V word cells, with little-endian and alignment regressions.
- [x] Extend the RISC-V flat source evaluator with size-aware shared-memory
  loads and stores for words, bytes, halfwords, and aligned 32-bit values.
- [x] Add a fuel-bounded RISC-V flat source evaluator with structured control
  results for loops, declaration calls, exceptions, primitive dispatch, FFI,
  and RISC-V byte/32-bit/shared-memory operations.
- [x] Prove model-level register agreements for unsigned RISC-V division and
  remainder, including the HOL/RISC-V zero-divisor results.
- [x] Prove the AddCarry lowering preserves non-result registers outside its
  two destinations and x31 scratch register.
- [x] Generalize the AddCarry result theorem to arbitrary allocator-selected
  registers under explicit destination/source/scratch non-alias conditions.
- [x] Prove a mapped Loop-to-Word AddCarry agreement under explicit register
  value, destination non-alias, and allocator scratch contracts.
- [x] Lift primitive-aware Loop AddCarry execution to complete mapped-local
  preservation through the emitted RISC-V sequence.
- [x] Lift the AddCarry bridge through the fully composed primitive/call/FFI
  Loop evaluator and handler-aware Word evaluator.
- [x] Lift the ordinary LongMul bridge through the fully composed call/FFI
  Loop evaluator and handler-aware Word evaluator.
- [x] Exercise the composed LongMul bridge with a mapped-local RISC-V
  regression and an explicit destination non-alias proof.
- [x] Lift ordinary division through the composed call/FFI Loop evaluator and
  handler-aware Word evaluator, with a concrete mapped-local regression.
- [x] Generalize the composed LongMul and division bridges to arbitrary
  positive evaluator fuel for later sequence/loop induction.
- [x] Generalize the composed AddCarry bridge to arbitrary positive evaluator
  fuel for later sequence/loop induction.
- [x] Add the control-neutral Loop-to-Word `skip` preservation rule and keep
  its regression in a dedicated control-correctness test module.
- [x] Lift the Loop no-memory-write projection invariant from one step to
  arbitrary fuel, including sequencing, conditionals, loop repetition, and
  control results.
- [x] Compose the arbitrary-fuel local, global, and memory projections into a
  reusable full `LoopState` frame theorem, with return and loop-control tests.
- [x] Prove Word expression evaluation is preserved by SSA renaming under an
  explicit register and memory correspondence.
- [x] Prove Word expression evaluation is preserved by applying a physical
  register colouring under the corresponding register and memory relation.
- [x] Prove Word condition evaluation is preserved by applying a physical
  register colouring, including immediate and register comparison operands.
- [x] Prove physical-colouring preservation for Word return-value lists and
  raised exception values under the corresponding register relation.
- [x] Prove Word condition evaluation is preserved by SSA renaming, including
  immediate and register comparison operands.
- [x] Prove SSA-renamed Word return evaluation preserves arbitrary returned
  register lists under the register correspondence.
- [x] Prove SSA-renamed Word raise evaluation preserves the raised exception
  value under the register correspondence.
- [x] Prove the complete Loop state-preservation theorem, including the
  remaining operations and control-flow invariants.
- [x] Add the terminal return control-result bridge, including mapped state
  preservation and equality of Loop and Word returned value lists.
- [x] Add the terminal raise control-result bridge, including mapped state
  preservation and equality of Loop and Word raised exception values.
- [x] Prove that compiler-generated RISC-V ticks preserve the mapped-local
  relation needed by conditional and loop simulations.
- [x] Prove conditional branch simulation for fuel-2 Loop programs, including
  the compiler-generated post-conditional tick.
- [x] Add fuel-bounded Word loop execution with explicit break and continue
  control results, plus basic loop-control regression theorems.
- [x] Add handler-aware Word loop execution with recursive calls, FFI actions,
  and control-result propagation, with focused regressions.
- [x] Prove the loop-aware Loop-to-Word FFI simulation boundary for the fully
  composed primitive/call/FFI evaluator, with a mapped-local regression.
- [x] Add the normal-path loop-aware sequence simulation rule needed to
  resume Word loop code after a composed FFI or call.
- [x] Generalize loop-aware sequence simulation to propagate normal, return,
  raise, break, and continue results, with an FFI-followed-by-break regression.
- [x] Add the handler-free loop-aware call boundary for fully composed callee
  evaluation, including propagation of a callee `break` result.
- [x] Exercise the actual Loop-to-Word loop lowering through the Word loop
  evaluator, including its generated entry and exit ticks.
- [x] Add layout-aware RISC-V lowering for Word loops, resolving generated
  break and continue jumps and wiring it into the default pipeline.
- [x] Extend call-aware RISC-V lowering and linked return-signature derivation
  to retain loop-containing Word functions.
- [x] Execute a lowered RISC-V loop with a generated break jump through the
  architectural code runner.
- [x] Add an end-to-end source `while` regression through Loop/Word loop
  lowering and RISC-V architectural execution.
- [x] Add an end-to-end source full-word store/load regression through the
  composed pipeline and RISC-V byte-memory execution.
- [x] Promote the composed full-word store/load regression to a library-level
  source-memory versus compiled-RISC-V correctness theorem.
- [x] Prove generic fuel-inductive Loop/Word repeat preservation for normal,
  break, and continue control results.
- [x] Compose repeat preservation with the generated entry/exit ticks and prove
  the outer Loop-to-Word loop simulation rule.
- [x] Prove the one-step global-state projection invariant for every Loop
  constructor under the no-global-writes syntactic side condition.
- [x] Lift the global-state projection invariant to arbitrary fuel, including
  sequence, conditional, loop-repeat, and control-result cases.
- [x] Derive the direct successful-evaluation global-state corollary used by
  downstream Loop result-state proofs.
- [x] Prove the first source-to-Crepe-to-Loop semantic bridge for compiled
  constant returns using the executable Loop evaluator.
- [x] Establish reusable Loop state-transition lemmas for the modeled
  assignment, load/store (including byte and 32-bit forms), shared-memory,
  `locValue`, global, return, and control-result cases.
- [x] Isolate successful option-bind result-state invariants for use in the
  fuel-bounded Loop preservation induction.
- [x] Add context-mapped Loop-to-Word register agreements for assignments
  and read-only 32-bit loads, plus the low-byte memory observation for
  `store32`, with explicit byte-fold memory premises.
- [x] Prove mapped-local state preservation for compiled Loop/RISC-V `load32`
  and `store32`, including source-memory and architectural-word observations.
- [x] Prove mapped-local state preservation for compiled byte loads and stores,
  including zero-extension and preservation of all non-destination locals.
- [x] Prove mapped-local preservation for structured shared-memory `load8` and
  `store8` lowering through the emitted `shareInst` operations.
- [x] Prove mapped-local preservation for structured shared-memory `load16` and
  `store16` lowering through the emitted `shareInst` operations.
- [x] Prove mapped-local preservation for structured shared-memory full-word
  `load` and `store` lowering, including register preservation through the
  byte-fold word store.
- [x] Prove mapped-local preservation for ordinary constant-address `store`
  lowering, with the RISC-V x31 address-materialization scratch contract.
- [x] Generalize the context-mapped Loop-to-Word assignment agreement to all
  register-register binary operations, including BitVec bitwise compatibility.
- [x] Correct and prove context mapping for both operands of Loop `locValue`
  assignments in the Loop-to-Word/RISC-V bridge.
- [x] Add context-mapped Loop-to-Word/RISC-V agreements for byte loads and
  stores in the emitted shared-memory form, including zero-extension and byte
  truncation at the memory boundary.
- [x] Add context-mapped agreements for shared-memory halfword loads and
  stores, including the first little-endian byte observation.
- [x] Lift the one-step mapped expression agreements to a reusable
  context-indexed assignment simulation lemma.
- [x] Add reusable mapped LSL/LSR assignment simulation with an explicit
  source shift-count bound matching the RISC-V masking convention.
- [x] Prove preservation of the mapped-local relation across a destination
  update and corresponding non-aliasing RISC-V register write.
- [x] Prove mapped-local preservation for same-destination Loop `longMul`,
  including the emitted `mulHU`/`mul` sequence and source-register non-aliasing.
- [x] Prove mapped source-variable evaluation agrees with the compiled Word
  variable evaluation whenever the source local is present.
- [x] Prove the one-parameter call-boundary case: fresh Loop local binding
  agrees with cleared-and-bound Word registers under the mapped-local relation.
- [x] Prove that every source slot in the pipeline's `name ↦ name + 2`
  context is found with its mapped register name.
- [x] Compose the single-parameter Loop and Word binding lemmas into an
  explicit call-boundary state-agreement theorem.
- [x] Prove the handler-free single-parameter call simulation boundary,
  including argument transfer, callee-frame setup, return propagation, and
  preservation of the caller's mapped locals.
- [x] Add the handler-aware single-parameter call simulation boundary,
  including compatible callee normal/raise results, exception-register
  binding, handler resumption, and mapped-local preservation.
- [x] Add a concrete exception-handler call regression covering constant
  exception production, callee raise propagation, and handler continuation.
- [x] Prove control-result sequence composition for normal completion,
  returns, and raises under the combined Loop and handler-aware Word
  evaluators.
- [x] Prove mapped-local preservation across compiled register-register
  ADD/SUB/AND/OR/XOR assignments, including unchanged non-destination locals.
- [x] Prove mapped-local preservation across compiled LSL/LSR assignments,
  with the explicit bounded shift-count agreement.
- [x] Prove mapped-local preservation across compiled constant assignments,
  carrying the architectural x0 invariant.
- [x] Prove mapped-local preservation across compiled unsigned division,
  including the nonzero-divisor condition and DIVU result agreement.
- [x] Prove mapped-local preservation across compiled `locValue` moves,
  including preservation of all non-destination locals.
- [x] Prove mapped-local preservation across ordinary variable assignments,
  which lower to the same register move as `locValue`.
- [x] Prove successful two-step Loop/Word sequence evaluation decomposes
  through matching intermediate Loop and machine states.
- [x] Add the compositional sequence simulation rule that chains mapped-local
  preservation across both successful components.
- [x] Generalize the normal-path Loop-to-Word sequence simulation rule to
  arbitrary Loop fuel budgets.
- [x] Prove mapped Loop/Word condition agreement for equality, unsigned
  ordering, and HOL zero-test comparisons with immediate/register operands.
- [x] Prove Loop slot-analysis insertion helpers preserve duplicate-freeness,
  supporting later derivation of register non-aliasing invariants.
- [x] Prove RISC-V `registerOfNat` injectivity and derive pipeline-specific
  non-aliasing for distinct mapped source slots.
- [x] Extend Loop condition and expression evaluation to all comparison
  constructors, including HOL's zero-test convention for test/not-test.
- [x] Add an end-to-end declaration-call regression from Pancake through
  source semantics, Loop, Word, call-aware linking, Word semantics, and RV64
  execution, with a combined source/Word/machine agreement theorem.
- [x] Add an end-to-end conditional compiler-correctness theorem from source
  `if` through the linked RV64 artifact and architectural execution.
- [x] Exercise the same theorem shape with parameter-dependent equality
  branches on both equal and unequal RV64 inputs.
- [x] Add handler-aware source control-result semantics for the supported
  expression/call fragment, including exception matching, handler-variable
  binding, and a concrete raised-call regression.
- [x] Add an explicit source-level FFI handler boundary with evaluated
  arguments, caller-local state threading, and a concrete host-update
  regression.
- [x] Compose the source FFI boundary with nested calls and declaration-call
  result assignment in a fuel-bounded source regression.
- [x] Compose the source FFI boundary with the source call evaluator, allowing
  host effects inside a callee before declaration-call result propagation.
- [x] Integrate fuel-bounded source memory semantics for `while` loops, with
  verified immediate termination for false conditions.
- [x] Extend direct source memory semantics with structural `if` execution.
- [x] Add source equality-condition evaluation for local variables and a
  conditional-program regression.
- [x] Extend memory-backed source equality conditions through fuel-bounded
  conditional execution and add a load-based regression.
- [x] Extend scalar source expression semantics to subtraction, bitwise
  operations, all comparison constructors, and logical shifts, with executable
  Nat regressions.
- [x] Add scoped local-declaration semantics to the base, stateful,
  call-aware, and handler-aware scalar source evaluators, with focused
  regressions.
- [x] Close the constant binary-expression RISC-V selector gap and prove
  end-to-end RV64 subtraction and bitwise pipeline regressions.
- [x] Add the first structured source-value evaluator, preserving words,
  raw/named records, field projection, globals, shaped loads, and stateful
  local/global/memory updates with executable regressions.
- [x] Extend the structured evaluator with fuel-bounded declaration calls,
  caller-local result binding, matching exception handlers, and an explicit
  structured FFI boundary with executable regressions.
- [x] Add structured control-result support for scoped declarations, stores,
  conditionals, while loops, break/continue, and shared-memory operations,
  with executable store/load and loop regressions.
- [x] Port the top-level structured declaration environment for structures,
  globals, functions, and exceptions, and expose an entry-point evaluator that
  composes declaration processing with calls, primitives, and FFI.
- [x] Enforce structure-context well-formedness for structured loads, matching
  the source evaluator's shape-validation rule.
- [x] Connect the structured source evaluator to end-to-end declaration-call
  and FFI-call correctness fixtures.
- [x] Add an explicit source primitive-handler interface with a RISC-V
  `AddCarry` implementation and executable structured-evaluator regression.
- [x] Add the matching handler-parameterized Crepe state evaluator, including
  flattened primitive-result assignment and a compiled AddCarry regression
  linked back to the structured source result.
- [x] Prove the primitive constructor is preserved by the Crepe-to-Loop
  lowering and that both evaluators agree on its updated locals and results.
- [x] Prove the emitted RISC-V AddCarry sequence preserves the complete
  mapped-local relation under explicit allocator non-alias contracts.
- [x] Extend the Crepe primitive evaluator across compiled memory stores,
  loads, conditionals, and result extraction.
- [x] Port CakeML's flat structured-memory load/store model, including
  consecutive word offsets, `Comb`/`Named` reconstruction, flattening, and
  failed-domain behavior.
- [x] Extend the flat source evaluator with fuel-bounded calls, scoped
  declaration calls, caught exceptions, loops, primitive dispatch, and FFI.
- [x] Complete generic flat source `load32` and `loadByte` expression
  evaluation with domain-checked word reads, alongside focused regressions.
- [x] Add a handler-parameterized Loop evaluator for primitive dispatch and
  connect its RISC-V AddCarry handler to an executable Loop-to-Word agreement.
- [x] Prove a structured AddCarry source program through the composed
  Pancake/Crepe/Loop/Word straight-line RISC-V artifact.
- [x] Split the regression suite into focused modules under `Flapjack/Test`.
- [x] Split the RISC-V regression suite further into backend and flat-memory
  modules as the source-memory adapter grew.
- [x] Prove a pass-composed Crepe/flat-source structured store/load
  correctness bridge for flattened record payloads.
- [x] Prove a one-step Loop-to-Word FFI simulation theorem under an explicit
  RISC-V host-handler agreement, with a concrete register-mapped regression.
- [x] Prove the generated RISC-V FFI ABI move/`ECALL` sequence agrees with the
  abstract Word FFI handler under explicit non-clobber and service-width
  contracts.
- [x] Lift the generated FFI ABI agreement through the call-aware WordProg
  compiler entry point and its fuel-bounded handler-aware evaluator.
- [x] Prove the ordinary single-parameter Loop-to-Word call boundary, including
  singleton result assignment and rejection of incompatible result arities.
- [x] Exercise the loop-aware call boundary with a callee that performs an FFI
  action under the fully composed Loop and Word evaluators.
- [x] Extend the loop-aware call boundary through an exception handler and
  verify the handler's exception binding in the mapped-local relation.
- [x] Prove fully composed repeat-loop preservation for all five control
  outcomes, including zero-labelled break termination and continue recursion.
- [x] Add a concrete zero-labelled break regression for repeat-loop
  preservation.
- [x] Port the initial StackLang store-removal slice for fixed stores,
  `CurrHeap`, stack-frame allocation/free, and fixed/dynamic stack accesses,
  recursively rewriting nested control-flow and call bodies into explicit
  word-memory operations.
- [x] Lower the compact remaining StackLang store-removal equations for
  `OpCurrHeap`, stack-size conversion, and bitmap loads.
- [x] Expose the first executable StackLang → StackRemove → LabLang → RISC-V
  composition and test exact RV64 instruction output.
- [x] Lower StackLang `DataBufferWrite` to explicit word memory and verify the
  result through the RV64 backend.
- [x] Port the structured StackLang `StoreConsts` bitmap-copy lowering and
  verify that its generated loop compiles through the RV64 backend.
- [x] Add a concrete WordProg → Word-to-Stack → StackRemove → LabLang → RV64
  composition with an exact constant-lowering regression.
- [x] Add a combined structured Pancake evaluator that threads primitive
  handlers through declarations, calls, loops, exceptions, and FFI, with
  AddCarry source and nested-call regressions.
- [x] Add the width-indexed Word-to-Stack adapter and an actual
  `WordProg (Word width)` to RISC-V entry point, preserving bit-vector
  constants through the explicit Nat StackLang boundary.
- [x] Add explicit generated function entry labels and a cross-section
  StackLang program linker through LabLang and the RISC-V backend.
- [x] Wire the register-coloured Word function list through the actual
  Word-to-Stack, StackRemove, LabLang, and multi-section RISC-V pipeline, with
  an RV64 addition compilation regression.
- [x] Wire the executable SSA/clash-colouring Word allocation boundary into a
  separate allocated Stack-to-RISC-V entry point with an allocation regression.
- [x] Exercise the allocated Stack-to-RISC-V entry point on a declaration call
  across two generated function sections.
- [x] Preserve linked section labels and byte entry addresses through the
  allocator-aware Stack/RISC-V entry point for execution-harness integration.
- [x] Move allocated formal parameters from the incoming even-numbered ABI
  registers into their allocated registers or spill slots at function entry.
- [x] Add CakeML-style function SSA setup: fresh formal names above the source
  variable range, with unused formals retained in spill allocation inputs.
- [x] Align the allocated pipeline with the established Loop-to-Word context
  and `name + 2` formal-parameter mapping before function SSA setup.
- [x] Port CakeML's source-faithful SSA FFI boundary: refresh the live cut set,
  marshal the four ABI arguments, emit the FFI node, and restore the cut set.
- [x] Preserve every architectural even-numbered Word name in spill
  allocation, including FFI ABI operands that are not formal parameters.
- [x] Port CakeML's SSA call ABI boundary for handler-free calls, including
  argument-register moves and refreshed normal-return cut sets.
- [x] Port the returned-call exception-handler SSA boundary, including
  ABI return copies and explicit reconciliation of normal and exceptional
  handler states.
- [x] Match CakeML's loop SSA setup by separating fresh live names from
  refreshed names and zero-initializing newly introduced names.
- [x] Port CakeML's cut-set-aware SSA allocation boundary, including ABI
  size marshalling and post-allocation cut-set restoration.
- [x] Port CakeML's SSA Raise and Return ABI equations, moving exceptions and
  result values through the fixed return register sequence.
- [x] Port CakeML's SSA Install boundary, including code-pointer/length ABI
  marshalling and post-install pointer/cut-set restoration.
- [x] Port CakeML's SSA StoreConsts boundary, including code/data length ABI
  marshalling and fresh result restoration.
- [x] Match CakeML's two-pass SSA branch reconciliation, including prioritized
  merge moves and zero-register initialization for one-sided names.
- [x] Match CakeML's SSA cut-set reconciliation with priority-1 moves and
  omission of names absent from the current map.
- [x] Prove the generated SSA `Raise` ABI sequence preserves the exception
  semantic result under the allocator's register and scratch invariants.
- [x] Prove the generated one-result SSA `Return` ABI sequence preserves the
  returned value under the allocator's register and scratch invariants.
- [x] Prove the generated multi-result SSA `Return` ABI sequence preserves all
  returned values under acyclic ABI-move and register-state invariants.
- [x] Marshal allocated Word call arguments into the even-numbered ABI
  registers before StackLang call-frame construction, for both handler-free
  and handler-aware calls.
- [x] Prove that an allocated Word-to-ABI argument move preserves the
  source value at its physical destination, including register and spill
  sources.
- [x] Replace the fixed StackRemove fuel in all composed backend entry points
  with a size-derived bound, so generated functions are not limited to 1024
  levels of nesting.
- [x] Prove the non-`CurrHeap` StackRemove `Get` equation against the
  executable StackLang machine state under an explicit store-memory invariant.
- [x] Prove the matching non-`CurrHeap` StackRemove `Set` equation under
  explicit address/source non-aliasing conditions.
- [x] Prove the `CurrHeap` StackRemove fast-path simulations for both `Get`
  and `Set`.
- [x] Prove the bounded StackRemove stack-allocation equation under an
  explicit scratch/stack-pointer non-aliasing condition.
- [x] Prove the one-step Loop local-state projection for programs classified
  as not writing the observed local, including all executable instruction
  forms and control constructors.
- [x] Lift Loop local-state projection to arbitrary fuel, including sequence
  and repeat execution, for every successful base-evaluator result.
- [x] Prove StackRemove fixed-offset stack load/store simulations under
  explicit address-scratch and memory-write invariants.
- [x] Match CakeML's byte-scaled negative store offsets in StackRemove and
  update the store-memory simulation invariant accordingly.
- [x] Complete the StackRemove `StoreConsts` bitmap-copy loop with the final
  `copy_each` pass from CakeML and add a structural regression.
- [x] Connect the exact CakeML byte-level FFI oracle/event boundary to the
  generated RISC-V x10--x14 ABI, including returned-byte writes, terminal
  outcomes, unknown-service rejection, and an executable RV64 regression.
- [x] Align the Word clash tree's call equations with CakeML cut-set `Set`
  boundaries and exceptional handler branches, with reduced-IR regressions.
- [x] Prove general normal-return and terminal-outcome equations for the exact
  RISC-V ECALL adapter directly from CakeML's `callFfi` equations.
- [x] Prove that the generated RISC-V FFI ABI prefix reaches the exact ECALL
  adapter, with an explicit zero-register invariant and an RV64 regression.
- [x] Prove the exact RISC-V ECALL adapter's CakeML length-mismatch failure
  equation and add a concrete terminal-failure regression.
- [x] Extend the Word/Stack/Lab carriers with CakeML runtime-store, heap,
  installation, and code/data-buffer operations; thread them through SSA,
  clash analysis, colouring, Word-to-Nat conversion, Word-to-Stack,
  StackRemove, and Lab flattening, with register/spill regressions. Bitmap-
  dependent `Alloc`/`StoreConsts` remain an explicit follow-up.
- [x] Port bitmap-aware `Alloc`/`StoreConsts` lowering and thread bitmap
  metadata through the allocator-aware declaration and RISC-V artifact
  pipeline, returning the generated bitmap table with the code.
- [x] Align the Word call and FFI carriers with CakeML's exact return cut sets,
  embedded return programs, handler labels, and paired FFI cut sets; preserve
  that metadata through SSA, clash analysis, colouring, executable semantics,
  and the RISC-V/Word-to-Stack consumers.
- [x] Port CakeML's downstream StackAlloc insertion traversal and section
  compiler, including fresh-label reservation, continuation recursion, and
  the generated GC-stub section. The collector body remains a separate
  semantic port.
- [x] Port CakeML's non-generational (`Simple`) copying-collector StackLang
  body and expose a runtime-backed Nat section compiler. The generated code
  now has a fuel-bounded executable StackLang machine boundary and concrete
  zero-heap, forwarding-pointer, and one-word object-copy execution
  regressions; the full heap/bitmap simulation theorem remains. Add a
  call-aware runtime bridge that resolves the generated GC label and resumes
  its return continuation.
- [x] Add CakeML-aligned halt-PC lowering and assemble the runtime-backed
  Simple StackAlloc image through the RV64 pipeline.
- [x] Add a target-level halt-aware Lab executor that follows the generated
  jump and returns when the architectural PC reaches the linked halt PC.
- [x] Add a linked StackLang evaluator that resolves generated label calls,
  executes the runtime collector stub, and resumes the explicit return
  continuation under fuel.
- [x] Port the word-only CakeML collector specification for forwarding
  pointers, object copying, destination-memory updates, and preservation
  equations.
- [x] Preserve the location-valued collector input case and its success
  condition from CakeML's word_gc_move definition.
- [x] Port the word-only collector root traversal, pointer-list traversal,
  and bounded heap-scan recursion with condition and memory threading. The
  word-level full-collection composition is included; the full StackLang
  heap/bitmap simulation remains.
- [x] Preserve the total-domain condition invariant through location-valid
  bitmap root values during Nat root traversal.
- [x] Port the collector scan-condition invariants corresponding to CakeML's
  `word_gc_move_loop_F` and `word_gc_move_loop_ok` theorems.
- [x] Add a bounded StackLang frame-state evaluator matching CakeML's
  `stack_space` checks, fixed/dynamic stack accesses, stack-size conversion,
  and bitmap loads, with explicit structured control outcomes.
- [x] Execute the generated non-generational collector through the bounded
  frame evaluator on a zero-heap state.
- [x] Prove the immediate-pointer StackLang collector case against the pure
  Nat `stackGcNatMove` specification at the machine-result boundary.
- [x] Add reusable bounded fixed-slot frame equations and exercise the
  forwarding-pointer and object-copy `word_gc_move` cases against the pure
  Nat observations.
- [x] Carry explicit main/shared memory domains through the bounded frame
  evaluator and reject out-of-domain loads in both memory spaces.
- [x] Expose the RISC-V little-endian byte, halfword, and 32-bit memory
  equations at the bounded StackLang frame-machine boundary, including
  alignment failures.
- [x] Prove the bounded StackLang collector memcpy zero-word base case,
  preserving the complete frame state.
- [x] Add reusable bounded-frame sequence and conditional evaluator equations
  for compositional collector proofs.
- [x] Prove the generated bitmap `MoveBitmap` and `MoveBitmaps` sentinel
  machine states terminate without changing the frame state.
- [x] Expose the bounded frame-machine bitmap-table load equation under its
  destination/register separation and successful bitmap lookup conditions.
- [x] Add the fuel-indexed frame-machine iteration API for the generated
  bitmap-root `MoveBitmaps` loop.
- [x] Add the corresponding fuel-indexed iteration API for the generated
  `MoveRootsBitmaps` root loop.
- [x] Compose the bitmap root-movement phase with the subsequent heap-scan
  phase at the bounded frame-machine boundary.
- [x] Prove the exact bounded-frame collector memcpy-body transition,
  including scratch-register state and destination-memory update.
- [x] Compose that transition with the bounded loop evaluator for the
  one-word memcpy case.
- [x] Factor the collector copy path into named machine-state transitions and
  prove its complete one-word non-forwarded branch composition.
- [x] Factor the collector forwarding path into named machine-state
  transitions and prove its full branch composition.
- [x] Prove the zero-iteration machine equations for collector move-list,
  heap-scan, and bitmap-root loops.
- [x] Complete the pure Nat collector copy-case equations for the copied
  value, next destination address, forwarding-header write, and success
  condition.
- [x] Add an iterated frame-machine transition API for collector memcpy,
  including equations and invariants for the frame metadata preserved by
  every copy step.
- [x] Isolate the finite-word successor-minus-one equation and the resulting
  collector memcpy count-register transition.
- [x] Prove the bounded frame-machine memcpy evaluator for every bounded
  word count, using the iterated transition API and linear recursion-depth
  fuel.
- [x] Add Nat-level memcpy framing lemmas for domain success and
  non-destination memory preservation.
- [x] Expose named one-step frame-machine equations for collector memcpy,
  covering the count, loaded value, source, destination, and memory updates.
- [x] Prove the iterated collector memcpy register equations, including
  bounded count exhaustion and source/destination address advancement.
- [x] Define the recursive word-level memcpy memory transformer and prove the
  iterated frame machine realizes it under scratch-register separation.
- [x] Record the pointwise and function-level memory equations for one
  collector memcpy transition for reuse in later simulation proofs.
- [x] Prove word-level non-destination memory preservation for the recursive
  collector memcpy transformer.
- [x] Package the collector memcpy register and memory equations into a
  compositional frame-state correspondence predicate.
- [x] Lift the collector memcpy correspondence across a bounded iteration,
  including the final registers and recursive word-level memory transformer.
- [x] Compose the bounded collector memcpy evaluator with the iterated
  correspondence, exposing an executable simulation boundary.
- [x] Expose Nat projections for iterated source and destination registers,
  preserving the machine word-width modulo behavior.
- [x] Prove the collector destination-memory update commutes with projection
  from word addresses to the Nat memory model.
- [x] Relate the recursive word-level memcpy memory transformer to the Nat
  memcpy result under explicit memory-range and no-wrap hypotheses.
- [x] Prove an end-to-end bounded memcpy simulation boundary combining the
  frame evaluator, final destination address, and projected Nat memory.
- [x] Prove total-domain condition contracts for Nat collector `Move` and
  `MoveList`, establishing the condition-preservation premise for machine
  simulation over valid memory ranges.
- [x] Add the exact Nat one-item immediate-pointer `MoveList` transition,
  including scan advancement, unchanged move index/address, memory update,
  and domain condition.
- [x] Add the exact Nat one-item forwarding-pointer `MoveList` transition,
  including forwarding-address remapping and the two domain checks.
- [x] Add the exact Nat one-item copy `MoveList` transition, threading the
  recursive memcpy result, header forwarding write, destination advancement,
  and composed condition.
- [x] Compose the frame-machine immediate `MoveList` evaluator with the Nat
  immediate transition, proving the machine’s loaded value matches the
  projected Nat result under explicit address and memory correspondence.
- [x] Relate the immediate frame `MoveList` scan pointer to the Nat
  `nextScan` field under an explicit no-wrap bound.
- [x] Prove the total-domain condition contract for the recursive Nat root
  traversal, completing condition propagation through root `Move` calls.
- [x] Prove the one-item immediate-pointer `MoveList` frame transition,
  including load, count update, store, address advance, and loop termination.
- [x] Generalize the forwarding-path `Move` evaluator to arbitrary surplus
  fuel for compositional outer-collector proofs.
- [x] Prove the one-item forwarding-pointer `MoveList` frame transition,
  including the forwarding `Move`, store, address advance, and termination.
- [x] Generalize the one-word object-copy `Move` evaluator to arbitrary
  surplus fuel for outer-collector composition.
- [x] Prove the one-item object-copy `MoveList` frame transition, including
  the copy `Move`, store, address advance, and loop termination.
- [x] Port the CakeML `word_gc_move_list_append` decomposition to the Nat
  collector model, composing sequential MoveList segments and conditions.
- [x] Prove that the Nat MoveList scan pointer advances by
  `length * bytesInWord`, independently of moved object contents.
- [x] Add a fuel-indexed frame-machine theorem for iterated normal loop-body
  transitions, exposing per-iteration conditions and state updates.
- [x] Specialize the iterated frame-loop evaluator to the generated
  `stackGcMoveListCode` body for arbitrary concrete state transitions.
- [x] Expose named Nat `MoveLoop` code-object and data-object transition
  equations with fuel and condition threading.
- [x] Package the bounded frame-machine/Nat `MoveLoop` invariants as a
  reusable source-aligned simulation boundary, including condition soundness.
- [x] Prove the collector machine semantics and simulation theorem; the current
  RISC-V target does not require generational support.
- [x] Add executable CakeML bitmap encoding and an explicit bitmap-state
  accumulator for Word-to-Stack Alloc/StoreConsts, including sequential
  state-threading and fixed-width regression tests.
- [x] Add the recursive word/Nat bitmap-table relation and prove lookup
  preservation for bounded frame-machine bitmap loads.
- [x] Connect the bounded frame-machine bitmap-load result directly to the
  corresponding Nat bitmap-table lookup under that machine/Nat relation.
- [x] Bridge the immediate one-word machine MoveList evaluator to the Nat
  semantics for its moved value, scan pointer, count register, and stored
  memory projection.
- [x] Extend the immediate one-item MoveList bridge to the full bounded
  machine/Nat memory relation.
- [x] Extend the forwarding one-item MoveList bridge to the full bounded
  machine/Nat memory relation.
- [x] Extend the copying one-item MoveList bridge to the full bounded
  machine/Nat memory relation, parameterized by the recursive copy-memory
  correspondence.
- [x] Expose and relate the arbitrary-counter immediate MoveList body
  transition, including scan advancement and the full bounded memory update.
- [x] Expose the arbitrary-counter forwarding MoveList body transition for
  outer MoveList iteration.
- [x] Relate the arbitrary-counter forwarding MoveList body to its full
  bounded machine/Nat memory update and scan advancement.
- [x] Expose the arbitrary-counter copying MoveList body transition for outer
  MoveList iteration.
- [x] Relate the arbitrary-counter copying MoveList body to its full bounded
  machine/Nat memory update and scan advancement, parameterized by the
  recursive-copy and copy-address correspondences.
- [x] Generalize the copying MoveList suffix evaluator to arbitrary copied-word
  counts, reusing the fuel-indexed machine/Nat `Memcpy` bridge.
- [x] Add a named Nat post-`Memcpy` copy-suffix result with equations for its
  updated value, index, destination, forwarding-header memory, and condition.
- [x] Identify the Nat post-`Memcpy` copy suffix with the pure Nat `Move`
  copy branch for `decodeLength(header)+1` words.
- [x] Prove the Nat copy-suffix success contract under a total memory domain.
- [x] Name the Nat copying MoveList body result and identify it with the
  one-item Nat MoveList copy equation.
- [x] Relate the bounded post-`Memcpy` machine suffix evaluator to that Nat
  result, including the forwarding-header memory projection.
- [x] Lift the arbitrary-word suffix relation through the bounded machine
  `Memcpy` loop, including the domain-independent Nat memory projection.
- [x] Package the arbitrary-word copying `MoveCode` evaluator with the
  corresponding Nat suffix relation at the code-branch boundary.
- [x] Generalize the copying `MoveCode` evaluator to arbitrary copied-word
  counts, with an explicit prefix count correspondence and bounded count.
- [x] Expose a forwarding MoveList machine/Nat value bridge, parameterized by
  the explicit fixed-width forwarding-address correspondence.
- [x] Expose a copying MoveList machine/Nat value bridge, parameterized by the
  explicit fixed-width copied-value correspondence.
- [x] Align the machine MoveLoop termination condition with the Nat
  `scan != destination` condition under explicit word-width bounds.
- [x] Bridge the machine data/code header test (`header &&& 4`) to the Nat
  `header / 4 % 2` code tag under an explicit fixed-width bound.
- [x] Derive the machine MoveLoop branch condition directly from the Nat
  header tag and the bounded machine/Nat memory correspondence.
- [x] Specialize the data-step machine/Nat contract to derive its branch
  condition from the bounded memory correspondence.
- [x] Specialize the code-step machine/Nat contract to derive its branch
  condition from the bounded memory correspondence.
- [x] Specialize code-object MoveLoop relation preservation to derive the
  machine branch predicate from the combined scan/memory relation.
- [x] Add an induction principle propagating the combined machine/Nat
  relation across iterated MoveLoop states.
- [x] Package the fuel-indexed MoveList evaluator iteration together with
  propagation of the combined machine/Nat relation.
- [x] Package the fuel-indexed MoveLoop evaluator iteration together with
  propagation of the combined machine/Nat relation.
- [x] Prove the bounded machine transition for a code-object MoveLoop header,
  covering header load, length decoding, object-size scan advance, and the
  destination update without unfolding the nested MoveList loop.
- [x] Isolate the true-test MoveLoop code-header prefix as a bounded machine
  transition, leaving the nested MoveList execution as an explicit handoff.
- [x] Specialize the bounded frame-loop induction to `stackGcMoveLoopCode`,
  exposing per-iteration body transitions and final scan termination.
- [x] Compose the true-test MoveLoop data branch through its length-decoding
  prefix into an explicit MoveList evaluator handoff.
- [x] Compose the MoveLoop data-object header load with the true-test branch,
  yielding the complete bounded machine data-step transition.
- [x] Package the machine data-step with the Nat `MoveLoop` data-step equation
  for direct outer-loop induction.
- [x] Package MoveLoop data/code branch evaluators with their corresponding
  machine/Nat relation-preservation results.
- [x] Bridge the code-object MoveLoop machine step’s scan register to the Nat
  scan advance under explicit fixed-width memory and arithmetic hypotheses.
- [x] Package the code-object machine scan bridge with the corresponding Nat
  MoveLoop recursive-step equation for direct induction use.
- [x] Prove that the code-object MoveLoop machine transition preserves the
  underlying machine memory, making it composable with the collector invariant.
- [x] Introduce a bounded Nat memory-projection relation and prove that the
  code-object MoveLoop state transition preserves it.
- [x] Introduce the corresponding Nat scan-register relation and prove its
  preservation across the code-object MoveLoop transition.
- [x] Package the scan and bounded memory projections into a combined
  machine/Nat MoveLoop relation and prove code-object-step preservation.
- [x] Prove the bounded arbitrary-word MoveList copying-body evaluator,
  including the load/count prefix, copied-word MoveCode, store, and scan
  advancement.
- [x] Relate the arbitrary-word copying-body evaluator to the Nat body
  specification, including final registers and bounded memory projection.
- [x] Keep the arbitrary-word body relation independent of branch-specific
  Nat copy conditions, so it can be reused by later MoveList induction.
- [x] Package the terminal `MoveLoop` machine transition with the Nat
  terminal result and preservation of the machine/Nat relation.
- [x] Derive terminal MoveLoop scan equality from the machine/Nat relation
  and the destination-register correspondence.
- [x] Package MoveLoop destination and index registers into the terminal
  machine/Nat state relation.
- [x] Prove code-object MoveLoop steps preserve the extended destination and
  index register relation under explicit scratch-register separation.
- [x] Package code-object MoveLoop evaluation with preservation of the
  extended machine/Nat state relation.
- [x] Package data-object MoveLoop evaluation with the extended relation at
  the nested MoveList handoff and output.
- [x] Lift the extended scan/index/destination/memory relation through
  arbitrary MoveList loop iteration.
- [x] Lift the extended state relation through arbitrary outer MoveLoop
  iteration and package the resulting machine evaluator theorem.
- [x] Prove the corresponding fuel-indexed Nat MoveLoop iteration equation,
  composing arbitrary recursive step equations before termination.
- [x] Compose machine and Nat MoveLoop iteration into one evaluator contract
  exposing execution, relation preservation, and the Nat result.
- [x] Close the composed outer MoveLoop contract at machine termination,
  reducing the residual Nat loop to its terminal result.
- [x] Package the code-object branch with its machine evaluator, Nat
  recursive-step equation, and extended relation preservation.
- [x] Package the data-object branch with its nested MoveList evaluator, Nat
  recursive-step equation, and extended relation preservation.
- [x] Port executable bitmap filtering and reconstruction combinators for the
  root/bitmap collector wrappers.
- [x] Port Nat-executable bitmap bit-length, word decoding, and full bitmap
  lookup semantics.
- [x] Prove bitmap filtering and reconstruction remainder-length invariants.
- [x] Port fuel-bounded bitmap stack encoding and decoding with sentinel and
  malformed-input behavior.
- [x] Port location-preserving root traversal over encoded stack values with
  memory, index, destination, and condition threading.
- [x] Compose bitmap descriptor decoding, live-value filtering, root movement,
  and stack reconstruction for one frame.
- [x] Compose complete bitmap-managed stack root collection through encoding,
  value movement, and shape-preserving decoding.
- [x] Compose bitmap-managed root collection with the existing heap scan loop
  into a full collector result contract.
- [x] Prove that successful bitmap filtering and reconstruction leave the same
  stack suffix, using root-list length preservation.
- [x] Prove exact bitmap reconstruction partition lengths for emitted values
  and the untouched source remainder.
- [x] Prove the exact filter partition equation, accounting for values
  consumed by false bitmap bits.
- [x] Prove successful per-frame bitmap movement emits one reconstructed value
  per bitmap bit.
- [x] Expose the full-read and filter witnesses for every successful per-frame
  bitmap move, including its untouched remainder.
- [x] Prove that successful fuel-bounded bitmap decoding preserves stack
  length, including the public decoder wrapper.
- [x] Prove that successful bitmap root collection preserves the input stack
  length after encode, root movement, and decode.
- [x] Prove that successful full bitmap collection preserves stack length
  through the subsequent heap scan loop.
- [x] Prove the one-iteration pointer-free `MoveBitmap` transition, including
  descriptor shifting, scan-pointer advancement, and loop termination.
- [x] Expose exact `extCall` lowering with four fresh temporaries under
  successful expression compilation witnesses.
- [x] Prove the fuel-bounded full-Crepe `extCall` execution rule, threading
  decoded local arguments through the abstract FFI handler.
- [x] Expose call-handler lowering with return-slot allocation, exception-code
  lookup, and handler-result setup under successful context lookups.
- [x] Prove the full-Crepe caught-exception call rule, including callee memory
  transfer and handler execution under explicit evaluation witnesses.
- [x] Prove the complementary full-Crepe uncaught-exception call rule,
  preserving the callee memory in the propagated result.
- [x] Compose machine bitmap-root movement and heap scanning with the Nat
  full bitmap collector result under explicit root and loop witnesses.
- [x] Connect handler-aware Word-to-Stack lowering to the RISC-V image,
  including function-local handler labels and the reserved raise stub.
- [x] Exercise source `extCall` lowering through the StackLang/LabLang RISC-V
  image with a concrete service-table regression.
- [x] Exercise loop-aware Word FFI lowering through generated RISC-V control
  flow and observe a host update after a generated `break`.
- [x] Add explicit raised control outcomes and handler propagation to the
  executable StackLang machine evaluator.
- [x] Add an FFI-aware StackLang evaluator and one-step host-transition
  contract for nested control forms.
- [x] Add the corresponding FFI-aware bounded frame evaluator, preserving
  stack-frame checks and host transitions through calls and returns.
- [x] Package the complete bitmap-root/heap-scan collector as an explicit
  machine/Nat simulation witness and composition theorem.
- [x] Thread bitmap state through recursive call-handler lowering in the
  stateful Word-to-Stack compiler.
- [x] Thread bitmap state through both branches of conditional Word-to-Stack
  lowering, preserving distinct bitmap indices for branch-local allocations.
- [x] Prove bitmap-state length invariants for insertion, allocation, and
  constant-storage lowering.
- [x] Lift the bitmap-state length invariant through the complete recursive
  Word-to-Stack builder, including sequences, branches, loops, and handlers.
- [x] Prove the one-step FFI compatibility equation across register colouring,
  with the host transition retained as an explicit semantic hypothesis.
- [x] Compose generated FFI agreement through instruction-list sequencing and
  the call-aware Word compiler.
- [x] Expose the fuel-bounded normal-path sequence equation for the
  call-aware Word FFI evaluator, with a concrete FFI-then-return regression.
- [x] Expose true- and false-branch equations for the fuel-bounded FFI-aware
  Word conditional evaluator, with branch-selected FFI and return tests.
- [x] Expose the early-return sequence equation for the fuel-bounded FFI-aware
  Word evaluator, including a regression that skips a later FFI operation.
- [x] Add compositional StackLang FFI normal-sequence and raised-handler
  equations, with machine-level regressions.
- [x] Add the matching bounded FrameMachine FFI normal-sequence and
  raised-handler equations, with frame-state regressions.
- [x] Expose the bounded FrameMachine FFI returned-callee continuation
  equation, with a return-path FFI regression.
- [x] Lift the Word-to-Stack FFI ABI equation through the option-valued
  compiler entry point, with a spill-aware source-location regression.
- [x] Expose the state-threaded handler-call equation for the Word-to-Stack
  compiler, retaining the generated call shape and bitmap state.
- [x] Compose state-threaded handler-call lowering with bounded StackLang
  execution, retaining the bitmap state after argument moves and call code.
- [x] Expose the matching state-threaded no-handler call lowering equation,
  including return destinations and the unchanged bitmap state.
- [x] Compose state-threaded no-handler call lowering with bounded StackLang
  execution under explicit argument-move and return-call premises.
- [x] Cover zero-return direct calls, including their raw StackLang call code,
  in the state-threaded lowering and execution equations.
- [x] Expose state-threaded raise lowering and its bounded execution equation,
  retaining the runtime raise-stub execution as an explicit premise.
- [x] Expose state-threaded return lowering and its bounded execution equation,
  retaining the generated return-code execution as an explicit premise.
- [x] Add a reusable bounded execution bridge for successful state-threaded
  compilation, and cover `break`, `continue`, and `tick` lowering.
- [x] Expose the state-threaded Word-to-Stack FFI equation, retaining the
  bitmap accumulator across ABI argument lowering.
- [x] Compose state-threaded Word-to-Stack FFI lowering with bounded
  StackLang execution, retaining the bitmap state in the result relation.
- [x] Expose sequential state-threaded Word-to-Stack composition, including
  an allocating prefix followed by an FFI lowering.
- [x] Compose state-threaded sequential lowering with bounded StackLang
  execution, threading both the intermediate machine and bitmap states.
- [x] Expose state-threaded Word-to-Stack conditional composition, including
  condition materialization and branch-state threading.
- [x] Compose the nontrivial true branch of state-threaded conditional
  lowering with bounded StackLang execution after condition materialization.
- [x] Compose the corresponding false branch with bounded StackLang execution
  after condition materialization.
- [x] Expose state-threaded Word-to-Stack loop and MustTerminate composition.
- [x] Compose state-threaded loop lowering with bounded StackLang execution for
  a body that exits through `break`.
- [x] Expose normal and `continue` loop-iteration equations, retaining the
  recursive remainder evaluation as an explicit premise.
- [x] Compose state-threaded `MustTerminate` lowering with bounded StackLang
  execution.
- [x] Expose the state-threaded `Alloc` lowering pair, including its bitmap
  state transition before `StackAlloc` runtime replacement.
- [x] Expose the state-threaded `StoreConsts` lowering pair, including its
  bitmap table append before `StackAlloc` runtime replacement.
- [x] Compose state-threaded `Alloc` lowering with `StackAlloc` collector-call
  replacement and fresh-label accounting.
- [x] Compose state-threaded `StoreConsts` lowering with optional `StackAlloc`
  runtime replacement and fresh-label accounting.
- [x] Add a bitmap-carrying full-SSA spill pipeline and RISC-V entrypoint,
  retaining entry-inclusive parameter allocation and the generated bitmap
  artifact.
- [x] Link the full-SSA bitmap path with separate raise, StoreConsts, and
  simple-GC runtime sections, reserving their labels before compiled functions.
- [x] Expose source-order bitmap threading through the allocated Word-to-Stack
  function pipeline, including a compositional append equation.
- [x] Add abstract and bounded FFI loop-break simulation equations, with
  FFI-in-loop regressions.
- [x] Add the corresponding FFI loop-continue lowering equation and compiler
  shape regression.
- [x] Expose the abstract StackLang FFI returned-callee continuation equation,
  matching the bounded frame boundary.
- [x] Prove that a Word-to-Stack FFI argument move preserves every unrelated
  mapped variable, extending the per-destination FFI move contract.
- [x] Compose the four Word-to-Stack FFI argument moves into an ABI-register
  simulation theorem, preserving the original mapped source values.
- [x] Connect the generated Word-to-Stack FFI prefix to the FFI-aware
  StackLang evaluator, including fuel accounting and optional host results.
- [x] Rewrite the StackLang FFI host arguments to the original mapped Word
  values at the generated ABI boundary.
- [x] Exercise Word FFI lowering through StackRemove, LabLang, and the
  RISC-V backend, including ABI moves, return-label materialization, service
  selection, and ECALL emission.
- [x] Prove the Lab-level FFI-to-machine boundary: service materialization
  followed by ECALL agrees with the FFI host transition.
- [x] Lift the Lab FFI machine boundary through singleton section
  compilation, hiding label collection and code-shape normalization.
- [x] Lift the same boundary through singleton linked-program flattening,
  establishing the first program-level Lab-to-machine FFI simulation.
- [x] Compose a singleton Lab FFI call-and-return through
  `executeFunctionAtWithFfi`, including the caller's `x1` continuation.
- [ ] Port remaining handler/FFI lowering and a semantic simulation theorem
  for the complete pass.
- [x] Expose location-aware bitmap sequence compilation and evaluator
  contracts for the spill-aware Word-to-Stack boundary.
- [x] Expose location-aware bitmap handler-call and FFI lowering equations
  for the spill-aware Word-to-Stack correctness boundary.
- [x] Compose a raised StackLang callee with generated handler-call setup,
  argument transfer, exception-register write, and handler execution, with
  explicit fuel accounting.
- [x] Compose a normally returned StackLang callee with generated handler-call
  setup, argument transfer, and return continuation execution, with explicit
  fuel accounting.
- [x] Close the generated Word-to-Stack/StackRemove/LabLang FFI path with a
  machine-level RISC-V execution theorem, retaining the host transition as
  an explicit hypothesis.
- [x] Connect loop-aware FFI lowering to a machine-level RISC-V execution
  regression, including the ECALL host program-counter transition and break
  target.

## First implementation slice

The initial Lean commit implements stage 1's core in
`Flapjack/Language.lean`: shapes, polymorphic expressions, programs, function
and declaration syntax, `nestedSeq`, and shape sizing. The next slice should
port the nested-recursion measure and variable-use helpers, then the
static-checker data types and shape-context operations from
`panStaticScript.sml`, followed by a small executable checker. The static
data/context layer, expression variable-use helpers, Crepe IR, expression
lowering, and core structured statement lowering are now implemented; full
checking and semantic simulation remain the next increments.

## Verification workflow

- Lean: `lake build` from the repository root.
- HOL reference: `Holmake` in `cakeml/pancake` (and its relevant child
  directories).
- Keep commits small enough that a syntax/pass port and its proof obligations
  can be reviewed independently.
