import Flapjack.Language
import Flapjack.Ffi
import Flapjack.LoopFfi
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Pipeline
import Flapjack.Correctness
import Flapjack.FlatCorrectness
import Flapjack.Tests
import Flapjack.Static
import Flapjack.Crepe
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.CrepeSemantics
import Flapjack.CrepeRuntime
import Flapjack.CrepeCorrectness
import Flapjack.PanValues
import Flapjack.PanMemory
import Flapjack.RiscV.Model
import Flapjack.RiscV.PanMemory
import Flapjack.RiscV.PanSemantics
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.AllocatorCorrectness
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.Backend
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Calls
import Flapjack.RiscV.CorrectnessFfi
import Flapjack.RiscV.CorrectnessLoop
import Flapjack.RiscV.CorrectnessFfiMachine
import Flapjack.RiscV.CorrectnessStack
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.ExactFfi
import Flapjack.RiscV.CorrectnessExactFfi
import Flapjack.RiscV.Link
import Flapjack.WordSemantics
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.LoopSemantics
import Flapjack.Word
import Flapjack.Stack
import Flapjack.StackAlloc
import Flapjack.StackAlloc.Runtime
import Flapjack.StackAlloc.Machine
import Flapjack.StackAlloc.FrameMachine
import Flapjack.StackAlloc.CollectorSemantics
import Flapjack.StackAlloc.Correctness
import Flapjack.StackAlloc.BitmapSemantics
import Flapjack.StackRemove
import Flapjack.Lab
import Flapjack.RiscV.Lab

/-!
# Flapjack in Lean

The library currently contains the first Lean representation of Flapjack's
front-end language. The source of truth used while porting is the CakeML HOL
development in `cakeml/pancake`.
-/
