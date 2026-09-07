import Flapjack.Test.Source
import Flapjack.Test.Backend
import Flapjack.Test.Correctness
import Flapjack.Test.Runtime
import Flapjack.Test.CollectorSemantics
import Flapjack.Test.SpillAllocation
import Flapjack.Test.CorrectnessBackend
import Flapjack.Test.OracleAllocator
import Flapjack.Test.AllocatorDriver
import Flapjack.Test.Heuristics
import Flapjack.Test.SpillCosts
import Flapjack.Test.HeuristicDriver
import Flapjack.Test.HeuristicPipeline
import Flapjack.Test.LinearScan
import Flapjack.Test.LinearScanSource
import Flapjack.Test.LinearScanDriver
import Flapjack.Test.AllocationModePipeline
import Flapjack.Test.CorrectnessCondition
import Flapjack.Test.CorrectnessCode
import Flapjack.Test.CorrectnessConditional
import Flapjack.Test.CorrectnessColour
import Flapjack.Test.FrameMachineCalls
import Flapjack.Test.StackMachineCalls
import Flapjack.Test.WordCallEquations
import Flapjack.Test.WordToStack.CompilerFfi
import Flapjack.Test.WordToStack.HandlerLowering
import Flapjack.Test.WordToStack.StatefulFfi
import Flapjack.Test.WordToStack.StatefulFfiCorrectness
import Flapjack.Test.WordToStack.StatefulSequence
import Flapjack.Test.WordToStack.StatefulIte
import Flapjack.Test.WordToStack.StatefulLoop
import Flapjack.Test.WordToStack.ControlLeaves
import Flapjack.Test.StatefulPipeline
import Flapjack.Test.CorrectnessFfiRiscVLoop
import Flapjack.Test.FullSsa
import Flapjack.Test.FullSsaPipeline

/-!
# Flapjack regression tests

The tests are split by compiler layer under `Flapjack.Test`; importing this
module runs the complete regression suite while keeping each file reviewable.
-/
