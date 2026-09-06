import Flapjack.RiscV.Correctness
import Flapjack.RiscV.CorrectnessFfi
import Flapjack.Test.Structured
import Flapjack.Test.CorrectnessFfi
import Flapjack.Test.CorrectnessCalls
import Flapjack.Test.CorrectnessMemory
import Flapjack.Test.CorrectnessPrimitive
import Flapjack.Test.CorrectnessControl
import Flapjack.Test.CorrectnessLoopHandlers
import Flapjack.Test.CorrectnessLoopControl
import Flapjack.Test.CorrectnessLoopCalls
import Flapjack.Test.CorrectnessLoopCallHandlers
import Flapjack.Test.CorrectnessLoopRepeat
import Flapjack.Test.WordLoopHandlers
import Flapjack.Test.CorrectnessFfiMachine
import Flapjack.Test.CorrectnessTarget
import Flapjack.Test.ExactFfi
import Flapjack.Test.CorrectnessExactFfi

/-!
# Compiler-correctness regression tests

The theorem-level tests are grouped separately from executable backend shape
tests.  Keeping this boundary explicit makes it easier to build and review
the correctness port incrementally.
-/
