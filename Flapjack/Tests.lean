import Flapjack.Test.Source
import Flapjack.Test.Backend
import Flapjack.Test.Correctness
import Flapjack.Test.Runtime
import Flapjack.Test.CollectorSemantics
import Flapjack.Test.SpillAllocation
import Flapjack.Test.CorrectnessBackend
import Flapjack.Test.OracleAllocator
import Flapjack.Test.AllocatorDriver
import Flapjack.Test.CorrectnessCondition
import Flapjack.Test.CorrectnessCode
import Flapjack.Test.CorrectnessConditional

/-!
# Flapjack regression tests

The tests are split by compiler layer under `Flapjack.Test`; importing this
module runs the complete regression suite while keeping each file reviewable.
-/
