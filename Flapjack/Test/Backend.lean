import Flapjack.Test.RiscVMemory
import Flapjack.Test.RiscV
import Flapjack.Test.Pipeline
import Flapjack.Test.Calls
import Flapjack.Test.Loops
import Flapjack.Test.Primitive
import Flapjack.Test.Allocator
import Flapjack.Test.AllocatorFunction
import Flapjack.Test.AllocatorCalls
import Flapjack.Test.AllocatorCorrectness
import Flapjack.Test.AllocatorRegAlloc
import Flapjack.Test.MustTerminate
import Flapjack.Test.WordToStack
import Flapjack.Test.ParallelMove
import Flapjack.Test.Stack
import Flapjack.Test.Lab
import Flapjack.Test.RiscVLab
import Flapjack.Test.StackRemove
import Flapjack.Test.StackRemoveCorrectness

/-!
# Backend regression tests

This aggregate covers the executable RISC-V, allocator, StackLang, and
Word-to-Stack checks.
-/
