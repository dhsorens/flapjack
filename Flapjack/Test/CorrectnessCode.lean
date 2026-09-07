import Flapjack.RiscV.CorrectnessCode

namespace Flapjack.Test.CorrectnessCode

open Flapjack Flapjack.RiscV

/- The branch selector is exercised for both a comparison and a bit test. -/
example [NeZero width] (offset : Word width) :
    riscVBranchFalseInstruction .equal 1 2 offset =
      .branchNe 1 2 offset := by
  rfl

example [NeZero width] (offset : Word width) :
    riscVBranchFalseInstruction .notTest 1 2 offset =
      .branchEq 1 2 offset := by
  rfl

end Flapjack.Test.CorrectnessCode
