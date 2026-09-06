import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

/-! CakeML's `MustTerminate` is a semantic wrapper: all lowerings preserve
the nested Word program while keeping the constructor visible to later
passes. -/

example :
    wordProgReadVars
        (.mustTerminate (.assign 3 (.var 2)) : WordProg Nat) = [2] := by
  simp [wordProgReadVars, wordExpReadVars]

example :
    wordApplyColour (fun name => name + 4)
        (.mustTerminate (.assign 3 (.var 2)) : WordProg Nat) =
      .mustTerminate (.assign 7 (.var 6)) := by
  simp [wordApplyColour, wordApplyColourExp]

example [NeZero 64] (state : State 64) (program : WordProg (Word 64)) :
    RiscV.evalWordProg state (.mustTerminate program) =
      RiscV.evalWordProg state program := by
  simp [RiscV.evalWordProg]

example [BEq Nat] (config : WordStackConfig) (program : WordProg Nat) :
    wordToStackProgNat config (.mustTerminate program) =
      wordToStackProgNat config program := by
  simp [wordToStackProgNat]

end Flapjack
