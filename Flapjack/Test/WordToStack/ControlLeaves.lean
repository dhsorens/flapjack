import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression coverage for state-threaded non-allocating control leaves. -/

namespace Flapjack.RiscV

def controlLeafConfig : WordStackConfig :=
  { locations := [], scratch := 31, stackBase := 20 }

def controlLeafState : WordStackBitmapState :=
  { data := [3, 5], length := 2 }

example :
    wordToStackProgNatWithBitmapBuilder controlLeafConfig (fun _ => [])
      2 26 4 64 none controlLeafState
      (.break 7) = some (.break 7, controlLeafState) := by
  exact wordToStackProgNatWithBitmapBuilder_break
    controlLeafConfig (fun _ => []) 2 26 4 64 none controlLeafState 7

example :
    wordToStackProgNatWithBitmapBuilder controlLeafConfig (fun _ => [])
      2 26 4 64 none controlLeafState
      (.continue 11) = some (.continue 11, controlLeafState) := by
  exact wordToStackProgNatWithBitmapBuilder_continue
    controlLeafConfig (fun _ => []) 2 26 4 64 none controlLeafState 11

example :
    wordToStackProgNatWithBitmapBuilder controlLeafConfig (fun _ => [])
      2 26 4 64 none controlLeafState
      .tick = some (.tick, controlLeafState) := by
  exact wordToStackProgNatWithBitmapBuilder_tick
    controlLeafConfig (fun _ => []) 2 26 4 64 none controlLeafState

end Flapjack.RiscV
