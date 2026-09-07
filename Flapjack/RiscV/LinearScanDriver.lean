import Flapjack.RiscV.LinearScan

/-!
# Function-level linear-scan allocation

This is the function boundary corresponding to CakeML's
`linear_scan_reg_alloc` path.  The Word function is SSA-renamed first, the
formal-parameter set is retained in the clash tree, and the checked
program-level linear allocator supplies the locations consumed by
`word_to_stack`.
-/

namespace Flapjack

def wordAllocateLinearScanFunction (parameters : List Nat)
    (program : WordProg α) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordLinearScanState × WordProg α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let moves := wordPreferenceMoves
    (wordProgPreferenceEdges renamedProgram)
  (wordLinearScanAllocateClashTreeChecked colours stackStart tree forced moves).map
    (fun allocation =>
      (state, renamedParameters, allocation, renamedProgram))

end Flapjack
