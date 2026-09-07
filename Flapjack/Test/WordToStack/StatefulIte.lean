import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for state-threaded conditional compilation.  The selected
    branch is a runtime concern, while bitmap allocation is threaded through
    both source branches during compilation. -/

namespace Flapjack.RiscV

def statefulIteConfig : WordStackConfig :=
  { locations := [(0, .register 4)]
    scratch := 31
    stackBase := 20 }

def statefulIteInitial : WordStackBitmapState :=
  { data := [4]
    length := 1 }

example :
    wordToStackProgNatWithBitmapBuilder statefulIteConfig (fun _ => [7])
      2 26 4 64 none statefulIteInitial
      (.ite .equal 0 (.imm 0)
        (.alloc 9 ([], [2])) .skip : WordProg Nat) =
      some (.ite .equal 4 (.imm 0)
          (.seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1)) .skip,
        { data := [4, 7]
          length := 2 }) := by
  apply wordToStackProgNatWithBitmapBuilder_ite
    (config := statefulIteConfig) (bitmapBuilder := fun _ => [7])
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulIteInitial)
    (state1 := { data := [4, 7], length := 2 })
    (finalState := { data := [4, 7], length := 2 })
    (operator := .equal) (condition := 0) (right := .imm 0)
    (thenBranch := (.alloc 9 ([], [2]) : WordProg Nat))
    (elseBranch := (.skip : WordProg Nat))
    (conditionPrelude := .skip) (conditionRegister := 4)
    (rightOperand := .imm 0)
    (thenCode := .seq (.seq (.const 26 2) (.stackStore 26 20)) (.alloc 1))
    (elseCode := .skip)
  · simp [statefulIteConfig, wordStackConditionOperands,
      wordStackReadRegister, wordStackLocation, lookupNatInfo,
      wordStackJoin]
  · simp [wordToStackProgNatWithBitmapBuilder,
      wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      wordStackInsertBitmap, wordStackJoin, wordStackOffset,
      statefulIteConfig, statefulIteInitial]
  · simp [wordToStackProgNatWithBitmapBuilder, wordToStackProgNat]

end Flapjack.RiscV
