import Flapjack.Pipeline

namespace Flapjack

example :
    wordAllocateContext [0, 1, 29, 30] =
      some { vars := [(0, 2), (1, 3), (29, 4), (30, 5)] } := by
  exact wordAllocateContext_examples

example :
    wordAllocateContext [0, 1, 2, 3] =
      some { vars := [(0, 2), (1, 3), (2, 4), (3, 5)] } := by
  exact wordAllocateContext_preserves_small_names

example :
    wordAllocateContextWithClashes [0, 1, 28]
        [(0, 1), (1, 28)] =
      some { vars := [(28, 2), (1, 3), (0, 2)] } := by
  exact wordAllocateContextWithClashes_examples

example :
    wordAllocateVarsWithClashes [0, 1] [(0, 1)] =
      some [(1, 3), (0, 2)] := by
  exact wordAllocateVarsWithClashes_safe_example

example :
    wordProgPreferenceEdges
        (.seq (.assign 4 (.var 0)) (.locValue 5 4) : WordProg Nat) =
      [(4, 0), (5, 4)] := by
  simp [wordProgPreferenceEdges]

example :
    wordAllocateVarsWithClashesAndPreferences [0, 4] [] [(4, 0)] =
      some [(4, 2), (0, 2)] := by
  rfl

example :
    wordAllocateVarsWithClashesAndPreferences [0, 4] [(0, 4)] [(4, 0)] =
      some [(4, 6), (0, 2)] := by
  rfl

example (slots : List Nat) (edges preferences : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashesAndPreferences slots edges preferences =
      some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  exact wordAllocateVarsWithClashesAndPreferences_sound slots edges preferences
    colouring hcolouring

example :
    wordInstVars (.arith (.addCarry 1 2 3 4 5)) = [3, 4, 5, 1, 2] := by
  exact wordInstVars_addCarry

example :
    wordAllocateLinearInstructions
      [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      some { vars := [(6, 8), (5, 7), (1, 3), (0, 2), (4, 6), (3, 5), (2, 4)] } := by
  exact wordAllocateLinearInstructions_example

example :
    wordProgClashAnalysis
        ((.seq (.assign 0 (.var 1)) (.assign 2 (.var 0))) : WordProg α) [] =
      ([1], []) := by
  exact wordProgClashAnalysis_seq

example :
    wordProgClashAnalysis
        ((.ite .equal 0 (.reg 1)
          (.assign 2 (.var 0)) (.assign 3 (.var 0))) : WordProg α) [] =
      ([0, 1], []) := by
  exact wordProgClashAnalysis_ite

example :
    (2, 4) ∈ (wordProgClashAnalysis
      ((.call none none []
        (some (9, (.assign 2 (.var 3)), 0, 0)) : WordProg Nat))
      [4]).2 := by
  native_decide

example :
    (9, 3) ∈ (wordProgClashAnalysis
      ((.call none none []
        (some (9, (.assign 2 (.var 3)), 0, 0)) : WordProg Nat))
      [4]).2 := by
  native_decide

example :
    9 ∈ (wordProgClashAnalysis
      ((.call none none []
        (some (9, (.assign 2 (.var 3)), 0, 0)) : WordProg Nat))
      [4]).1 := by
  native_decide

example :
    3 ∈ (wordProgClashAnalysis
      ((.call none none []
        (some (9, (.assign 2 (.var 3)), 0, 0)) : WordProg Nat))
      [4]).1 := by
  native_decide

example :
    (wordAllocateSsaProgram
      ({ current := [], next := 10 } : WordSsaState)
      ((.ite .equal 0 (.reg 0)
        (.assign 1 (.var 0)) (.assign 1 (.var 0))) : WordProg Nat)).isSome =
      true := by
  native_decide

example (slots : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  exact wordAllocateVarsWithClashes_sound slots edges colouring hcolouring

example (slots : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring)
    (name : Nat) (hname : name ∈ slots.eraseDups) :
    ∃ register,
      lookupNatInfo name colouring = some register ∧
        wordRegisterIsAllocatable register = true := by
  exact wordAllocateVarsWithClashes_maps_slots slots edges colouring hcolouring
    name hname

example : 29 ∉ wordAllocatableRegisters := by
  decide

example : 28 ∉ wordAllocatableRegisters := by
  decide

example : 27 ∉ wordAllocatableRegisters := by
  decide

example : wordRegisterIsReserved 28 = true := by
  decide

example : wordRegisterIsReserved 27 = true := by
  decide

example : wordRegisterIsReserved 29 = true := by
  decide

end Flapjack
