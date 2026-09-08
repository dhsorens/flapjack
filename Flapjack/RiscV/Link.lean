import Flapjack.RiscV.Calls
import Flapjack.RiscV.Ffi

/-!
The first RISC-V linker layer for Flapjack function artifacts. Function labels
are assigned byte addresses from the emitted instruction lengths; unresolved
artifacts fail explicitly. The resulting entry table feeds
`wordCallToRiscVLabel`, which resolves a Word call target before selecting its
RISC-V sequence.
-/

namespace Flapjack.RiscV

def linkRiscVFunctionsAt [NeZero width] (start : Word width) (offset : Nat) :
    List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) →
      Option (List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)))
  | [] => some []
  | (label, parameters, some (code, returns)) :: functions => do
      let rest ← linkRiscVFunctionsAt start (offset + 4 * code.length) functions
      pure ((label, start + BitVec.ofNat width offset, parameters, code, returns) :: rest)
  | _ => none

def linkRiscVFunctions [NeZero width]
    (start : Word width)
    (functions : List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32)))) :=
  linkRiscVFunctionsAt start 0 functions

def linkRiscVCodeLength [NeZero width] :
    List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) → Nat
  | [] => 0
  | (_, _, some (code, _)) :: functions => code.length + linkRiscVCodeLength functions
  | _ :: functions => linkRiscVCodeLength functions

theorem linkRiscVFunctionsAt_append_resolved [NeZero width]
    (start : Word width) (offset : Nat)
    (functionsPrefix suffix :
      List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))))
    (hresolved : ∀ item ∈ functionsPrefix, ∃ code returns, item.2.2 = some (code, returns)) :
    linkRiscVFunctionsAt start offset (functionsPrefix ++ suffix) = (do
      let left ← linkRiscVFunctionsAt start offset functionsPrefix
      let right ← linkRiscVFunctionsAt
        start (offset + 4 * linkRiscVCodeLength functionsPrefix) suffix
      pure (left ++ right)) := by
  induction functionsPrefix generalizing offset with
  | nil => simp [linkRiscVCodeLength, linkRiscVFunctionsAt]
  | cons item functionsPrefix ih =>
      rcases item with ⟨label, parameters, artifact⟩
      cases artifact with
      | none =>
          have h := hresolved (label, parameters, none) (by simp)
          simp at h
      | some artifact =>
          rcases artifact with ⟨code, returns⟩
          have htail : ∀ item ∈ functionsPrefix, ∃ code returns, item.2.2 = some (code, returns) := by
            intro item hitem
            exact hresolved item (by simp [hitem])
          simp only [linkRiscVFunctionsAt, linkRiscVCodeLength, List.cons_append]
          rw [ih (offset := offset + 4 * code.length) htail]
          generalize hlinked :
            linkRiscVFunctionsAt start (offset + 4 * code.length) functionsPrefix = linkedPrefix
          cases linkedPrefix <;> simp [Nat.add_assoc, Nat.mul_add]
          generalize hrest :
            linkRiscVFunctionsAt
              start (offset + (4 * code.length + 4 * linkRiscVCodeLength functionsPrefix))
              suffix = linkedSuffix
          cases linkedSuffix <;> simp

def lookupLinkedEntry [NeZero width]
    (label : Nat)
    (functions : List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32))) :
    Option (Word width) :=
  match functions with
  | [] => none
  | (candidate, entry, _, _, _) :: functions =>
      if label == candidate then some entry else lookupLinkedEntry label functions

theorem lookupLinkedEntry_linkRiscVFunctionsAt_head [NeZero width]
    (start : Word width) (offset label : Nat) (parameters : List Nat)
    (code : List (Instruction width)) (returns : List (Fin 32))
    (functions :
      List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))))
    (linked :
      List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)))
    (hrest : linkRiscVFunctionsAt start (offset + 4 * code.length) functions =
      some linked) :
    (linkRiscVFunctionsAt start offset
      ((label, parameters, some (code, returns)) :: functions)).bind
        (lookupLinkedEntry label) =
      some (start + BitVec.ofNat width offset) := by
  simp [linkRiscVFunctionsAt, hrest, lookupLinkedEntry]

def wordCallToRiscVLabel [NeZero width]
    (functions : List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)))
    (label : Nat) (parameters returns arguments destinations : List Nat) :
    Option (List (Instruction width)) := do
  let entry ← lookupLinkedEntry label functions
  wordCallToRiscV entry parameters returns arguments destinations

def wordFunctionReturnNames [NeZero width] :
    WordProg (Word width) → Option (List Nat)
  | .return _ values => some values
  | .seq first second =>
      match wordFunctionReturnNames first with
      | some values => some values
      | none => wordFunctionReturnNames second
  | .ite _ _ _ thenBranch elseBranch =>
      match wordFunctionReturnNames thenBranch, wordFunctionReturnNames elseBranch with
      | some thenReturns, some elseReturns =>
          if thenReturns == elseReturns then some thenReturns else none
      | _, _ => none
  | .loop _ body _ =>
      match wordFunctionReturnNames body with
      | some values => some values
      | none => some []
  | _ => none
  termination_by program => sizeOf program

def lookupWordFunctionBody [NeZero width] (label : Nat) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (WordProg (Word width))
  | [] => none
  | (candidate, _, body) :: functions =>
      if label == candidate then some body
      else lookupWordFunctionBody label functions

def wordFunctionReturnNamesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
    WordProg (Word width) → Option (List Nat)
  | .call (some ([], _)) (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .call none (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .call (some (_, _)) _ _ none => some []
  | .seq first second =>
      match wordFunctionReturnNamesWithCalls functions first with
      | some values => some values
      | none => wordFunctionReturnNamesWithCalls functions second
  | .ite _ _ _ thenBranch elseBranch => do
      let thenReturns ← wordFunctionReturnNamesWithCalls functions thenBranch
      let elseReturns ← wordFunctionReturnNamesWithCalls functions elseBranch
      if thenReturns == elseReturns then some thenReturns else none
  | .loop _ body _ =>
      match wordFunctionReturnNamesWithCalls functions body with
      | some values => some values
      | none => some []
  | .return _ values => some values
  | _ => none
termination_by program => sizeOf program

def compileLinkedWordFunction [NeZero width]
    (context : WordCallContext width)
    (function : Nat × List Nat × WordProg (Word width)) :
    Option (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) := do
  let (label, parameters, body) := function
  let (code, returns) ← wordFunctionToRiscVWithCallsAndLoops context body
  pure (label, parameters, some (code ++ [.jalr 0 1 0], returns))

theorem compileLinkedWordFunction_shape [NeZero width]
    (context : WordCallContext width)
    (label : Nat) (parameters : List Nat) (body : WordProg (Word width))
    (code : List (Instruction width)) (returns : List (Fin 32))
    (hcode : wordFunctionToRiscVWithCallsAndLoops context body = some (code, returns)) :
    compileLinkedWordFunction context (label, parameters, body) =
      some (label, parameters, some (code ++ [.jalr 0 1 0], returns)) := by
  simp [compileLinkedWordFunction, hcode]

def wordFunctionTargetSignaturesAux [NeZero width]
    (allFunctions : List (Nat × List Nat × WordProg (Word width))) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNamesWithCalls allFunctions body
      let rest ← wordFunctionTargetSignaturesAux allFunctions functions
      pure ((label, 0, parameters, returns) :: rest)

def wordFunctionTargetSignaturesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
      Option (List (Nat × Word width × List Nat × List Nat)) :=
  wordFunctionTargetSignaturesAux functions functions

def wordFunctionTargetSignatures [NeZero width] :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNames body
      let rest ← wordFunctionTargetSignatures functions
      pure ((label, 0, parameters, returns) :: rest)

def linkWordFunctions [NeZero width]
    (start : Word width)
    (functions : List (Nat × List Nat × WordProg (Word width))) := do
  let signatures ← wordFunctionTargetSignaturesWithCalls functions
  let provisionalContext : WordCallContext width := { targets := signatures }
  let provisional ← functions.mapM (compileLinkedWordFunction provisionalContext)
  let linked :
      List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) ←
    linkRiscVFunctions start provisional
  let targets : List (Nat × Word width × List Nat × List Nat) :=
    linked.map (fun (item :
        Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) =>
      let (label, entry, parameters, _code, returns) := item
      (label, entry, parameters, List.map (fun register : Fin 32 => register.val) returns))
  let context : WordCallContext width := { targets := targets }
  let actual ← functions.mapM (compileLinkedWordFunction context)
  linkRiscVFunctions start actual

/-!
Linking for the FFI-aware selector mirrors the ordinary call-aware linker but
retains the service table throughout both provisional and final compilation.
This keeps function entry addresses stable while allowing an FFI operation in
any supported straight-line or loop body.
-/
def compileLinkedWordFunctionWithFfi [NeZero width]
    (context : WordCallFfiContext width)
    (function : Nat × List Nat × WordProg (Word width)) :
    Option (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) := do
  let (label, parameters, body) := function
  let (code, returns) ← wordFunctionToRiscVWithCallsAndFfiAndLoops context body
  pure (label, parameters, some (code ++ [.jalr 0 1 0], returns))

theorem compileLinkedWordFunctionWithFfi_shape [NeZero width]
    (context : WordCallFfiContext width)
    (label : Nat) (parameters : List Nat) (body : WordProg (Word width))
    (code : List (Instruction width)) (returns : List (Fin 32))
    (hcode : wordFunctionToRiscVWithCallsAndFfiAndLoops context body =
      some (code, returns)) :
    compileLinkedWordFunctionWithFfi context (label, parameters, body) =
      some (label, parameters, some (code ++ [.jalr 0 1 0], returns)) := by
  simp [compileLinkedWordFunctionWithFfi, hcode]

def linkWordFunctionsWithFfi [NeZero width]
    (start : Word width) (services : List (FunName × Nat))
    (functions : List (Nat × List Nat × WordProg (Word width))) := do
  let signatures ← wordFunctionTargetSignaturesWithCalls functions
  let provisionalContext : WordCallFfiContext width :=
    { targets := signatures, services := services }
  let provisional ← functions.mapM (compileLinkedWordFunctionWithFfi provisionalContext)
  let linked :
      List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) ←
    linkRiscVFunctions start provisional
  let targets : List (Nat × Word width × List Nat × List Nat) :=
    linked.map (fun (item :
        Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) =>
      let (label, entry, parameters, _code, returns) := item
      (label, entry, parameters, List.map (fun register : Fin 32 => register.val) returns))
  let context : WordCallFfiContext width :=
    { targets := targets, services := services }
  let actual ← functions.mapM (compileLinkedWordFunctionWithFfi context)
  linkRiscVFunctions start actual

theorem linkWordFunctionsWithFfi_empty [NeZero width]
    (start : Word width) (services : List (FunName × Nat)) :
    linkWordFunctionsWithFfi start services [] = some [] := by
  rfl

theorem wordFunctionReturnNames_return [NeZero width] (values : List Nat) :
    wordFunctionReturnNames (.return 0 values : WordProg (Word width)) = some values := by
  simp [wordFunctionReturnNames]

theorem linkWordFunctions_empty [NeZero width] (start : Word width) :
    linkWordFunctions start [] = some [] := by
  rfl

theorem linkRiscVFunctions_empty [NeZero width] (start : Word width) :
    linkRiscVFunctions start [] = some [] := by
  rfl

end Flapjack.RiscV
