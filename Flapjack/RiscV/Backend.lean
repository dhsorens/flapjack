import Flapjack.Word
import Flapjack.RiscV.Model

/-!
The first executable Word-to-RISC-V instruction-selection slice.

This is intentionally a partial compiler. It covers the Word fragment made of
`skip`, assignments, sequencing, equality/order/bit-test conditionals,
constants, register reads, binary arithmetic, shifts, and selected memory
operations. Zero conditions use the architectural x0 register; nonzero
immediate conditions materialize their operand in the reserved x31 scratch
register. Bit tests use either `AND` or `ANDI` and branch on the resulting
temporary. The option-valued interface makes the current boundary explicit
while the remaining Word instructions are ported.
-/

namespace Flapjack.RiscV

def registerOfNat (name : Nat) : Option (Fin 32) :=
  if h : name < 32 then some ⟨name, h⟩ else none

@[simp] theorem registerOfNat_zero : registerOfNat 0 = some 0 := by
  simp [registerOfNat]

theorem registerOfNat_some_lt {name : Nat} {register : Fin 32}
    (h : registerOfNat name = some register) : name < 32 := by
  simp only [registerOfNat] at h
  split at h <;> simp_all

theorem registerOfNat_injective {left right : Nat}
    {leftRegister rightRegister : Fin 32}
    (hleft : registerOfNat left = some leftRegister)
    (hright : registerOfNat right = some rightRegister)
    (hsame : leftRegister = rightRegister) : left = right := by
  have hleft_lt := registerOfNat_some_lt hleft
  have hright_lt := registerOfNat_some_lt hright
  have hleft_fin :
      (⟨left, hleft_lt⟩ : Fin 32) = leftRegister := by
    have h := hleft
    simp [registerOfNat, hleft_lt] at h
    exact h
  have hright_fin :
      (⟨right, hright_lt⟩ : Fin 32) = rightRegister := by
    have h := hright
    simp [registerOfNat, hright_lt] at h
    exact h
  have hfin :
      (⟨left, hleft_lt⟩ : Fin 32) = (⟨right, hright_lt⟩ : Fin 32) :=
    hleft_fin.trans (hsame.trans hright_fin.symm)
  exact congrArg Fin.val hfin

def wordExpToInstruction [NeZero width] (destination : Nat) :
    WordExp (Word width) → Option (Instruction width)
  | .const value => do
      let destination ← registerOfNat destination
      pure (.addi destination 0 value)
  | .var source => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.addi destination source 0)
  | .op operator [.const left, .const right] => do
      let destination ← registerOfNat destination
      let value := match operator with
        | .add => left + right
        | .sub => left - right
        | .and => left &&& right
        | .or => left ||| right
        | .xor => left ^^^ right
      pure (.addi destination 0 value)
  | .op .add [.var source, .const value] => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.addi destination source value)
  | .op .sub [.var source, .const value] => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.addi destination source (0 - value))
  | .op .and [.var source, .const value] => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.andi destination source value)
  | .op .or [.var source, .const value] => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.ori destination source value)
  | .op .xor [.var source, .const value] => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      pure (.xori destination source value)
  | .op operator [.var left, .var right] => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (match operator with
        | .add => .add destination left right
        | .sub => .sub destination left right
        | .and => .and destination left right
        | .or => .or destination left right
        | .xor => .xor destination left right)
  | .shift operator (.var left) (.var right) => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      let right ← registerOfNat right
      match operator with
      | .lsl => pure (.sll destination left right)
      | .lsr => pure (.srl destination left right)
      | .asr => pure (.sra destination left right)
      | .ror => none
  | .shift operator (.var left) (.const amount) => do
      let destination ← registerOfNat destination
      let left ← registerOfNat left
      match operator with
      | .lsl => pure (.slli destination left amount)
      | .lsr => pure (.srli destination left amount)
      | .asr => pure (.srai destination left amount)
      | .ror => none
  | _ => none

@[simp] def wordExpToInstructions [NeZero width] (destination : Nat) :
    WordExp (Word width) → Option (List (Instruction width))
  | .load address => do
      if destination == 31 then none
      else
        let addressInstructions ← wordExpToInstructions 31 address
        let destination ← registerOfNat destination
        pure (addressInstructions ++ [.loadWord destination 31])
  | .shift .ror (.var left) (.var right) => do
      if destination == 31 || left == 31 || right == 31 then none
      else
        let destination ← registerOfNat destination
        let left ← registerOfNat left
        let right ← registerOfNat right
        pure [.ori 31 0 (BitVec.ofNat width width),
          .sub 31 31 right, .sll 31 left 31, .srl destination left right,
          .or destination destination 31]
  | .shift .ror (.var left) (.const amount) => do
      if destination == 31 || left == 31 then none
      else
        let destination ← registerOfNat destination
        let left ← registerOfNat left
        let amount := shiftAmount amount
        pure [.srli 31 left amount,
          .slli destination left (BitVec.ofNat width ((width - amount) % width)),
          .or destination destination 31]
  | expression => (wordExpToInstruction destination expression).map (fun instruction => [instruction])

def wordArithToInstruction [NeZero width] :
    WordArith → Option (Instruction width)
  | .longMul _destinationLeft _destinationRight _sourceLeft _sourceRight =>
      none
  | .longDiv _ _ _ _ _ => none
  | .addCarry _ _ _ _ _ => none
  | .div destination dividend divisor => do
      let destination ← registerOfNat destination
      let dividend ← registerOfNat dividend
      let divisor ← registerOfNat divisor
      pure (.divU destination dividend divisor)

def wordArithToInstructions [NeZero width] :
    WordArith → Option (List (Instruction width))
  | .longMul destinationLeft destinationRight sourceLeft sourceRight => do
      if destinationLeft = sourceLeft || destinationLeft = sourceRight then
        none
      else
        let destinationLeft ← registerOfNat destinationLeft
        let destinationRight ← registerOfNat destinationRight
        let sourceLeft ← registerOfNat sourceLeft
        let sourceRight ← registerOfNat sourceRight
        pure [.mulHU destinationLeft sourceLeft sourceRight,
          .mul destinationRight sourceLeft sourceRight]
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn => do
      if [destination, resultCarry, sourceLeft, sourceRight, carryIn].any (· == 31) then
        none
      else
        let destination ← registerOfNat destination
        let resultCarry ← registerOfNat resultCarry
        let sourceLeft ← registerOfNat sourceLeft
        let sourceRight ← registerOfNat sourceRight
        let carryIn ← registerOfNat carryIn
        pure [
          .sltu 31 0 carryIn,
          .add destination sourceLeft sourceRight,
          .sltu resultCarry destination sourceRight,
          .add destination destination 31,
          .sltu 31 destination 31,
          .or resultCarry resultCarry 31]
  | operation => (wordArithToInstruction operation).map (fun instruction => [instruction])

def wordInstToInstruction [NeZero width] :
    WordInst → Option (Instruction width)
  | .arith operation => wordArithToInstruction operation
  | .mem .load8 destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.loadByte destination address)
  | .mem .store8 source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.storeByte source address)
  | .mem .load16 destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.loadHalf destination address)
  | .mem .store16 source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.storeHalf source address)
  | .mem .load32 destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.load32 destination address)
  | .mem .store32 source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.store32 source address)
  | .mem .load destination address => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (.loadWord destination address)
  | .mem .store source address => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (.storeWord source address)

def executeInstructions [NeZero width] (state : State width) :
    List (Instruction width) → State width
  | [] => state
  | instruction :: instructions =>
      executeInstructions (execute state instruction) instructions

@[simp] theorem executeInstructions_single [NeZero width] (state : State width)
    (instruction : Instruction width) :
    executeInstructions state [instruction] = execute state instruction := by
  rfl

def wordShareInstToInstructions [NeZero width] (operator : WordMemOp)
    (name : Nat) : WordExp (Word width) → Option (List (Instruction width))
  | .var address => do
      let instruction ← wordInstToInstruction (.mem operator name address)
      pure [instruction]
  | expression => do
      if name == 31 then none
      else
        let address ← wordExpToInstructions 31 expression
        let instruction ← wordInstToInstruction (.mem operator name 31)
        pure (address ++ [instruction])

def evalWordShareInst [NeZero width] (state : State width)
    (operator : WordMemOp) (name : Nat) (address : WordExp (Word width)) :
    Option (State width) := do
  let instructions ← wordShareInstToInstructions operator name address
  pure (executeInstructions state instructions)

def wordStoreToInstructions [NeZero width] (address : WordExp (Word width))
    (value : Nat) : Option (List (Instruction width)) :=
  wordShareInstToInstructions .store value address

def wordMoveRegisterDestinations (moves : List (Nat × Nat)) : List Nat :=
  moves.map (fun move => move.1)

def wordMoveRegisterRemoveDestination (destination : Nat) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.filter (fun move => move.1 != destination)

def wordMoveRegisterReady (destinations : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | move :: moves =>
      if move.2 ∉ destinations then
        some move
      else
        wordMoveRegisterReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordMoveToInstructionsAux [NeZero width] :
    Nat → List (Nat × Nat) → Option (List (Instruction width))
  | 0, _ => none
  | fuel + 1, moves =>
      let destinations := wordMoveRegisterDestinations moves
      if moves.any (fun move => move.1 == 31 || move.2 == 31) then
        none
      else if !destinations.Nodup then
        none
      else if moves.isEmpty then
        some []
      else
        match wordMoveRegisterReady destinations moves with
        | some (destination, source) => do
            let first ← wordExpToInstructions destination (.var source)
            let rest ← wordMoveToInstructionsAux fuel
              (wordMoveRegisterRemoveDestination destination moves)
            pure (first ++ rest)
        | none =>
            match moves with
            | [] => some []
            | (destination, source) :: _ => do
                let save ← wordExpToInstructions 31 (.var source)
                let rest ← wordMoveToInstructionsAux fuel
                  (wordMoveRegisterRemoveDestination destination moves)
                let restore ← wordExpToInstructions destination (.var 31)
                pure (save ++ rest ++ restore)

def wordMoveToInstructions [NeZero width] (moves : List (Nat × Nat)) :
    Option (List (Instruction width)) :=
  wordMoveToInstructionsAux (moves.length + 1) moves

@[simp] def wordConditionOperands [NeZero width] (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width)) :
    Option (Fin 32 × Fin 32 × List (Instruction width)) := do
  let condition ← registerOfNat condition
  match rightValue with
  | .reg right =>
      let right ← registerOfNat right
      match operator with
      | .test | .notTest => pure (condition, 0, [.and condition condition right])
      | _ => pure (condition, right, [])
  | .imm value =>
      if value == 0 then
        match operator with
        | .test | .notTest => pure (condition, 0, [.and condition condition 0])
        | _ => pure (condition, 0, [])
      else if condition == 31 then
        none
      else
        match operator with
        | .test | .notTest =>
            pure (31, 0, [.andi 31 condition value])
        | _ =>
            pure (condition, 31, [.ori 31 0 value])

def wordProgToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width))
  | .skip => some []
  | .move _ moves => wordMoveToInstructions moves
  | .assign name value =>
      wordExpToInstructions name value
  | .store address value =>
      wordStoreToInstructions address value
  | .shareInst operator name address =>
      wordShareInstToInstructions operator name address
  | .locValue destination source =>
      wordExpToInstructions destination (.var source)
  | .inst (.arith operation) => wordArithToInstructions operation
  | .inst instruction =>
      (wordInstToInstruction instruction).map (fun instruction => [instruction])
  | .seq first second => do
      let first ← wordProgToRiscV first
      let second ← wordProgToRiscV second
      pure (first ++ second)
  | .tick => some [.addi 0 0 0]
  | .ite operator condition rightValue thenBranch elseBranch => do
      let (branchLeft, right, prelude) ←
        wordConditionOperands operator condition rightValue
      let thenCode ← wordProgToRiscV thenBranch
      let elseCode ← wordProgToRiscV elseBranch
      let falseOffset : Word width :=
        BitVec.ofNat width (8 + 4 * thenCode.length)
      let endOffset : Word width :=
        BitVec.ofNat width (4 + 4 * elseCode.length)
      let branchFalse ← match operator with
        | .equal => pure (.branchNe branchLeft right falseOffset)
        | .notEqual => pure (.branchEq branchLeft right falseOffset)
        | .less => pure (.branchGe branchLeft right falseOffset)
        | .notLess => pure (.branchLt branchLeft right falseOffset)
        | .lower => pure (.branchGeU branchLeft right falseOffset)
        | .notLower => pure (.branchLtU branchLeft right falseOffset)
        | .test => pure (.branchNe branchLeft right falseOffset)
        | .notTest => pure (.branchEq branchLeft right falseOffset)
      pure (prelude ++ [branchFalse] ++ thenCode ++
        [.branchEq 0 0 endOffset] ++ elseCode)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-!
`executeInstructions` is useful for straight-line code, but it deliberately
does not interpret branch targets.  This runner treats `start` as the address
of the first instruction and follows the architectural program counter.
Execution stops when the PC reaches the first byte after the code.
-/
def executeCode [NeZero width] :
    Nat → Word width → List (Instruction width) → State width → Option (State width)
  | 0, _, _, _ => none
  | fuel + 1, start, code, state =>
      let byteOffset := (state.pc - start).toNat
      if byteOffset % 4 ≠ 0 then none
      else
        let index := byteOffset / 4
        match code[index]? with
        | some instruction => executeCode fuel start code (execute state instruction)
        | none => if index = code.length then some state else none

/-!
Run code until it reaches a caller-supplied return address. Unlike
`executeCode`, this permits a function body to return with `JALR` before the
physical end of a linked code image.
-/
def executeCodeUntil [NeZero width] :
    Nat → Word width → Word width → List (Instruction width) → State width → Option (State width)
  | 0, _, _, _, _ => none
  | fuel + 1, start, returnAddress, code, state =>
      if state.pc = returnAddress then some state
      else
        let byteOffset := (state.pc - start).toNat
        if byteOffset % 4 ≠ 0 then none
        else
          let index := byteOffset / 4
          match code[index]? with
          | some instruction =>
              executeCodeUntil fuel start returnAddress code (execute state instruction)
          | none => none

def executeFunction [NeZero width]
    (fuel : Nat) (start : Word width)
    (parameters : List (Fin 32)) (code : List (Instruction width))
    (returns : List (Fin 32)) (arguments : List (Word width))
    (state : State width) : Option (List (Word width)) :=
  if parameters.length != arguments.length then none
  else
    let initialized :=
      (parameters.zip arguments).foldl
        (fun state (register, value) => writeRegister state register value)
        { state with pc := start }
    (executeCode fuel start code initialized).map
      (fun state => returns.map (readRegister state))

def executeFunctionAt [NeZero width]
    (fuel : Nat) (start entry returnAddress : Word width)
    (parameters : List (Fin 32)) (code : List (Instruction width))
    (returns : List (Fin 32)) (arguments : List (Word width))
    (state : State width) : Option (List (Word width)) :=
  if parameters.length != arguments.length then none
  else
    let initialized :=
      (parameters.zip arguments).foldl
        (fun state (register, value) => writeRegister state register value)
        { state with pc := entry }
    (executeCodeUntil fuel start returnAddress code initialized).map
      (fun state => returns.map (readRegister state))

def rotateRight [NeZero width] (value : Word width) (amount : Nat) : Word width :=
  BitVec.ushiftRight value (amount % width) |||
    BitVec.shiftLeft value ((width - amount % width) % width)


theorem executeCode_conditional_equal :
    (executeCode 10 (0 : Word 32)
      [.branchNe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (zeroState 32)).map (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeFunction_add :
    executeFunction 10 (0 : Word 64) [2, 3] [.add 5 2 3] [5] [7, 8]
      (zeroState 64) = some [15] := by
  native_decide

theorem executeFunction_add_general (left right : Word 64) :
    executeFunction 10 (0 : Word 64) [2, 3] [.add 5 2 3] [5] [left, right]
      (zeroState 64) = some [left + right] := by
  simp [executeFunction, executeCode, execute, writeRegister, readRegister,
    nextPc, zeroState]

theorem executeFunction_storeLoad :
    executeFunction 20 (0 : Word 64) []
      [.addi 1 0 100, .addi 2 0 42, .storeWord 2 1, .loadWord 3 1]
      [3] [] (zeroState 64) = some [42] := by
  native_decide

theorem executeFunctionAt_jalr_return :
    executeFunctionAt 20 (0 : Word 64) 16 4 []
      [.addi 0 0 0, .addi 0 0 0, .addi 0 0 0, .addi 0 0 0,
        .addi 10 0 42, .jalr 0 1 0] [10] []
      (writeRegister (zeroState 64) 1 4) = some [42] := by
  native_decide

theorem executeCode_conditional_notEqual :
    (executeCode 10 (0 : Word 32)
      [.branchEq 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (zeroState 32) 1 9)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_lower :
    (executeCode 10 (0 : Word 32)
      [.branchGeU 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notLower :
    (executeCode 10 (0 : Word 32)
      [.branchLtU 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

theorem executeCode_conditional_less :
    (executeCode 10 (0 : Word 32)
      [.branchGe 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 (BitVec.ofNat 32 (2 ^ 32 - 1))) 2 0)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notLess :
    (executeCode 10 (0 : Word 32)
      [.branchLt 1 2 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 (BitVec.ofNat 32 (2 ^ 32 - 1))) 2 0)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

theorem executeCode_conditional_test :
    (executeCode 12 (0 : Word 32)
      [.and 1 1 2, .branchNe 1 0 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (writeRegister (zeroState 32) 1 1) 2 2)).map
        (fun state => readRegister state 3) = some 1 := by
  native_decide

theorem executeCode_conditional_notTest :
    (executeCode 12 (0 : Word 32)
      [.and 1 1 0, .branchEq 1 0 (BitVec.ofNat 32 12),
        .addi 3 0 1, .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2]
      (writeRegister (zeroState 32) 1 1)).map
        (fun state => readRegister state 3) = some 2 := by
  native_decide

def evalWordExp [NeZero width] (state : State width) :
    WordExp (Word width) → Option (Word width)
  | .const value => some value
  | .var name => do
      let register ← registerOfNat name
      pure (readRegister state register)
  | .load address => do
      let address ← evalWordExp state address
      pure (readWordValue state address)
  | .op operator [.var left, .var right] => do
      let left ← registerOfNat left
      let right ← registerOfNat right
      pure (match operator with
        | .add => readRegister state left + readRegister state right
        | .sub => readRegister state left - readRegister state right
        | .and => readRegister state left &&& readRegister state right
        | .or => readRegister state left ||| readRegister state right
        | .xor => readRegister state left ^^^ readRegister state right)
  | .shift operator (.var left) (.var right) => do
      let left ← registerOfNat left
      let right ← registerOfNat right
      match operator with
      | .lsl => pure (BitVec.shiftLeft (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .lsr => pure (BitVec.ushiftRight (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .asr => pure (BitVec.sshiftRight (readRegister state left)
          (shiftAmount (readRegister state right)))
      | .ror => pure (rotateRight (readRegister state left)
          (shiftAmount (readRegister state right)))
  | .shift operator (.var left) (.const amount) => do
      let left ← registerOfNat left
      match operator with
      | .lsl => pure (BitVec.shiftLeft (readRegister state left) (shiftAmount amount))
      | .lsr => pure (BitVec.ushiftRight (readRegister state left) (shiftAmount amount))
      | .asr => pure (BitVec.sshiftRight (readRegister state left) (shiftAmount amount))
      | .ror => pure (rotateRight (readRegister state left) (shiftAmount amount))
  | _ => none

def wordFunctionToRiscV [NeZero width] :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .skip => some ([], [])
  | .assign name value => do
      let instructions ← wordExpToInstructions name value
      pure (instructions, [])
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (instructions, [])
  | .inst instruction => do
      let instruction ← wordInstToInstruction instruction
      pure ([instruction], [])
  | .store address value => do
      let instructions ← wordStoreToInstructions address value
      pure (instructions, [])
  | .shareInst operator name address => do
      let instructions ← wordShareInstToInstructions operator name address
      pure (instructions, [])
  | .locValue destination source => do
      let instructions ← wordExpToInstructions destination (.var source)
      pure (instructions, [])
  | .tick => pure ([.addi 0 0 0], [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let (branchLeft, right, prelude) ←
        wordConditionOperands operator condition rightValue
      let (thenCode, thenReturns) ← wordFunctionToRiscV thenBranch
      let (elseCode, elseReturns) ← wordFunctionToRiscV elseBranch
      if thenReturns != elseReturns then none
      else
        let falseOffset : Word width :=
          BitVec.ofNat width (8 + 4 * thenCode.length)
        let endOffset : Word width :=
          BitVec.ofNat width (4 + 4 * elseCode.length)
        let branchFalse ← match operator with
          | .equal => pure (.branchNe branchLeft right falseOffset)
          | .notEqual => pure (.branchEq branchLeft right falseOffset)
          | .less => pure (.branchGe branchLeft right falseOffset)
          | .notLess => pure (.branchLt branchLeft right falseOffset)
          | .lower => pure (.branchGeU branchLeft right falseOffset)
          | .notLower => pure (.branchLtU branchLeft right falseOffset)
          | .test => pure (.branchNe branchLeft right falseOffset)
          | .notTest => pure (.branchEq branchLeft right falseOffset)
        pure (prelude ++ [branchFalse] ++ thenCode ++
          [.branchEq 0 0 endOffset] ++ elseCode, thenReturns)
  | .mustTerminate body => wordFunctionToRiscV body
  | .seq first second => do
      let (firstCode, firstReturns) ← wordFunctionToRiscV first
      if !firstReturns.isEmpty then
        pure (firstCode, firstReturns)
      else
        let (secondCode, secondReturns) ← wordFunctionToRiscV second
        pure (firstCode ++ secondCode, secondReturns)
  | .return _ values => do
      let values ← values.mapM registerOfNat
      pure ([], values)
  | _ => none

def evalWordCondition [NeZero width] (state : State width)
    (operator : Cmp) (condition : Nat) (rightValue : WordRegImm (Word width)) :
    Option Bool := do
  let condition ← registerOfNat condition
  let left := readRegister state condition
  let right ← match rightValue with
    | .reg right => do
        let right ← registerOfNat right
        pure (readRegister state right)
    | .imm value => pure value
  match operator with
  | .equal => pure (left == right)
  | .notEqual => pure (left != right)
  | .less => pure (signedLess left right)
  | .notLess => pure (!signedLess left right)
  | .lower => pure (decide (left < right))
  | .notLower => pure (decide (¬ left < right))
  | .test => pure (left &&& right == 0)
  | .notTest => pure (left &&& right != 0)

def evalWordFunction [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width × List (Word width))
  | .skip => some (state, [])
  | .move _ moves => do
      let instructions ← wordMoveToInstructions moves
      pure (executeInstructions state instructions, [])
  | .assign name value => do
      let instructions ← wordExpToInstructions name value
      pure (executeInstructions state instructions, [])
  | .tick => pure (execute state (.addi 0 0 0), [])
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (executeInstructions state instructions, [])
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address), [])
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address), [])
  | .inst (.mem .load16 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalf destination address), [])
  | .inst (.mem .store16 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalf source address), [])
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address), [])
  | .inst (.mem .load destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWord destination address), [])
  | .store address value => do
      let state ← evalWordShareInst state .store value address
      pure (state, [])
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address), [])
  | .inst (.mem .store source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWord source address), [])
  | .shareInst operator name address => do
      let state ← evalWordShareInst state operator name address
      pure (state, [])
  | .locValue destination source => do
      let instructions ← wordExpToInstructions destination (.var source)
      pure (executeInstructions state instructions, [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordFunction state thenBranch
      else evalWordFunction state elseBranch
  | .mustTerminate body => evalWordFunction state body
  | .seq first second => do
      let (state, firstReturns) ← evalWordFunction state first
      if !firstReturns.isEmpty then
        pure (state, firstReturns)
      else
        let (state, secondReturns) ← evalWordFunction state second
        pure (state, secondReturns)
  | .return _ values => do
      let values ← values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister state register))
      pure (state, values)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def evalWordProg [NeZero width] (state : State width) :
    WordProg (Word width) → Option (State width)
  | .skip => some state
  | .move _ moves => do
      let instructions ← wordMoveToInstructions moves
      pure (executeInstructions state instructions)
  | .assign name value => do
      let instructions ← wordExpToInstructions name value
      pure (executeInstructions state instructions)
  | .tick => pure (execute state (.addi 0 0 0))
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (executeInstructions state instructions)
  | .inst (.mem .load8 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadByte destination address))
  | .inst (.mem .store8 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeByte source address))
  | .inst (.mem .load16 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadHalf destination address))
  | .inst (.mem .store16 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeHalf source address))
  | .inst (.mem .load32 destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.load32 destination address))
  | .store address value =>
      evalWordShareInst state .store value address
  | .inst (.mem .store32 source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.store32 source address))
  | .inst (.mem .store source address) => do
      let source ← registerOfNat source
      let address ← registerOfNat address
      pure (execute state (.storeWord source address))
  | .inst (.mem .load destination address) => do
      let destination ← registerOfNat destination
      let address ← registerOfNat address
      pure (execute state (.loadWord destination address))
  | .shareInst operator name address =>
      evalWordShareInst state operator name address
  | .locValue destination source => do
      let instructions ← wordExpToInstructions destination (.var source)
      pure (executeInstructions state instructions)
  | .ite operator condition rightValue thenBranch elseBranch => do
      let choose ← evalWordCondition state operator condition rightValue
      if choose then evalWordProg state thenBranch
      else evalWordProg state elseBranch
  | .mustTerminate body => evalWordProg state body
  | .seq first second => do
      let state ← evalWordProg state first
      evalWordProg state second
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem compileWordAdd_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.op .add [.var 2, .var 3])) =
      some (executeInstructions state [.add 1 2 3]) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction, evalWordExp,
    executeInstructions, registerOfNat,
    execute, writeRegister, nextPc]

theorem wordFunctionToRiscV_locValue [NeZero width] :
    wordFunctionToRiscV
        ((.locValue 4 2) : WordProg (Word width)) =
      some ([.addi 4 2 0], []) := by
  simp [wordFunctionToRiscV, wordExpToInstructions,
    wordExpToInstruction, registerOfNat]

theorem evalWordFunction_locValue [NeZero width] (state : State width) :
    evalWordFunction state
        ((.locValue 4 2) : WordProg (Word width)) =
      some (execute state (.addi 4 2 0), []) := by
  simp [evalWordFunction, wordExpToInstructions,
    wordExpToInstruction, executeInstructions, registerOfNat]

theorem compileWordLocValue_sound [NeZero width] (state : State width) :
    evalWordProg state
        ((.locValue 4 2) : WordProg (Word width)) =
      some (executeInstructions state [.addi 4 2 0]) := by
  simp [evalWordProg, wordExpToInstructions,
    wordExpToInstruction, executeInstructions, registerOfNat]

theorem wordExpToInstruction_binOp [NeZero width] (operator : BinOp) :
    wordExpToInstruction (width := width) 1 (.op operator [.var 2, .var 3]) =
      some (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3) := by
  cases operator <;> simp [wordExpToInstruction, registerOfNat]

theorem compileWordBinOp_sound [NeZero width] (state : State width)
    (operator : BinOp) :
    evalWordProg state
        (.assign 1 (.op operator [.var 2, .var 3])) =
      some (execute state (match operator with
        | .add => .add 1 2 3
        | .sub => .sub 1 2 3
        | .and => .and 1 2 3
        | .or => .or 1 2 3
        | .xor => .xor 1 2 3)) := by
  cases operator <;>
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, executeInstructions_single]

theorem compileWordShiftLsl_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.var 3))) =
      some (execute state (.sll 1 2 3)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions_single]

theorem compileWordShiftLsr_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.var 3))) =
      some (execute state (.srl 1 2 3)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions_single]

theorem compileWordShiftAsr_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.var 3))) =
      some (execute state (.sra 1 2 3)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions_single]

theorem evalWordExp_rotateRight_immediate [NeZero width] (state : State width)
    (amount : Word width) :
    evalWordExp state (.shift .ror (.var 2) (.const amount)) =
      some (rotateRight (readRegister state 2) (shiftAmount amount)) := by
  simp [evalWordExp, rotateRight, registerOfNat]

theorem shiftAmount_ofNat_of_lt [NeZero width] {amount : Nat} (h : amount < width) :
    shiftAmount (BitVec.ofNat width amount) = amount := by
  unfold shiftAmount
  rw [BitVec.toNat_ofNat]
  have hpow : width ≤ 2 ^ width := by
    have haux : ∀ n : Nat, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          cases n with
          | zero => simp
          | succ n =>
              rw [Nat.pow_succ]
              calc
                n + 2 ≤ (n + 1) * 2 := by omega
                _ ≤ 2 ^ (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
    exact haux width
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h hpow), Nat.mod_eq_of_lt h]

theorem compileWordRotateRight_immediate_sound [NeZero width] (state : State width)
    (amount : Word width) :
    (evalWordProg state
      (.assign 1 (.shift .ror (.var 2) (.const amount)))).map
        (fun state => readRegister state 1) =
      evalWordExp state (.shift .ror (.var 2) (.const amount)) := by
  have amount_lt : shiftAmount amount < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  have complement_lt : (width - shiftAmount amount) % width < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    evalWordExp, rotateRight, registerOfNat, executeInstructions,
    execute, writeRegister, readRegister, nextPc,
    shiftAmount_ofNat_of_lt amount_lt,
    shiftAmount_ofNat_of_lt complement_lt,
    Nat.mod_eq_of_lt amount_lt, BitVec.or_comm]

theorem compileWordAdd_zeroState [NeZero width] :
    evalWordProg (zeroState width)
        (.assign 1 (.const (7 : Word width))) =
      some (executeInstructions (zeroState width) [.addi 1 0 7]) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction, evalWordExp,
    executeInstructions, registerOfNat,
    execute, writeRegister, nextPc, ZeroRegister, zeroState, readRegister]

theorem compileWordLoadByte_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .load8 1 2)) =
      some (execute state (.loadByte 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, writeByte,
    readByte, nextPc]

theorem compileWordStoreByte_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .store8 1 2)) =
      some (execute state (.storeByte 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, writeByte,
    readByte, nextPc]

theorem compileWordLoad16_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .load16 1 2)) =
      some (execute state (.loadHalf 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, readWord16,
    readByte, byteAddress, nextPc]

theorem compileWordStore16_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .store16 1 2)) =
      some (execute state (.storeHalf 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeWord16, writeByte,
    byteAddress, nextPc]

theorem compileWordLoad32_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .load32 1 2)) =
      some (execute state (.load32 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeRegister, readWord32,
    readByte, byteAddress, nextPc]

theorem compileWordStore32_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.mem .store32 1 2)) =
      some (execute state (.store32 1 2)) := by
  simp [evalWordProg, registerOfNat, execute, writeWord32, writeByte,
    byteAddress, nextPc]

theorem compileWordStoreWord_sound [NeZero width] (state : State width) :
    evalWordProg state (.store (.var 2) 1) =
      some (execute state (.storeWord 1 2)) := by
  simp [evalWordProg, evalWordShareInst, wordStoreToInstructions,
    wordShareInstToInstructions,
    wordInstToInstruction, evalWordExp, registerOfNat, executeInstructions,
    execute,
    writeWordValue, writeByte, byteAddress, nextPc]

theorem wordShareInstToRiscV_load [NeZero width] :
    wordProgToRiscV (width := width)
        (.shareInst .load 1 (.var 2)) = some [.loadWord 1 2] := by
  simp [wordProgToRiscV, wordShareInstToInstructions, wordInstToInstruction,
    registerOfNat]

theorem wordExpToRiscV_load [NeZero width] :
    wordExpToInstructions (width := width) 1
        (.load (.var 2)) =
      some [.addi 31 2 0, .loadWord 1 31] := by
  simp [wordExpToInstructions, wordExpToInstruction, registerOfNat]

theorem compileWordExpLoad_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.assign 1 (.load (.var 2))) =
      some (executeInstructions state
        [.addi 31 2 0, .loadWord 1 31]) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, readWordValue,
    readByte, byteAddress, nextPc]

theorem wordShareInstToRiscV_store8 [NeZero width] :
    wordProgToRiscV (width := width)
        (.shareInst .store8 1 (.var 2)) = some [.storeByte 1 2] := by
  simp [wordProgToRiscV, wordShareInstToInstructions, wordInstToInstruction,
    registerOfNat]

theorem wordShareInstToRiscV_load16 [NeZero width] :
    wordProgToRiscV (width := width)
        (.shareInst .load16 1 (.var 2)) = some [.loadHalf 1 2] := by
  simp [wordProgToRiscV, wordShareInstToInstructions, wordInstToInstruction,
    registerOfNat]

theorem wordShareInstToRiscV_store16 [NeZero width] :
    wordProgToRiscV (width := width)
        (.shareInst .store16 1 (.var 2)) = some [.storeHalf 1 2] := by
  simp [wordProgToRiscV, wordShareInstToInstructions, wordInstToInstruction,
    registerOfNat]

theorem wordShareInstToRiscV_add_offset [NeZero width] :
    wordProgToRiscV (width := width)
        (.shareInst .load32 1 (.op .add [.var 2, .const (4 : Word width)])) =
      some [.addi 31 2 4, .load32 1 31] := by
  simp [wordProgToRiscV, wordShareInstToInstructions, wordExpToInstructions,
    wordExpToInstruction,
    wordInstToInstruction, registerOfNat]

theorem wordStoreToRiscV_add_offset [NeZero width] :
    wordProgToRiscV (width := width)
        (.store (.op .add [.var 2, .const (8 : Word width)]) 1) =
      some [.addi 31 2 8, .storeWord 1 31] := by
  simp [wordProgToRiscV, wordStoreToInstructions,
    wordShareInstToInstructions, wordExpToInstructions, wordExpToInstruction,
    wordInstToInstruction,
    registerOfNat]

theorem compileWordShareInstLoad_sound [NeZero width] (state : State width) :
    evalWordProg state (.shareInst .load 1 (.var 2)) =
      some (execute state (.loadWord 1 2)) := by
  simp [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
    wordInstToInstruction, registerOfNat, execute,
    executeInstructions, writeRegister, readWordValue, readByte, byteAddress,
    nextPc]

theorem compileWordShareInstStore32_sound [NeZero width] (state : State width) :
    evalWordProg state (.shareInst .store32 1 (.var 2)) =
      some (execute state (.store32 1 2)) := by
  simp [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
    wordInstToInstruction, registerOfNat, execute,
    executeInstructions, writeWord32, writeByte, byteAddress, nextPc]

theorem compileWordShareInstLoad16_sound [NeZero width] (state : State width) :
    evalWordProg state (.shareInst .load16 1 (.var 2)) =
      some (execute state (.loadHalf 1 2)) := by
  simp [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
    wordInstToInstruction, registerOfNat, execute,
    executeInstructions, writeRegister, readWord16, readByte, byteAddress,
    nextPc]

theorem compileWordShareInstStore16_sound [NeZero width] (state : State width) :
    evalWordProg state (.shareInst .store16 1 (.var 2)) =
      some (execute state (.storeHalf 1 2)) := by
  simp [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
    wordInstToInstruction, registerOfNat, execute,
    executeInstructions, writeWord16, writeByte, byteAddress, nextPc]

theorem compileWordShareInstLoadOffset_sound [NeZero width] (state : State width) :
    evalWordProg state
        (.shareInst .load32 1
          (.op .add [.var 2, .const (4 : Word width)])) =
      some (executeInstructions state [.addi 31 2 4, .load32 1 31]) := by
  simp [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
    wordExpToInstructions, wordExpToInstruction, wordInstToInstruction, registerOfNat,
    executeInstructions, execute, writeRegister, readWord32, readByte,
    byteAddress, nextPc]

theorem wordFunctionToRiscV_return_add [NeZero width] :
    wordFunctionToRiscV
        ((.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) :
          WordProg (Word width)) =
      some ([.add 1 2 3], [1]) := by
  simp [wordFunctionToRiscV, wordExpToInstructions, wordExpToInstruction, registerOfNat]

theorem evalWordFunction_return_add [NeZero width] (state : State width) :
    evalWordFunction state
        (.seq (.assign 1 (.op .add [.var 2, .var 3])) (.return 0 [1])) =
      some (execute state (.add 1 2 3),
        [readRegister (execute state (.add 1 2 3)) 1]) := by
  simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions_single]

theorem wordFunctionToRiscV_return_const [NeZero width] (value : Word width) :
    wordFunctionToRiscV
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (Word width)) =
      some ([.addi 1 0 value], [1]) := by
  simp [wordFunctionToRiscV, wordExpToInstructions, wordExpToInstruction, registerOfNat]

theorem evalWordFunction_return_const [NeZero width] (state : State width)
    (value : Word width) (zero : ZeroRegister state) :
    evalWordFunction state
        ((.seq (.assign 1 (.const value)) (.return 0 [1])) :
          WordProg (Word width)) =
      some (execute state (.addi 1 0 value),
        [readRegister (execute state (.addi 1 0 value)) 1]) := by
  simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions_single]

theorem wordArithToInstruction_longMul [NeZero width] :
    wordArithToInstruction (width := width) (.longMul 1 1 2 3) =
      none := by
  simp [wordArithToInstruction]

theorem wordArithToInstructions_longMul [NeZero width] :
    wordArithToInstructions (width := width) (.longMul 1 2 3 4) =
      some [.mulHU 1 3 4, .mul 2 3 4] := by
  simp [wordArithToInstructions, registerOfNat]

theorem wordArithToInstructions_longMul_alias [NeZero width] :
    wordArithToInstructions (width := width) (.longMul 3 2 3 4) = none := by
  simp [wordArithToInstructions]

theorem compileWordLongMul_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.arith (.longMul 1 1 2 3))) =
      some (executeInstructions state [.mulHU 1 2 3, .mul 1 2 3]) := by
  simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
    executeInstructions, registerOfNat]

theorem wordFunctionToRiscV_longMul [NeZero width] :
    wordFunctionToRiscV
      ((.inst (.arith (.longMul 5 6 2 3))) : WordProg (Word width)) =
      some ([.mulHU 5 2 3, .mul 6 2 3], []) := by
  simp [wordFunctionToRiscV, wordArithToInstructions, registerOfNat]

theorem evalWordFunction_longMul [NeZero width] (state : State width) :
    evalWordFunction state
      ((.inst (.arith (.longMul 5 6 2 3))) : WordProg (Word width)) =
      some (executeInstructions state [.mulHU 5 2 3, .mul 6 2 3], []) := by
  simp [evalWordFunction, wordArithToInstructions, executeInstructions,
    registerOfNat]

theorem wordArithToInstruction_div [NeZero width] :
    wordArithToInstruction (width := width) (.div 1 2 3) =
      some (.divU 1 2 3) := by
  simp [wordArithToInstruction, registerOfNat]

theorem compileWordDiv_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.arith (.div 1 2 3))) =
      some (execute state (.divU 1 2 3)) := by
  simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
    executeInstructions, registerOfNat]

theorem wordArithToInstructions_addCarry [NeZero width] :
    wordArithToInstructions (width := width) (.addCarry 5 6 2 3 4) =
      some [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] := by
  simp [wordArithToInstructions, registerOfNat]

theorem compileWordAddCarry_sound [NeZero width] (state : State width) :
    evalWordProg state (.inst (.arith (.addCarry 5 6 2 3 4))) =
      some (executeInstructions state
        [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
          .sltu 31 5 31, .or 6 6 31]) := by
  simp [evalWordProg, wordArithToInstructions, executeInstructions,
    registerOfNat]

theorem wordFunctionToRiscV_addCarry [NeZero width] :
    wordFunctionToRiscV
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some ([.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31], []) := by
  simp [wordFunctionToRiscV, wordArithToInstructions, registerOfNat]

theorem evalWordFunction_addCarry [NeZero width] (state : State width) :
    evalWordFunction state
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some (executeInstructions state
        [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
          .sltu 31 5 31, .or 6 6 31], []) := by
  simp [evalWordFunction, wordArithToInstructions, executeInstructions,
    registerOfNat]

def compileWordAdd [NeZero width] (destination left right : Nat) :
    Option (List (Instruction width)) :=
  wordProgToRiscV (.assign destination (.op .add [.var left, .var right]))

example [NeZero width] :
    compileWordAdd (width := width) 1 2 3 = some [.add 1 2 3] := by
  simp [compileWordAdd, wordProgToRiscV, wordExpToInstructions,
    wordExpToInstruction, registerOfNat]

example [NeZero width] :
    wordExpToInstruction (width := width) 1 (.op .xor [.var 2, .var 3]) =
      some (.xor 1 2 3) := by
  simp [wordExpToInstruction, registerOfNat]

example [NeZero width] :
    wordInstToInstruction (width := width) (.arith (.longMul 1 1 2 3)) =
      none := by
  simp [wordInstToInstruction, wordArithToInstruction, registerOfNat]

end Flapjack.RiscV
