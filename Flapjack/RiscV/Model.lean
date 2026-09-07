import Std

/-!
The first Lean target-model slice for Flapjack's RISC-V backend.

The HOL reference is
`HOL/examples/l3-machine-code/riscv/model/riscv.sml`. This file ports the
architectural vocabulary and executable register, byte-memory, and
straight-line instruction primitives used by later instruction and
compiler-correctness layers. It intentionally does not claim to be the
complete RISC-V transition system yet.
-/

namespace Flapjack.RiscV

abbrev Word (width : Nat) := BitVec width

/-!
The Loop semantics uses homogeneous shift typeclasses.  BitVec exposes its
architectural shifts through heterogeneous instances because the shift count
is itself a BitVec, so provide the corresponding homogeneous views for the
Word-level Loop-to-Word bridge.
-/
instance bitVecWordShiftLeft : ShiftLeft (Word width) :=
  ⟨fun value amount => value <<< amount.toNat⟩

instance bitVecWordShiftRight : ShiftRight (Word width) :=
  ⟨fun value amount => value >>> amount.toNat⟩

inductive AccessType where
  | read
  | write
  deriving DecidableEq, Repr

inductive FetchType where
  | instruction
  | data
  deriving DecidableEq, Repr

inductive Architecture where
  | rv32i
  | rv64i
  | rv128i
  deriving DecidableEq, Repr

def Architecture.width : Architecture → Nat
  | .rv32i => 32
  | .rv64i => 64
  | .rv128i => 128

inductive Privilege where
  | user
  | supervisor
  | hypervisor
  | machine
  deriving DecidableEq, Repr

inductive VMMode where
  | mbare
  | mbb
  | mbbid
  | sv32
  | sv39
  | sv48
  | sv57
  | sv64
  deriving DecidableEq, Repr

inductive ExtStatus where
  | off
  | initial
  | clean
  | dirty
  deriving DecidableEq, Repr

inductive Interrupt where
  | software
  | timer
  deriving DecidableEq, Repr

inductive ExceptionType where
  | fetchMisaligned
  | fetchFault
  | illegalInstr
  | breakpoint
  | loadFault
  | amoMisaligned
  | storeAmoFault
  | uModeEnvCall
  | sModeEnvCall
  | hModeEnvCall
  | mModeEnvCall
  deriving DecidableEq, Repr

structure SynchronousTrap (width : Nat) where
  badAddress : Option (Word width)
  trap : ExceptionType
  deriving DecidableEq, Repr

inductive TransferControl (width : Nat) where
  | branchTo (address : Word width)
  | eReturn
  | mReturn
  | trap (trap : SynchronousTrap width)
  deriving Repr

structure State (width : Nat) where
  pc : Word width
  registers : Fin 32 → Word width
  memory : Word width → BitVec 8
  privilege : Privilege
  mode : VMMode

inductive Instruction (width : Nat) where
  | add (destination sourceLeft sourceRight : Fin 32)
  | sub (destination sourceLeft sourceRight : Fin 32)
  | addW (destination sourceLeft sourceRight : Fin 32)
  | subW (destination sourceLeft sourceRight : Fin 32)
  | and (destination sourceLeft sourceRight : Fin 32)
  | or (destination sourceLeft sourceRight : Fin 32)
  | xor (destination sourceLeft sourceRight : Fin 32)
  | addi (destination source : Fin 32) (immediate : Word width)
  | addiW (destination source : Fin 32) (immediate : Word width)
  | andi (destination source : Fin 32) (immediate : Word width)
  | ori (destination source : Fin 32) (immediate : Word width)
  | xori (destination source : Fin 32) (immediate : Word width)
  | mul (destination sourceLeft sourceRight : Fin 32)
  | mulW (destination sourceLeft sourceRight : Fin 32)
  | mulHU (destination sourceLeft sourceRight : Fin 32)
  | sll (destination sourceLeft sourceRight : Fin 32)
  | srl (destination sourceLeft sourceRight : Fin 32)
  | sra (destination sourceLeft sourceRight : Fin 32)
  | sllW (destination sourceLeft sourceRight : Fin 32)
  | srlW (destination sourceLeft sourceRight : Fin 32)
  | sraW (destination sourceLeft sourceRight : Fin 32)
  | slli (destination source : Fin 32) (amount : Word width)
  | srli (destination source : Fin 32) (amount : Word width)
  | srai (destination source : Fin 32) (amount : Word width)
  | slliW (destination source : Fin 32) (amount : Word width)
  | srliW (destination source : Fin 32) (amount : Word width)
  | sraiW (destination source : Fin 32) (amount : Word width)
  | slt (destination sourceLeft sourceRight : Fin 32)
  | slti (destination source : Fin 32) (immediate : Word width)
  | sltu (destination sourceLeft sourceRight : Fin 32)
  | sltiu (destination source : Fin 32) (immediate : Word width)
  | lui (destination : Fin 32) (immediate : Word width)
  | auipc (destination : Fin 32) (immediate : Word width)
  | divU (destination sourceLeft sourceRight : Fin 32)
  | remU (destination sourceLeft sourceRight : Fin 32)
  | branchEq (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | branchNe (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | branchLt (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | branchGe (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | branchLtU (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | branchGeU (sourceLeft sourceRight : Fin 32) (offset : Word width)
  | jal (destination : Fin 32) (offset : Word width)
  | jalr (destination source : Fin 32) (offset : Word width)
  | ecall
  | loadByte (destination address : Fin 32)
  | loadByteSigned (destination address : Fin 32)
  | storeByte (source address : Fin 32)
  | loadHalf (destination address : Fin 32)
  | loadHalfSigned (destination address : Fin 32)
  | storeHalf (source address : Fin 32)
  | load32 (destination address : Fin 32)
  | store32 (source address : Fin 32)
  | loadWord (destination address : Fin 32)
  | storeWord (source address : Fin 32)
  deriving DecidableEq, Repr

def zeroState (width : Nat) [NeZero width] : State width :=
  { pc := 0
    registers := fun _ => 0
    memory := fun _ => 0
    privilege := .machine
    mode := .mbare }

def aligned (address : Word width) (alignment : Nat) : Bool :=
  alignment ≠ 0 && address.toNat % alignment = 0

def readRegister (state : State width) (register : Fin 32) : Word width :=
  state.registers register

def ZeroRegister (state : State width) : Prop :=
  readRegister state 0 = 0

def writeRegister (state : State width) (register : Fin 32) (value : Word width) : State width :=
  if register = 0 then state
  else { state with registers := fun current => if current = register then value else state.registers current }

def readByte (state : State width) (address : Word width) : BitVec 8 :=
  state.memory address

def writeByte (state : State width) (address : Word width) (value : BitVec 8) : State width :=
  { state with memory := fun current => if current = address then value else state.memory current }

def byteAddress (address : Word width) (offset : Nat) : Word width :=
  address + BitVec.ofNat width offset

def readWord32 (state : State width) (address : Word width) : Word width :=
  let byte0 := (readByte state (byteAddress address 0)).toNat
  let byte1 := (readByte state (byteAddress address 1)).toNat
  let byte2 := (readByte state (byteAddress address 2)).toNat
  let byte3 := (readByte state (byteAddress address 3)).toNat
  BitVec.ofNat width (byte0 + 256 * byte1 + 256 ^ 2 * byte2 + 256 ^ 3 * byte3)

def readWord16 (state : State width) (address : Word width) : Word width :=
  let byte0 := (readByte state (byteAddress address 0)).toNat
  let byte1 := (readByte state (byteAddress address 1)).toNat
  BitVec.ofNat width (byte0 + 256 * byte1)

def readByteSigned (state : State width) (address : Word width) : Word width :=
  BitVec.signExtend width (readByte state address)

def readHalfSigned (state : State width) (address : Word width) : Word width :=
  BitVec.signExtend width (BitVec.extractLsb 15 0 (readWord16 state address))

def writeWord32 (state : State width) (address : Word width) (value : Word width) : State width :=
  let byte0 := BitVec.ofNat 8 (value.toNat % 256)
  let byte1 := BitVec.ofNat 8 (value.toNat / 256 % 256)
  let byte2 := BitVec.ofNat 8 (value.toNat / 256 ^ 2 % 256)
  let byte3 := BitVec.ofNat 8 (value.toNat / 256 ^ 3 % 256)
  let state := writeByte state (byteAddress address 0) byte0
  let state := writeByte state (byteAddress address 1) byte1
  let state := writeByte state (byteAddress address 2) byte2
  writeByte state (byteAddress address 3) byte3

def writeWord16 (state : State width) (address : Word width) (value : Word width) : State width :=
  let byte0 := BitVec.ofNat 8 (value.toNat % 256)
  let byte1 := BitVec.ofNat 8 (value.toNat / 256 % 256)
  let state := writeByte state (byteAddress address 0) byte0
  writeByte state (byteAddress address 1) byte1

def readWordValue (state : State width) (address : Word width) : Word width :=
  BitVec.ofNat width
    ((List.range (width / 8)).foldl
      (fun total offset =>
        total + 256 ^ offset *
          (readByte state (byteAddress address offset)).toNat) 0)

def writeWordValue (state : State width) (address : Word width) (value : Word width) :
    State width :=
  (List.range (width / 8)).foldl
    (fun state offset =>
      writeByte state (byteAddress address offset)
        (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) state

theorem foldWriteBytes_pc (state : State width) (address value : Word width)
    (offsets : List Nat) :
    (offsets.foldl
      (fun state offset =>
        writeByte state (byteAddress address offset)
          (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) state).pc =
      state.pc := by
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets induction =>
      simp only [List.foldl]
      rw [induction]
      rfl

theorem foldWriteBytes_registers (state : State width) (address value : Word width)
    (offsets : List Nat) :
    (offsets.foldl
      (fun state offset =>
        writeByte state (byteAddress address offset)
          (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) state).registers =
      state.registers := by
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets induction =>
      simp only [List.foldl]
      rw [induction]
      rfl

theorem writeWordValue_pc (state : State width) (address value : Word width) :
    (writeWordValue state address value).pc = state.pc := by
  exact foldWriteBytes_pc state address value (List.range (width / 8))

theorem writeWordValue_registers (state : State width) (address value : Word width) :
    (writeWordValue state address value).registers = state.registers := by
  exact foldWriteBytes_registers state address value (List.range (width / 8))

def nextPc (state : State width) : Word width := state.pc + 4

def shiftAmount (value : Word width) : Nat := value.toNat % width

/-! RV64 word operations compute in the low 32 bits and sign-extend their
    result back to the architectural register width.  The same definitions
    also give the natural RV32 behaviour when `width = 32`. -/
def word32 (value : Word width) : Word width :=
  BitVec.signExtend width (BitVec.extractLsb 31 0 value)

def word32Low (value : Word width) : Word width :=
  BitVec.ofNat width (BitVec.extractLsb 31 0 value).toNat

def wordShiftAmount (value : Word width) : Nat := value.toNat % 32

def uImmediate (immediate : Word width) : Word width :=
  BitVec.shiftLeft
    (BitVec.signExtend width (BitVec.ofNat 20 immediate.toNat)) 12

/-! Signed ordering for the two's-complement word represented by `BitVec`. -/
def signedLess (left right : Word width) : Bool :=
  let sign := 2 ^ (width - 1)
  if left.toNat < sign then
    if right.toNat < sign then decide (left.toNat < right.toNat) else false
  else if right.toNat < sign then
    true
  else
    decide (left.toNat < right.toNat)

def execute (state : State width) : Instruction width → State width
  | .add destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft + readRegister state sourceRight)
  | .sub destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft - readRegister state sourceRight)
  | .addW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (readRegister state sourceLeft + readRegister state sourceRight))
  | .subW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (readRegister state sourceLeft - readRegister state sourceRight))
  | .and destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft &&& readRegister state sourceRight)
  | .or destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft ||| readRegister state sourceRight)
  | .xor destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft ^^^ readRegister state sourceRight)
  | .addi destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state source + immediate)
  | .addiW destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (readRegister state source + immediate))
  | .andi destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state source &&& immediate)
  | .ori destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state source ||| immediate)
  | .xori destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state source ^^^ immediate)
  | .mul destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft * readRegister state sourceRight)
  | .mulW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (readRegister state sourceLeft * readRegister state sourceRight))
  | .mulHU destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.ofNat width
          ((readRegister state sourceLeft).toNat *
            (readRegister state sourceRight).toNat / 2 ^ width))
  | .sll destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.shiftLeft (readRegister state sourceLeft)
          (shiftAmount (readRegister state sourceRight)))
  | .srl destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.ushiftRight (readRegister state sourceLeft)
          (shiftAmount (readRegister state sourceRight)))
  | .sra destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.sshiftRight (readRegister state sourceLeft)
          (shiftAmount (readRegister state sourceRight)))
  | .sllW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.shiftLeft (word32Low (readRegister state sourceLeft))
          (wordShiftAmount (readRegister state sourceRight))))
  | .srlW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.ushiftRight (word32Low (readRegister state sourceLeft))
          (wordShiftAmount (readRegister state sourceRight))))
  | .sraW destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.sshiftRight (word32 (readRegister state sourceLeft))
          (wordShiftAmount (readRegister state sourceRight))))
  | .slli destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.shiftLeft (readRegister state source) (shiftAmount amount))
  | .srli destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.ushiftRight (readRegister state source) (shiftAmount amount))
  | .srai destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (BitVec.sshiftRight (readRegister state source) (shiftAmount amount))
  | .slliW destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.shiftLeft (word32Low (readRegister state source))
          (wordShiftAmount amount)))
  | .srliW destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.ushiftRight (word32Low (readRegister state source))
          (wordShiftAmount amount)))
  | .sraiW destination source amount =>
      writeRegister { state with pc := nextPc state } destination
        (word32 (BitVec.sshiftRight (word32 (readRegister state source))
          (wordShiftAmount amount)))
  | .slt destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (if signedLess (readRegister state sourceLeft) (readRegister state sourceRight)
        then 1 else 0)
  | .slti destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (if signedLess (readRegister state source) immediate then 1 else 0)
  | .sltu destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (if readRegister state sourceLeft < readRegister state sourceRight then 1 else 0)
  | .sltiu destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (if readRegister state source < immediate then 1 else 0)
  | .lui destination immediate =>
      writeRegister { state with pc := nextPc state } destination
        (uImmediate immediate)
  | .auipc destination immediate =>
      writeRegister { state with pc := nextPc state } destination
        (state.pc + uImmediate immediate)
  | .divU destination sourceLeft sourceRight =>
      let divisor := readRegister state sourceRight
      writeRegister { state with pc := nextPc state } destination
        (if divisor == 0 then BitVec.ofNat width (2 ^ width - 1)
        else BitVec.ofNat width
          (readRegister state sourceLeft).toNat / divisor.toNat)
  | .remU destination sourceLeft sourceRight =>
      let divisor := readRegister state sourceRight
      writeRegister { state with pc := nextPc state } destination
        (if divisor == 0 then readRegister state sourceLeft
        else BitVec.ofNat width
          ((readRegister state sourceLeft).toNat % divisor.toNat))
  | .branchEq sourceLeft sourceRight offset =>
      { state with pc := (if readRegister state sourceLeft == readRegister state sourceRight then
          state.pc + offset else nextPc state) }
  | .branchNe sourceLeft sourceRight offset =>
      { state with pc := (if readRegister state sourceLeft == readRegister state sourceRight then
          nextPc state else state.pc + offset) }
  | .branchLt sourceLeft sourceRight offset =>
      { state with pc := (if signedLess (readRegister state sourceLeft)
          (readRegister state sourceRight) then
          state.pc + offset else nextPc state) }
  | .branchGe sourceLeft sourceRight offset =>
      { state with pc := (if signedLess (readRegister state sourceLeft)
          (readRegister state sourceRight) then
          nextPc state else state.pc + offset) }
  | .branchLtU sourceLeft sourceRight offset =>
      { state with pc := (if readRegister state sourceLeft < readRegister state sourceRight then
          state.pc + offset else nextPc state) }
  | .branchGeU sourceLeft sourceRight offset =>
      { state with pc := (if readRegister state sourceLeft < readRegister state sourceRight then
          nextPc state else state.pc + offset) }
  | .jal destination offset =>
      writeRegister { state with pc := state.pc + offset } destination (nextPc state)
  | .jalr destination source offset =>
      writeRegister { state with
        pc := (readRegister state source + offset) &&& BitVec.ofNat width (2 ^ width - 2) }
        destination (nextPc state)
  | .ecall =>
      { state with pc := nextPc state }
  | .loadByte destination address =>
      let address := readRegister state address
      let value := BitVec.ofNat width (readByte state address).toNat
      writeRegister { state with pc := nextPc state } destination value
  | .loadByteSigned destination address =>
      let address := readRegister state address
      writeRegister { state with pc := nextPc state } destination
        (readByteSigned state address)
  | .storeByte source address =>
      let address := readRegister state address
      let value := BitVec.ofNat 8 (readRegister state source).toNat
      writeByte { state with pc := nextPc state } address value
  | .loadHalf destination address =>
      let address := readRegister state address
      writeRegister { state with pc := nextPc state } destination
        (readWord16 state address)
  | .loadHalfSigned destination address =>
      let address := readRegister state address
      writeRegister { state with pc := nextPc state } destination
        (readHalfSigned state address)
  | .storeHalf source address =>
      let address := readRegister state address
      writeWord16 { state with pc := nextPc state } address
        (readRegister state source)
  | .load32 destination address =>
      let address := readRegister state address
      writeRegister { state with pc := nextPc state } destination
        (readWord32 state address)
  | .store32 source address =>
      let address := readRegister state address
      writeWord32 { state with pc := nextPc state } address
        (readRegister state source)
  | .loadWord destination address =>
      let address := readRegister state address
      writeRegister { state with pc := nextPc state } destination
        (readWordValue state address)
  | .storeWord source address =>
      let address := readRegister state address
      writeWordValue { state with pc := nextPc state } address
        (readRegister state source)

def accessAligned (access : AccessType) (address : Word width) (alignment : Nat) :
    Option ExceptionType :=
  if aligned address alignment then none
  else some (match access with
    | .read => .loadFault
    | .write => .storeAmoFault)

/-! Classify the traps represented by the current architectural vocabulary.
    The full HOL state transition also updates trap CSRs and the PC; those
    machine details are intentionally outside this compact state record. -/

def executeTrap (state : State width) : Instruction width → Option ExceptionType
  | .ecall =>
      some (match state.privilege with
        | .user => .uModeEnvCall
        | .supervisor => .sModeEnvCall
        | .hypervisor => .hModeEnvCall
        | .machine => .mModeEnvCall)
  | .loadHalf _ address | .loadHalfSigned _ address =>
      accessAligned .read (readRegister state address) 2
  | .storeHalf _ address =>
      accessAligned .write (readRegister state address) 2
  | .load32 _ address =>
      accessAligned .read (readRegister state address) 4
  | .store32 _ address =>
      accessAligned .write (readRegister state address) 4
  | .loadWord _ address =>
      accessAligned .read (readRegister state address) (width / 8)
  | .storeWord _ address =>
      accessAligned .write (readRegister state address) (width / 8)
  | _ => none

/-! An execution boundary that rejects instructions classified as trapping.
    The total `execute` transition remains the backend's instruction equation;
    this option-valued boundary exposes its architectural rejection path. -/

def executeChecked (state : State width) (instruction : Instruction width) :
    Option (State width) :=
  match executeTrap state instruction with
  | none => some (execute state instruction)
  | some _ => none

theorem executeTrap_ecall (state : State width) :
    executeTrap state .ecall = some (match state.privilege with
      | .user => .uModeEnvCall
      | .supervisor => .sModeEnvCall
      | .hypervisor => .hModeEnvCall
      | .machine => .mModeEnvCall) := by
  rfl

theorem executeTrap_load32_misaligned (state : State width)
    (address : Fin 32)
    (h : aligned (readRegister state address) 4 = false) :
    executeTrap state (.load32 0 address) = some .loadFault := by
  simp [executeTrap, accessAligned, h]

theorem executeChecked_ecall (state : State width) :
    executeChecked state .ecall = none := by
  simp [executeChecked, executeTrap]

theorem executeChecked_aligned (state : State width)
    (instruction : Instruction width)
    (h : executeTrap state instruction = none) :
    executeChecked state instruction = some (execute state instruction) := by
  simp [executeChecked, h]

theorem executeChecked_loadHalf_aligned (state : State width)
    (destination address : Fin 32)
    (h : aligned (readRegister state address) 2 = true) :
    executeChecked state (.loadHalf destination address) =
      some (execute state (.loadHalf destination address)) := by
  apply executeChecked_aligned
  simp [executeTrap, accessAligned, h]

theorem executeChecked_load32_misaligned (state : State width)
    (destination address : Fin 32)
    (h : aligned (readRegister state address) 4 = false) :
    executeChecked state (.load32 destination address) = none := by
  simp [executeChecked, executeTrap, accessAligned, h]

theorem executeChecked_storeWord_aligned [NeZero width]
    (state : State width) (source address : Fin 32)
    (h : aligned (readRegister state address) (width / 8) = true) :
    executeChecked state (.storeWord source address) =
      some (execute state (.storeWord source address)) := by
  apply executeChecked_aligned
  simp [executeTrap, accessAligned, h]

theorem zeroState_pc_zero [NeZero width] : (zeroState width).pc = 0 := by
  rfl

theorem writeRegister_zero (state : State width) (value : Word width) :
    writeRegister state 0 value = state := by
  simp [writeRegister]

theorem accessAligned_aligned (access : AccessType) (address : Word width)
    (alignment : Nat) (aligned_address : aligned address alignment = true) :
    accessAligned access address alignment = none := by
  simp [accessAligned, aligned_address]

def Instruction.isBranch : Instruction width → Bool
  | .branchEq _ _ _ | .branchNe _ _ _ | .branchLt _ _ _ | .branchGe _ _ _
  | .branchLtU _ _ _ | .branchGeU _ _ _ | .jal _ _ | .jalr _ _ _ => true
  | _ => false

theorem execute_pc_advance (state : State width) (instruction : Instruction width)
    (not_branch : instruction.isBranch = false) :
    (execute state instruction).pc = state.pc + 4 := by
  cases instruction <;>
    simp [Instruction.isBranch, execute, nextPc, writeRegister, writeByte,
      writeWord16, writeWord32, writeWordValue_pc] at not_branch ⊢
  all_goals split <;> rfl

theorem execute_sltu (state : State width) (destination sourceLeft sourceRight : Fin 32) :
    readRegister (execute state (.sltu destination sourceLeft sourceRight)) destination =
      if destination = 0 then readRegister state destination
      else if readRegister state sourceLeft < readRegister state sourceRight then 1 else 0 := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_divU (state : State width) (destination sourceLeft sourceRight : Fin 32) :
    readRegister (execute state (.divU destination sourceLeft sourceRight)) destination =
      if destination = 0 then readRegister state destination
      else if readRegister state sourceRight == 0 then BitVec.ofNat width (2 ^ width - 1)
      else BitVec.ofNat width
        ((readRegister state sourceLeft).toNat /
          (readRegister state sourceRight).toNat) := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h, BitVec.udiv_def]

theorem execute_remU (state : State width) (destination sourceLeft sourceRight : Fin 32) :
    readRegister (execute state (.remU destination sourceLeft sourceRight)) destination =
      if destination = 0 then readRegister state destination
      else if readRegister state sourceRight == 0 then readRegister state sourceLeft
      else BitVec.ofNat width
        ((readRegister state sourceLeft).toNat %
          (readRegister state sourceRight).toNat) := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_mulHU (state : State width) (destination sourceLeft sourceRight : Fin 32) :
    readRegister (execute state (.mulHU destination sourceLeft sourceRight)) destination =
      if destination = 0 then readRegister state destination
      else BitVec.ofNat width
        ((readRegister state sourceLeft).toNat *
          (readRegister state sourceRight).toNat / 2 ^ width) := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_loadByteSigned (state : State width) (destination address : Fin 32) :
    readRegister (execute state (.loadByteSigned destination address)) destination =
      if destination = 0 then readRegister state destination
      else readByteSigned state (readRegister state address) := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_loadHalfSigned (state : State width) (destination address : Fin 32) :
    readRegister (execute state (.loadHalfSigned destination address)) destination =
      if destination = 0 then readRegister state destination
      else readHalfSigned state (readRegister state address) := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_slt (state : State width) (destination sourceLeft sourceRight : Fin 32) :
    readRegister (execute state (.slt destination sourceLeft sourceRight)) destination =
      if destination = 0 then readRegister state destination
      else if signedLess (readRegister state sourceLeft) (readRegister state sourceRight)
        then 1 else 0 := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_slti (state : State width) (destination source : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.slti destination source immediate)) destination =
      if destination = 0 then readRegister state destination
      else if signedLess (readRegister state source) immediate then 1 else 0 := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_sltiu (state : State width) (destination source : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.sltiu destination source immediate)) destination =
      if destination = 0 then readRegister state destination
      else if readRegister state source < immediate then 1 else 0 := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_lui (state : State width) (destination : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.lui destination immediate)) destination =
      if destination = 0 then readRegister state destination
      else uImmediate immediate := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_auipc (state : State width) (destination : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.auipc destination immediate)) destination =
      if destination = 0 then readRegister state destination
      else state.pc + uImmediate immediate := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, h]

theorem execute_branchEq_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchEq sourceLeft sourceRight offset)).pc =
      if readRegister state sourceLeft == readRegister state sourceRight then
        state.pc + offset
      else
        state.pc + 4 := by
  simp [execute, nextPc]

theorem execute_branchNe_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchNe sourceLeft sourceRight offset)).pc =
      if readRegister state sourceLeft == readRegister state sourceRight then
        state.pc + 4
      else
        state.pc + offset := by
  simp [execute, nextPc]

theorem execute_branchLt_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchLt sourceLeft sourceRight offset)).pc =
      if signedLess (readRegister state sourceLeft) (readRegister state sourceRight) then
        state.pc + offset
      else
        state.pc + 4 := by
  simp [execute, nextPc]

theorem execute_branchGe_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchGe sourceLeft sourceRight offset)).pc =
      if signedLess (readRegister state sourceLeft) (readRegister state sourceRight) then
        state.pc + 4
      else
        state.pc + offset := by
  simp [execute, nextPc]

theorem execute_jal_pc (state : State width) (destination : Fin 32)
    (offset : Word width) :
    (execute state (.jal destination offset)).pc = state.pc + offset := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, h]

theorem execute_jal_link (state : State width) (destination : Fin 32)
    (offset : Word width) :
    readRegister (execute state (.jal destination offset)) destination =
        if destination = 0 then readRegister state destination else nextPc state := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, nextPc, h, eq_comm]

def jalrTarget (base offset : Word width) : Word width :=
  (base + offset) &&& BitVec.ofNat width (2 ^ width - 2)

theorem execute_jalr_pc (state : State width) (destination source : Fin 32)
    (offset : Word width) :
    (execute state (.jalr destination source offset)).pc =
      jalrTarget (readRegister state source) offset := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, jalrTarget, h]

theorem execute_jalr_link (state : State width) (destination source : Fin 32)
    (offset : Word width) :
    readRegister (execute state (.jalr destination source offset)) destination =
      if destination = 0 then readRegister state destination else nextPc state := by
  by_cases h : destination = 0 <;>
    simp [execute, writeRegister, readRegister, nextPc, h, eq_comm]

theorem execute_branchLtU_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchLtU sourceLeft sourceRight offset)).pc =
      if readRegister state sourceLeft < readRegister state sourceRight then
        state.pc + offset
      else
        state.pc + 4 := by
  simp [execute, nextPc]

theorem execute_branchGeU_pc (state : State width) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) :
    (execute state (.branchGeU sourceLeft sourceRight offset)).pc =
      if readRegister state sourceLeft < readRegister state sourceRight then
        state.pc + 4
      else
        state.pc + offset := by
  simp [execute, nextPc]

theorem execute_addi_zero_preserved (state : State width) (source : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.addi 0 source immediate)) 0 = readRegister state 0 := by
  simp [execute, nextPc, writeRegister, readRegister]

theorem execute_zeroRegister_preserved [NeZero width] (state : State width)
    (instruction : Instruction width) (zero : ZeroRegister state) :
    ZeroRegister (execute state instruction) := by
  change state.registers 0 = 0 at zero
  cases instruction <;>
    simp [ZeroRegister, execute, nextPc, writeRegister, writeByte, writeWord32,
      writeWordValue_registers, readRegister] <;>
    try split <;> simp_all [eq_comm]
  all_goals change state.registers 0 = 0
  all_goals exact zero

theorem zeroState_zeroRegister [NeZero width] : ZeroRegister (zeroState width) := by
  simp [ZeroRegister, zeroState, readRegister]

end Flapjack.RiscV
