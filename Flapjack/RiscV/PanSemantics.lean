import Flapjack.PanValues
import Flapjack.LoopSemantics
import Flapjack.RiscV.Model

/-!
RISC-V word semantics for Pancake's source-level `AddCarry` primitive.

CakeML defines the primitive over fixed-width words: the result is the
low-width part of `left + right + carry`, and the second field records whether
the mathematical sum overflowed the word width.  The generic source evaluator
receives this operation through `PanPrimitiveHandler`, keeping the source
language independent of the chosen target word representation.
-/

namespace Flapjack.RiscV

def addCarryWords [NeZero width] (left right carry : Word width) :
    Word width × Word width :=
  let total := left.toNat + right.toNat + if carry == 0 then 0 else 1
  (BitVec.ofNat width total,
    BitVec.ofNat width (if 2 ^ width ≤ total then 1 else 0))

def panPrimitiveHandler [NeZero width] :
    PanPrimitiveHandler (Word width)
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, carryOut) := addCarryWords left right carry
      some (.rStruct [.word result, .word carryOut])
  | _, _ => none

def loopPrimitiveHandler [NeZero width] :
    LoopPrimitiveHandler (Word width)
  | .addCarry, [left, right, carry] =>
      let (result, carryOut) := addCarryWords left right carry
      some [result, carryOut]
  | _, _ => none

theorem addCarryWords_no_overflow [NeZero width]
    (left right : Word width) :
    (addCarryWords left right (BitVec.ofNat width 0)).2 =
      BitVec.ofNat width
        (if 2 ^ width ≤ left.toNat + right.toNat then 1 else 0) := by
  simp [addCarryWords]

/-!
The six-instruction RISC-V lowering computes the same pair as
`addCarryWords`.  The first `sltu` turns an arbitrary carry word into a
single bit; the two later `sltu`s detect overflow from the two additions, and
the final `or` combines those flags.
-/
theorem addCarryWords_riscv_formula [NeZero width]
    (left right carry : Word width) :
    addCarryWords left right carry =
      (left + right + if 0#width < carry then 1#width else 0#width,
        if left + right < right then 1#width else 0#width |||
          if left + right + (if 0#width < carry then 1#width else 0#width) <
              (if 0#width < carry then 1#width else 0#width) then
            1#width
          else 0#width) := by
  have hleft : left.toNat < 2 ^ width := left.isLt
  have hright : right.toNat < 2 ^ width := right.isLt
  have hone_mod : 1 % 2 ^ width = 1 := by
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))
  have ofNat_mod (n : Nat) :
      BitVec.ofNat width (n % 2 ^ width) = BitVec.ofNat width n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  by_cases hcarry : carry = 0#width
  · by_cases hsum : left.toNat + right.toNat < 2 ^ width
    · simp [addCarryWords, hcarry, BitVec.add_def,
        BitVec.lt_def, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsum,
        show ¬ 2 ^ width ≤ left.toNat + right.toNat by omega,
        show ¬ left.toNat + right.toNat < right.toNat by omega]
    · have hsum_mod :
          (left.toNat + right.toNat) % 2 ^ width =
            left.toNat + right.toNat - 2 ^ width := by
        rw [Nat.mod_eq_sub_mod (by omega)]
        apply Nat.mod_eq_of_lt
        have hsum_lt_two : left.toNat + right.toNat <
            2 ^ width + 2 ^ width := by omega
        omega
      have hsum_sub_lt : left.toNat + right.toNat - 2 ^ width <
          2 ^ width := by
        have hsum_lt_two : left.toNat + right.toNat <
            2 ^ width + 2 ^ width := by omega
        omega
      have hsum_ofNat :
          BitVec.ofNat width (left.toNat + right.toNat) =
            BitVec.ofNat width (left.toNat + right.toNat - 2 ^ width) := by
        rw [← hsum_mod]
        exact (ofNat_mod (left.toNat + right.toNat)).symm
      have hwrap_mod :
          (left.toNat + right.toNat - 2 ^ width) % 2 ^ width =
            left.toNat + right.toNat - 2 ^ width :=
        Nat.mod_eq_of_lt hsum_sub_lt
      have hwrap_lt_right :
          left.toNat + right.toNat - 2 ^ width < right.toNat := by
        omega
      have hsum_ge : 2 ^ width ≤ left.toNat + right.toNat := by omega
      simp [addCarryWords, hcarry, BitVec.add_def,
        BitVec.lt_def, BitVec.toNat_ofNat, hsum_ofNat, hwrap_mod,
        hwrap_lt_right, hsum_ge]
  · have hcarry_pos : 0#width < carry := by
      have hcarry_nat : carry.toNat ≠ 0 := by
        intro hzero
        apply hcarry
        exact BitVec.eq_of_toNat_eq (by simpa using hzero)
      simp [BitVec.lt_def]
      omega
    by_cases hsum : left.toNat + right.toNat < 2 ^ width
    · by_cases hsum_plus : left.toNat + right.toNat + 1 < 2 ^ width
      · simp [addCarryWords, hcarry, hcarry_pos, 
          BitVec.add_def, BitVec.lt_def, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hsum_plus,
          show ¬ 2 ^ width ≤ left.toNat + right.toNat + 1 by omega,
          show ¬ left.toNat + right.toNat < right.toNat by omega,
          hone_mod]
      · have hsum_plus_mod :
            (left.toNat + right.toNat + 1) % 2 ^ width =
              left.toNat + right.toNat + 1 - 2 ^ width := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          apply Nat.mod_eq_of_lt
          have hsum_plus_lt_two : left.toNat + right.toNat + 1 <
              2 ^ width + 2 ^ width := by omega
          omega
        simp [addCarryWords, hcarry, hcarry_pos, 
          hsum_plus_mod, BitVec.add_def, BitVec.lt_def,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum, hone_mod,
          show ¬ left.toNat + right.toNat < right.toNat by omega,
          show left.toNat + right.toNat + 1 - 2 ^ width < 1 by omega,
          show 2 ^ width ≤ left.toNat + right.toNat + 1 by omega]
    · have hsum_mod :
          (left.toNat + right.toNat) % 2 ^ width =
            left.toNat + right.toNat - 2 ^ width := by
        rw [Nat.mod_eq_sub_mod (by omega)]
        apply Nat.mod_eq_of_lt
        have hsum_lt_two : left.toNat + right.toNat <
            2 ^ width + 2 ^ width := by omega
        omega
      have hsum_ge : 2 ^ width ≤ left.toNat + right.toNat := by omega
      have htotal_mod :
          (left.toNat + right.toNat + 1) % 2 ^ width =
            (left.toNat + right.toNat - 2 ^ width + 1) % 2 ^ width := by
        rw [Nat.mod_eq_sub_mod (by omega)]
        rw [show left.toNat + right.toNat + 1 - 2 ^ width =
          left.toNat + right.toNat - 2 ^ width + 1 by omega]
      have htotal_ofNat :
          BitVec.ofNat width (left.toNat + right.toNat + 1) =
            BitVec.ofNat width (left.toNat + right.toNat - 2 ^ width + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofNat, htotal_mod]
      have hwrap_lt_right :
          left.toNat + right.toNat - 2 ^ width < right.toNat := by
        omega
      simp [addCarryWords, hcarry, hcarry_pos, hsum_mod,
        BitVec.add_def, BitVec.lt_def, BitVec.toNat_ofNat, htotal_ofNat,
        hwrap_lt_right, hone_mod,
        show 2 ^ width ≤ left.toNat + right.toNat + 1 by omega]
theorem panPrimitiveHandler_addCarry [NeZero width]
    (left right : Word width) :
    panPrimitiveHandler .addCarry
      [.word left, .word right, .word (BitVec.ofNat width 0)] =
      some (.rStruct [
        .word (BitVec.ofNat width (left.toNat + right.toNat)),
        .word (BitVec.ofNat width
          (if 2 ^ width ≤ left.toNat + right.toNat then 1 else 0))]) := by
  simp [panPrimitiveHandler, addCarryWords]

end Flapjack.RiscV
