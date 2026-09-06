import Flapjack.RiscV.PanMemory

namespace Flapjack

open RiscV

def riscvFlatTestDomain : PanMemoryDomain (RiscV.Word 64) :=
  fun address => address == 8

def riscvFlatTestMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address =>
    if address == 8 then some (BitVec.ofNat 64 67305985) else none

def riscvFlatZeroMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address => if address == 8 then some 0 else none

example :
    panRiscVReadByte riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 9) =
      some (BitVec.ofNat 64 2) := by
  native_decide

example :
    panRiscVRead32 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) =
      some (BitVec.ofNat 64 67305985) := by
  native_decide

example :
    (do
      let memory ← panRiscVStore32 riscvFlatTestDomain riscvFlatZeroMemory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) (BitVec.ofNat 64 67305985)
      panRiscVRead32 riscvFlatTestDomain memory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8)) =
      some (BitVec.ofNat 64 67305985) := by
  native_decide

example :
    panRiscVRead32 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 2) = none := by
  native_decide

example :
    panRiscVRead16 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) =
      some (BitVec.ofNat 64 513) := by
  native_decide

example :
    (do
      let memory ← panRiscVStore16 riscvFlatTestDomain riscvFlatZeroMemory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) (BitVec.ofNat 64 48879)
      panRiscVRead16 riscvFlatTestDomain memory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8)) =
      some (BitVec.ofNat 64 48879) := by
  native_decide

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.store32 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 67305985)))
        (.return (.load32 (.const (BitVec.ofNat 64 8))))) =
      some [.word (BitVec.ofNat 64 67305985)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg, evalPanRiscVFlatExp,
    panRiscVStore32, panRiscVStoreByte, panRiscVRead32, panRiscVReadByte,
    panRiscVGetByte, panRiscVSetByte, panRiscVByteAlign, panRiscVByteIndex,
    riscvFlatTestDomain, riscvFlatZeroMemory, updatePanValueMap, byteAddress,
    aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 7)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9))))) =
    some [.word (BitVec.ofNat 64 7)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg, evalPanRiscVFlatExp,
    panRiscVStoreByte, panRiscVReadByte, panRiscVGetByte, panRiscVSetByte,
    panRiscVByteAlign, panRiscVByteIndex, riscvFlatTestDomain,
    riscvFlatZeroMemory, updatePanValueMap, byteAddress, aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatTestMemory
      (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
        (.return (.var .local "x"))) =
      some [.word (BitVec.ofNat 64 513)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg,
    evalPanRiscVFlatExp, panRiscVReadShared, panRiscVRead16,
    panRiscVReadByte, panRiscVGetByte, panRiscVByteAlign,
    panRiscVByteIndex, riscvFlatTestDomain, riscvFlatTestMemory,
    updatePanValueMap, byteAddress, aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.shMemStore .op16 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 48879)))
        (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
          (.return (.var .local "x")))) =
      some [.word (BitVec.ofNat 64 48879)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg,
    evalPanRiscVFlatExp, panRiscVReadShared, panRiscVRead16,
    panRiscVReadByte, panRiscVGetByte, panRiscVByteAlign,
    panRiscVByteIndex, panRiscVStoreShared, panRiscVStore16,
    panRiscVStoreByte, panRiscVSetByte, riscvFlatTestDomain,
    riscvFlatZeroMemory, updatePanValueMap, byteAddress, aligned]

def riscvFlatNoFfi : PanFlatFfiHandler (RiscV.Word 64) :=
  fun _ _ _ _ _ locals => some locals

def riscvFlatIncrementFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("increment", ["x"],
    .return (.op .add [.var .local "x", .const (BitVec.ofNat 64 1)]))]

def riscvFlatLocalResultNat
    (result : PanFlatControlResult (RiscV.Word 64)) :
    Option Nat :=
  match result with
  | .normal locals _ _ =>
      match locals "result" with
      | some (.word value) => some value.toNat
      | _ => none
  | _ => none

example :
    (evalPanRiscVFlatProgWithCallsAndFfi [] [] riscvFlatNoFfi
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 4
      (fun _ => none) (fun _ => none) riscvFlatTestDomain
      riscvFlatZeroMemory
      (.while (.const (BitVec.ofNat 64 0))
        (.assign .local "unused" (.const (BitVec.ofNat 64 1))))).map
      (fun result => match result with
      | .normal _ _ _ => true
      | _ => false) = some true := by
  native_decide

example :
    (evalPanRiscVFlatProgWithCallsAndFfi
      [] riscvFlatIncrementFunctions riscvFlatNoFfi
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun _ => none) (fun _ => none) riscvFlatTestDomain
      riscvFlatZeroMemory
      (.call (some (some (.local, "result"), none)) "increment"
        [.const (BitVec.ofNat 64 41)])).bind riscvFlatLocalResultNat =
      some 42 := by
  native_decide

end Flapjack
