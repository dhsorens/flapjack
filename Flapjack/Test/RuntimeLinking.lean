import Flapjack.Pipeline

namespace Flapjack

open RiscV

def runtimeLinkRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def runtimeLinkAllocConfig : StackAllocConfig :=
  { gcStubLocation := stackGcStubLocation, returnLabel := 0,
    firstFreshLabel := stackFunctionFirstLabel }

def runtimeLinkGcConfig : StackGcConfig :=
  { shiftLength := 11, smallShiftLength := 9, lenSize := 32, wordShift := 3,
    wordBits := 64, bytesInWord := 8, immediateScratch := 31 }

example :
    (stackAllocCompileWithSimpleGcAndStoreConsts runtimeLinkAllocConfig
      runtimeLinkGcConfig stackStoreConstsStubLocation
      wordAllocatableRegisters.length
      [(3, (.storeConsts 29 30 (some stackStoreConstsStubLocation) : StackProg Nat))]).map
        Prod.fst = [1, 2, 3] := by
  rfl

example :
    (compileStackProgramNatListWithSimpleGcAndStoreConstsToRiscV (width := 64)
      { services := [] } runtimeLinkRemoveConfig runtimeLinkAllocConfig
      runtimeLinkGcConfig stackStoreConstsStubLocation
      wordAllocatableRegisters.length 0 0
      [(3, (.storeConsts 29 30 (some stackStoreConstsStubLocation) : StackProg Nat))]).isSome := by
  decide +kernel

def runtimeLinkDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

#guard
  (compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGc
    (width := 64) .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) [] runtimeLinkRemoveConfig
    runtimeLinkDeclarations).isSome

end Flapjack
