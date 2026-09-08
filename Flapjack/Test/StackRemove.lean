import Flapjack.StackRemove

namespace Flapjack

def stackRemoveTestConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    stackRemove stackRemoveTestConfig (.get 4 .heapLength : StackProg Nat) =
      .seq (.seq (.const 29 24) (.arith .sub 29 10 29))
        (.inst (.mem .load 4 29)) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.get 4 .heapLength : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveGet, stackRemoveJoin,
    stackRemoveAddress, stackStorePosition, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.set .globals 6 : StackProg Nat) =
      .seq (.seq (.const 29 64) (.arith .sub 29 10 29))
        (.inst (.mem .store 6 29)) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.set .globals 6 : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveSet, stackRemoveJoin,
    stackRemoveAddress, stackStorePosition, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackAlloc 2 : StackProg Nat) =
      .seq (.const 31 16) (.arith .sub 20 20 31) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackAlloc,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackFree 2 : StackProg Nat) =
      .seq (.const 31 16) (.arith .add 20 20 31) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackFree,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackAlloc 256 : StackProg Nat) =
      .seq
        (.seq (.const 31 2040) (.arith .sub 20 20 31))
        (.seq (.const 31 8) (.arith .sub 20 20 31)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackAlloc,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackStore 6 2 : StackProg Nat) =
      .seq (.arith .or 31 6 6)
        (.seq (.seq (.const 29 16) (.arith .add 29 20 29))
          (.inst (.mem .store 31 29))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackStore,
    stackRemoveStackAddress, stackRemoveMove, stackRemoveJoin,
    stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackLoad 6 2 : StackProg Nat) =
      .seq (.seq (.const 29 16) (.arith .add 29 20 29))
        (.inst (.mem .load 6 29)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackLoad,
    stackRemoveStackAddress, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackLoadAny 6 7 : StackProg Nat) =
      .seq (.arith .add 29 20 7) (.inst (.mem .load 6 29)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackLoadAny,
    stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackStoreAny 6 7 : StackProg Nat) =
      .seq (.arith .or 31 6 6)
        (.seq (.arith .add 29 20 7) (.inst (.mem .store 31 29))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackStoreAny,
    stackRemoveMove, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.opCurrHeap .add 6 7 : StackProg Nat) =
      .arith .add 6 7 12 := by
  simp [stackRemove, stackRemoveFuel, stackRemoveOpCurrHeap,
    stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackGetSize 6 : StackProg Nat) =
      .seq (.arith .or 6 20 20)
        (.seq (.arith .sub 6 6 21)
          (.seq (.const 31 3) (.shift .lsr 6 6 31))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackGetSize,
    stackRemoveMove, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackSetSize 6 : StackProg Nat) =
      .seq (.const 31 3)
        (.seq (.shift .lsl 6 6 31)
          (.seq (.arith .or 20 21 21) (.arith .add 20 20 6))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackSetSize,
    stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackGetSize 31 : StackProg Nat) =
      .seq (.arith .or 31 20 20)
        (.seq (.arith .sub 31 31 21)
          (.seq (.const 29 3) (.shift .lsr 31 31 29))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackGetSize,
    stackRemoveMove, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackSetSize 31 : StackProg Nat) =
      .seq (.const 29 3)
        (.seq (.shift .lsl 31 31 29)
          (.seq (.arith .or 20 21 21) (.arith .add 20 20 31))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackSetSize,
    stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.bitmapLoad 6 7 : StackProg Nat) =
      .seq
        (.seq (.seq (.const 29 88) (.arith .sub 29 10 29))
          (.inst (.mem .load 6 29)))
        (.seq (.arith .add 6 6 7)
          (.seq (.const 31 3)
            (.seq (.shift .lsl 6 6 31) (.inst (.mem .load 6 6))))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveBitmapLoad,
    stackRemoveGet, stackRemoveAddress, stackRemoveJoin,
    stackStorePosition, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig
      (.dataBufferWrite 7 6 : StackProg Nat) =
      (.inst (.mem .store 6 7) : StackProg Nat) := by
  simp [stackRemove, stackRemoveFuel]

example :
    stackRemove stackRemoveTestConfig
      (.storeConsts 6 7 none : StackProg Nat) =
      stackRemoveStoreConsts stackRemoveTestConfig 6 7 none := by
  simp [stackRemove, stackRemoveFuel]

example :
    stackRemoveCopyLoop stackRemoveTestConfig 6 7 =
      .seq (.inst (.mem .load 1 7))
        (.seq (.arith .add 7 7 31)
          (.seq
            (.loop (.ite .less 1 (.imm (0 : Nat))
              (.seq (stackRemoveCopyEach stackRemoveTestConfig 6 7)
                (.seq (.inst (.mem .load 1 7))
                  (.arith .add 7 7 31)))
              (.break 0)))
            (stackRemoveCopyEach stackRemoveTestConfig 6 7))) := by
  rfl

example :
    stackRemove stackRemoveTestConfig (.get 4 .currHeap : StackProg Nat) =
      .arith .or 4 12 12 := by
  exact stackRemove_get_currHeap _ _

example :
    stackRemove stackRemoveTestConfig
        (.seq (.get 4 .heapLength)
          (.loop (.set .handler 6)) : StackProg Nat) =
      .seq
        (.seq (.seq (.const 29 24) (.arith .sub 29 10 29))
          (.inst (.mem .load 4 29)))
        (.loop (.seq (.seq (.const 29 56) (.arith .sub 29 10 29))
          (.inst (.mem .store 6 29)))) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.seq (.get 4 .heapLength)
        (.loop (.set .handler 6)) : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveGet, stackRemoveJoin,
    stackRemoveAddress, stackRemoveSet, stackRemoveTestConfig,
    stackRemoveJoin, stackRemoveAddress, stackStorePosition]

end Flapjack
