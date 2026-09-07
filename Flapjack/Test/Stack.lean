import Flapjack.Stack

namespace Flapjack

example :
    wordToStackFfi "sum" 2 3 4 5 =
      (.ffi "sum" 2 3 4 5 0 : StackProg Nat) := by
  rfl

example :
    wordToStackRaise 7 =
      (.call none (.label stackRaiseStubLocation) none : StackProg Nat) := by
  rfl

example :
    stackHandlerSlots false = 3 ∧ stackHandlerSlots true = 5 := by
  decide

example :
    stackArgs 2 4 9 =
      (.seq
        (.seq (.stackAlloc 2)
          (.seq (.stackLoad 9 5) (.stackStore 9 1)))
        (.seq (.stackLoad 9 4) (.stackStore 9 0)) : StackProg Nat) := by
  rfl

example :
    stackHandlerArgs (α := Nat) false 1 6 9 = stackArgs 1 9 9 := by
  rfl

example :
    wordToStackCallWithHandler false 11 2 6 9
      (.return 0) (.raise 1) 20 21 30 31 =
      stackSeq [
        stackPushHandler false 30 31 9,
        stackHandlerArgs false 3 6 9,
        (.call (some ((.return 0 : StackProg Nat), 0, 20, 21)) (.label 11)
          (some ((.raise 1 : StackProg Nat), 31, 30))
          : StackProg Nat)] := by
  rfl

end Flapjack
