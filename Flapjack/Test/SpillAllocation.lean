import Flapjack.RiscV.WordToStack

/-!
Regression for the public spill-aware Word-to-Stack entry point.  It verifies
that the allocator's locations replace only the location map while frame and
bitmap configuration remain unchanged.
-/

namespace Flapjack.RiscV

example [NeZero width] (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordSpillState) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    wordToStackFunctionWithSpillStateAndLocationBitmaps config parameters
        allocation registerCount bitmapRegister frameSlots storeConstsStub state program =
      wordToStackFunctionWithParametersAndLocationBitmaps
        { config with locations := allocation.locations }
        parameters registerCount bitmapRegister frameSlots storeConstsStub state program := by
  rfl

example [NeZero width] (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordGraphAllocation) (colours stackStart : Nat)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps config parameters
        allocation colours stackStart registerCount bitmapRegister frameSlots
        storeConstsStub state program =
      wordToStackFunctionWithParametersAndLocationBitmaps
        { config with locations := wordGraphLocations allocation colours stackStart }
        parameters registerCount bitmapRegister frameSlots storeConstsStub state program := by
  rfl

/-! The graph allocator, rather than only its location-map adapter, reaches
the bitmap-aware StackLang function entry point on a concrete function. -/
#guard
    (wordAllocateGraphFunctionWithStackOnlyToStack
      { locations := [], scratch := 31, stackBase := 0, addressScratch := 29 }
      [2] (.assign 3 (.var 2) : WordProg (Word 64)) [] 13 14 13 14 13 none
      (wordStackInitialBitmaps false)).isSome = true

end Flapjack.RiscV
