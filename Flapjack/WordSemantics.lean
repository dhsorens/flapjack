import Flapjack.RiscV.Backend

/-!
Call-aware executable semantics for the Word intermediate language.

The backend already evaluates individual Word functions. This module adds the
function-table boundary used by `loop_to_word`: arguments are read from the
caller registers, callee parameters are initialized in a fresh register
environment, returned values are assigned to the caller's declared registers,
and memory effects are carried back to the caller. Fuel bounds nested calls.
-/

namespace Flapjack.RiscV

abbrev WordCallReturns (α : Type u) :=
  Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat)

abbrev WordCallHandler (α : Type u) :=
  Option (Nat × WordProg α × Nat × Nat)

def lookupWordFunction [NeZero width] :
    Nat → List (Nat × List Nat × WordProg (Word width)) →
      Option (List Nat × WordProg (Word width))
  | _, [] => none
  | label, (candidate, parameters, body) :: functions =>
      if label == candidate then some (parameters, body)
      else lookupWordFunction label functions

def clearWordRegisters [NeZero width] (state : State width) : State width :=
  { state with registers := fun _ => 0 }

def readWordRegisters [NeZero width] (state : State width) :
    List Nat → Option (List (Word width))
  | [] => some []
  | name :: names => do
      let register ← registerOfNat name
      let values ← readWordRegisters state names
      pure (readRegister state register :: values)

def bindWordRegisters [NeZero width] (state : State width)
    (names : List Nat) (values : List (Word width)) : Option (State width) :=
  if names.length != values.length then none
  else
    (names.zip values).foldl (fun result (name, value) => do
      let state ← result
      let register ← registerOfNat name
      pure (writeRegister state register value)) (some (clearWordRegisters state))

def assignWordRegisters [NeZero width] (state : State width)
    (names : List Nat) (values : List (Word width)) : Option (State width) :=
  if names.length != values.length then none
  else
    (names.zip values).foldl (fun result (name, value) => do
      let state ← result
      let register ← registerOfNat name
      pure (writeRegister state register value)) (some state)

mutual
  def evalWordCall [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → WordCallReturns (Word width) → Option Nat → List Nat →
        WordCallHandler (Word width) →
        Option (State width × List (Word width))
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        if handler.isSome then none
        else
          let target ← target
          let (parameters, body) ← lookupWordFunction target functions
          let values ← readWordRegisters state arguments
          let calleeState ← bindWordRegisters state parameters values
          let result ← evalWordFunctionWithCalls functions fuel calleeState body
          let returnedState := { state with
            memory := result.1.memory
            privilege := result.1.privilege
            mode := result.1.mode }
          match returns with
          | none => some (returnedState, result.2)
          | some (names, _, _, _, _) => do
              let state ← assignWordRegisters returnedState names result.2
              some (state, [])
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordFunctionWithCalls [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → WordProg (Word width) →
        Option (State width × List (Word width))
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalWordCall functions fuel state returns target arguments handler
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFunctionWithCalls functions fuel state first
        if !result.2.isEmpty then some result
        else evalWordFunctionWithCalls functions fuel result.1 second
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFunctionWithCalls functions fuel state thenBranch
        else evalWordFunctionWithCalls functions fuel state elseBranch
    | fuel + 1, state, .mustTerminate body =>
        evalWordFunctionWithCalls functions fuel state body
    | _fuel + 1, state, program => evalWordFunction state program
    termination_by fuel _ _ => fuel
end

/-!
Fuel-bounded execution for Word loops.  The ordinary backend evaluator treats
loop/control-flow constructors as outside its single-instruction API; this
companion evaluator gives the lowered `WordProg.loop` the same control-result
shape as Loop's repeat semantics.
-/
inductive WordLoopResult (width : Nat) [NeZero width] where
  | normal (state : State width)
  | broke (state : State width) (label : Nat)
  | continued (state : State width) (label : Nat)

mutual
  def evalWordLoopProg [NeZero width] :
      Nat → State width → WordProg (Word width) → Option (WordLoopResult width)
    | 0, _, _ => none
    | fuel + 1, state, .seq first second => do
        let result ← evalWordLoopProg fuel state first
        match result with
        | .normal state => evalWordLoopProg fuel state second
        | result => some result
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordLoopProg fuel state thenBranch
        else evalWordLoopProg fuel state elseBranch
    | fuel + 1, state, .loop _ body _ =>
        evalWordLoopRepeat fuel state body
    | fuel + 1, state, .mustTerminate body =>
        evalWordLoopProg fuel state body
    | _fuel + 1, state, .break label => some (.broke state label)
    | _fuel + 1, state, .continue label => some (.continued state label)
    | _fuel + 1, state, program =>
        (evalWordProg state program).map (.normal ·)

  def evalWordLoopRepeat [NeZero width] :
      Nat → State width → WordProg (Word width) → Option (WordLoopResult width)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalWordLoopProg fuel state body
        match result with
        | .normal state => evalWordLoopRepeat fuel state body
        | .continued state 0 => evalWordLoopRepeat fuel state body
        | .broke state 0 => some (.normal state)
        | result => some result
end

/-!
Handler-aware Word loop semantics.  The handler-free loop evaluator above is
useful for isolated loop tests, but a source Loop body may contain calls and
FFI actions.  This evaluator preserves those effects while also propagating
return, raise, break, and continue control results through nested loops.
-/
inductive WordLoopControlResult (width : Nat) [NeZero width] where
  | normal (state : State width)
  | returned (state : State width) (values : List (Word width))
  | raised (state : State width) (exception : Word width)
  | broke (state : State width) (label : Nat)
  | continued (state : State width) (label : Nat)

mutual
  def evalWordLoopCallWithHandlersAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (ffiHandler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordCallReturns (Word width) → Option Nat → List Nat →
        WordCallHandler (Word width) →
        Option (WordLoopControlResult width)
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        let target ← target
        let (parameters, body) ← lookupWordFunction target functions
        let values ← readWordRegisters state arguments
        let calleeState ← bindWordRegisters state parameters values
        let result ← evalWordLoopProgWithHandlersAndFfi functions ffiHandler
          fuel calleeState body
        let returnedState := match result with
          | .normal calleeState => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .returned calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .raised calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .broke calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .continued calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
        match result with
        | .normal _ => some (.normal returnedState)
        | .returned _ values =>
            match returns with
            | none => some (.returned returnedState values)
            | some (names, _, _, _, _) => do
                let state ← assignWordRegisters returnedState names values
                some (.normal state)
        | .raised _ exception =>
            match handler with
            | none => some (.raised returnedState exception)
            | some (name, handlerBody, _, _) => do
                let name ← registerOfNat name
                evalWordLoopProgWithHandlersAndFfi functions ffiHandler fuel
                  (writeRegister returnedState name exception) handlerBody
        | .broke _ label => some (.broke returnedState label)
        | .continued _ label => some (.continued returnedState label)
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordLoopProgWithHandlersAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (ffiHandler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) →
        Option (WordLoopControlResult width)
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalWordLoopCallWithHandlersAndFfi functions ffiHandler fuel state returns
          target arguments handler
    | _fuel + 1, state,
        .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← registerOfNat configuration
        let configurationLength ← registerOfNat configurationLength
        let array ← registerOfNat array
        let arrayLength ← registerOfNat arrayLength
        let state ← ffiHandler function (readRegister state configuration)
          (readRegister state configurationLength) (readRegister state array)
          (readRegister state arrayLength) state
        pure (.normal state)
    | fuel + 1, state, .seq first second => do
        let result ← evalWordLoopProgWithHandlersAndFfi functions ffiHandler
          fuel state first
        match result with
          | .normal state =>
              evalWordLoopProgWithHandlersAndFfi functions ffiHandler fuel state second
          | result => some result
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then
          evalWordLoopProgWithHandlersAndFfi functions ffiHandler fuel state thenBranch
        else
          evalWordLoopProgWithHandlersAndFfi functions ffiHandler fuel state elseBranch
    | fuel + 1, state, .loop _ body _ =>
        evalWordLoopRepeatWithHandlersAndFfi functions ffiHandler fuel state body
    | fuel + 1, state, .mustTerminate body =>
        evalWordLoopProgWithHandlersAndFfi functions ffiHandler fuel state body
    | _fuel + 1, state, .break label => some (.broke state label)
    | _fuel + 1, state, .continue label => some (.continued state label)
    | _fuel + 1, state, .raise exception => do
        let exception ← registerOfNat exception
        pure (.raised state (readRegister state exception))
    | _fuel + 1, state, .return _ values => do
        let values ← values.mapM (fun name => do
          let register ← registerOfNat name
          pure (readRegister state register))
        pure (.returned state values)
    | _fuel + 1, state, program => do
        let (state, values) ← evalWordFunction state program
        if values.isEmpty then some (.normal state)
        else some (.returned state values)
    termination_by fuel _ _ => fuel

  def evalWordLoopRepeatWithHandlersAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (ffiHandler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) →
        Option (WordLoopControlResult width)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalWordLoopProgWithHandlersAndFfi functions ffiHandler
          fuel state body
        match result with
        | .normal state =>
            evalWordLoopRepeatWithHandlersAndFfi functions ffiHandler fuel state body
        | .continued state 0 =>
            evalWordLoopRepeatWithHandlersAndFfi functions ffiHandler fuel state body
        | .broke state 0 => some (.normal state)
        | result => some result
    termination_by fuel _ _ => fuel
end

theorem evalWordLoopProgWithHandlersAndFfi_break [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (ffiHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (label : Nat) :
    evalWordLoopProgWithHandlersAndFfi functions ffiHandler 1 state
      (.break label) = some (.broke state label) := by
  simp [evalWordLoopProgWithHandlersAndFfi]

theorem evalWordLoopProg_break [NeZero width] (state : State width) (label : Nat) :
    evalWordLoopProg 1 state (.break label) =
      some (.broke state label) := by
  simp [evalWordLoopProg]

theorem evalWordLoopProg_continue [NeZero width] (state : State width) (label : Nat) :
    evalWordLoopProg 1 state (.continue label) =
      some (.continued state label) := by
  simp [evalWordLoopProg]

theorem evalWordLoopProg_loop_break [NeZero width]
    (state : State width) (label : Nat) :
    evalWordLoopProg 3 state (.loop [] (.break label) []) =
      if label = 0 then some (.normal state) else some (.broke state label) := by
  cases label with
  | zero => simp [evalWordLoopProg, evalWordLoopRepeat]
  | succ label => simp [evalWordLoopProg, evalWordLoopRepeat]

/-!
Control-result semantics for Word calls with exception handlers.  The older
`evalWordFunctionWithCalls` API intentionally models only successful calls;
this companion API keeps the normal/return/raise distinction needed by the
handler-preserving `loop_to_word` lowering.
-/
inductive WordControlResult (width : Nat) [NeZero width] where
  | normal (state : State width)
  | returned (state : State width) (values : List (Word width))
  | raised (state : State width) (exception : Word width)

mutual
  def evalWordCallWithHandlers [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → WordCallReturns (Word width) → Option Nat → List Nat →
        WordCallHandler (Word width) → Option (WordControlResult width)
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        let target ← target
        let (parameters, body) ← lookupWordFunction target functions
        let values ← readWordRegisters state arguments
        let calleeState ← bindWordRegisters state parameters values
        let result ← evalWordFunctionWithHandlers functions fuel calleeState body
        let returnedState := match result with
          | .normal calleeState => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .returned calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .raised calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
        match result with
        | .normal _ => some (.normal returnedState)
        | .returned _ values =>
            match returns with
            | none => some (.returned returnedState values)
            | some (names, _, _, _, _) => do
                let state ← assignWordRegisters returnedState names values
                some (.normal state)
        | .raised _ exception =>
            match handler with
            | none => some (.raised returnedState exception)
            | some (name, handlerBody, _, _) => do
                let name ← registerOfNat name
                evalWordFunctionWithHandlers functions fuel
                  (writeRegister returnedState name exception) handlerBody
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordFunctionWithHandlers [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → WordProg (Word width) → Option (WordControlResult width)
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalWordCallWithHandlers functions fuel state returns target arguments handler
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFunctionWithHandlers functions fuel state first
        match result with
        | .normal state => evalWordFunctionWithHandlers functions fuel state second
        | result => some result
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFunctionWithHandlers functions fuel state thenBranch
        else evalWordFunctionWithHandlers functions fuel state elseBranch
    | fuel + 1, state, .mustTerminate body =>
        evalWordFunctionWithHandlers functions fuel state body
    | _fuel + 1, state, .raise exception => do
        let exception ← registerOfNat exception
        pure (.raised state (readRegister state exception))
    | _fuel + 1, state, .return _ values => do
        let values ← values.mapM (fun name => do
          let register ← registerOfNat name
          pure (readRegister state register))
        pure (.returned state values)
    | _fuel + 1, state, program => do
        let (state, values) ← evalWordFunction state program
        if values.isEmpty then some (.normal state)
        else some (.returned state values)
    termination_by fuel _ _ => fuel
end

/-!
An explicit host boundary for Word-level foreign calls.  The compiler keeps
the four FFI argument registers and the live-register list in the IR; the
target model cannot determine their external effect, so the handler is part
of the semantic environment.  Ordinary Word programs continue to use the
backend evaluator, while sequences and conditionals recurse through this
boundary.
-/
mutual
  def evalWordFfi [NeZero width]
      (handler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) →
        Option (State width × List (Word width))
    | 0, _, _ => none
    | _fuel + 1, state,
        .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← registerOfNat configuration
        let configurationLength ← registerOfNat configurationLength
        let array ← registerOfNat array
        let arrayLength ← registerOfNat arrayLength
        let state ← handler function (readRegister state configuration)
          (readRegister state configurationLength) (readRegister state array)
          (readRegister state arrayLength) state
        pure (state, [])
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFfi handler fuel state first
        if !result.2.isEmpty then some result
        else evalWordFfi handler fuel result.1 second
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFfi handler fuel state thenBranch
        else evalWordFfi handler fuel state elseBranch
    | fuel + 1, state, .mustTerminate body =>
        evalWordFfi handler fuel state body
    | _fuel + 1, state, program => evalWordFunction state program
    termination_by fuel _ _ => fuel
end

theorem evalWordFfi_single [NeZero width]
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat) :
    evalWordFfi handler 1 state
        (.ffi function configuration configurationLength array arrayLength live) = (do
      let configuration ← registerOfNat configuration
      let configurationLength ← registerOfNat configurationLength
      let array ← registerOfNat array
      let arrayLength ← registerOfNat arrayLength
      let state ← handler function (readRegister state configuration)
        (readRegister state configurationLength) (readRegister state array)
        (readRegister state arrayLength) state
      pure (state, [])) := by
  simp [evalWordFfi]

/-!
The combined control evaluator is the semantic counterpart of the eventual
handler-aware `word_to_stack`/RISC-V lowering.  It deliberately keeps the
foreign host and exception continuation explicit: a callee's register frame
does not escape, but its memory and architectural mode do, while an FFI call
updates the caller state directly.
-/
mutual
  def evalWordCallWithHandlersAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (ffiHandler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordCallReturns (Word width) → Option Nat → List Nat →
        WordCallHandler (Word width) → Option (WordControlResult width)
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        let target ← target
        let (parameters, body) ← lookupWordFunction target functions
        let values ← readWordRegisters state arguments
        let calleeState ← bindWordRegisters state parameters values
        let result ← evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel
          calleeState body
        let returnedState := match result with
          | .normal calleeState => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .returned calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
          | .raised calleeState _ => { state with
              memory := calleeState.memory
              privilege := calleeState.privilege
              mode := calleeState.mode }
        match result with
        | .normal _ => some (.normal returnedState)
        | .returned _ values =>
            match returns with
            | none => some (.returned returnedState values)
            | some (names, _, _, _, _) => do
                let state ← assignWordRegisters returnedState names values
                some (.normal state)
        | .raised _ exception =>
            match handler with
            | none => some (.raised returnedState exception)
            | some (name, handlerBody, _, _) => do
                let name ← registerOfNat name
                evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel
                  (writeRegister returnedState name exception) handlerBody
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordFunctionWithHandlersAndFfi [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width)))
      (ffiHandler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) → Option (WordControlResult width)
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalWordCallWithHandlersAndFfi functions ffiHandler fuel state returns target
          arguments handler
    | _fuel + 1, state,
        .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← registerOfNat configuration
        let configurationLength ← registerOfNat configurationLength
        let array ← registerOfNat array
        let arrayLength ← registerOfNat arrayLength
        let state ← ffiHandler function (readRegister state configuration)
          (readRegister state configurationLength) (readRegister state array)
          (readRegister state arrayLength) state
        pure (.normal state)
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel
          state first
        (match result with
        | .normal state => evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel
            state second
        | .returned state values => some (.returned state values)
        | .raised state exception => some (.raised state exception))
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then
          evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel state thenBranch
        else
          evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel state elseBranch
    | fuel + 1, state, .mustTerminate body =>
        evalWordFunctionWithHandlersAndFfi functions ffiHandler fuel state body
    | _fuel + 1, state, .raise exception => do
        let exception ← registerOfNat exception
        pure (.raised state (readRegister state exception))
    | _fuel + 1, state, .return _ values => do
        let values ← values.mapM (fun name => do
          let register ← registerOfNat name
          pure (readRegister state register))
        pure (.returned state values)
    | _fuel + 1, state, program => do
        let (state, values) ← evalWordFunction state program
        if values.isEmpty then some (.normal state)
        else some (.returned state values)
    termination_by fuel _ _ => fuel
end

theorem evalWordFunctionWithHandlersAndFfi_ffi [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (ffiHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat × List Nat) :
    evalWordFunctionWithHandlersAndFfi functions ffiHandler (fuel + 1) state
      (.ffi function configuration configurationLength array arrayLength live) = (do
      let configuration ← registerOfNat configuration
      let configurationLength ← registerOfNat configurationLength
      let array ← registerOfNat array
      let arrayLength ← registerOfNat arrayLength
      let state ← ffiHandler function (readRegister state configuration)
        (readRegister state configurationLength) (readRegister state array)
        (readRegister state arrayLength) state
      pure (.normal state)) := by
  simp [evalWordFunctionWithHandlersAndFfi]

end Flapjack.RiscV
