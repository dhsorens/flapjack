import Flapjack.CrepeSemantics

/-!
Observable runtime boundary for the Crepe evaluator.

`CrepeSemantics` is intentionally a compact executable model whose handlers
return `Option state`.  CakeML's `crepSem` has a richer machine state and an
observable `FinalFFI` result.  This file ports that boundary without changing
the compact evaluator: it is the state/result vocabulary on which the full
compiler simulation can be built.

The FFI request carries the already decoded word arguments.  Byte-array
decoding and the concrete foreign-state type are deliberately left to the
handler, just as CakeML leaves `call_FFI` abstract.  The runtime still keeps
the memory domains, clock, endianness, and FFI state explicit.
-/

namespace Flapjack

structure CrepRuntimeState (α σ : Type u) where
  locals : Nat → Option α
  globals : α → Option α
  functions : List (CompiledFunction α)
  memory : α → Option α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  byteAlign : α → α
  clock : Nat
  bigEndian : Bool
  ffi : σ
  baseAddress : α
  topAddress : α

inductive CrepRuntimeRequest (α : Type u) where
  | extCall (function : FunName)
      (configuration configurationLength array arrayLength : α)
  | sharedMem (operator : CrepMemOp) (name : Nat) (address : α)
  deriving DecidableEq, Repr

inductive CrepRuntimeFfiResponse (α σ ε : Type u) where
  | returned (state : CrepRuntimeState α σ)
  | final (event : ε)

abbrev CrepRuntimeFfiHandler (α σ ε : Type u) :=
  CrepRuntimeRequest α → CrepRuntimeState α σ → CrepRuntimeFfiResponse α σ ε

inductive CrepRuntimeResult (α ε : Type u) where
  | normal
  | error
  | timeout
  | broke (label : Nat)
  | continued (label : Nat)
  | returned (values : List α)
  | raised (exception : α)
  | finalFfi (event : ε)
  deriving DecidableEq, Repr

abbrev CrepRuntimeStep (α σ ε : Type u) :=
  CrepRuntimeResult α ε × CrepRuntimeState α σ

def crepRuntimeMemWidth : CrepMemOp → Nat
  | .load | .store => 0
  | .load8 | .store8 => 1
  | .load16 | .store16 => 2
  | .load32 | .store32 => 4

def crepRuntimeSharedAddress (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : α :=
  if crepRuntimeMemWidth operator = 0 then address
  else state.byteAlign address

def crepRuntimeSharedAddressValid (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : Bool :=
  state.shMemaddrs (crepRuntimeSharedAddress state operator address)

def crepRuntimeLoad (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memaddrs address then state.memory address else none

def crepRuntimeStore [BEq α] (state : CrepRuntimeState α σ)
    (address value : α) : Option (CrepRuntimeState α σ) :=
  if state.memaddrs address then
    some { state with memory := updateMemory state.memory address value }
  else none

def crepRuntimeExtCall (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    CrepRuntimeStep α σ ε :=
  match state.locals configuration, state.locals configurationLength,
      state.locals array, state.locals arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      match handler (.extCall function configuration configurationLength array arrayLength) state with
      | .returned state => (.normal, state)
      | .final event => (.finalFfi event, state)
  | _, _, _, _ => (.error, state)

def crepRuntimeSharedMem (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : CrepRuntimeStep α σ ε :=
  if crepRuntimeSharedAddressValid state operator address then
    match handler (.sharedMem operator name address) state with
    | .returned state => (.normal, state)
    | .final event => (.finalFfi event, state)
  else
    (.error, state)

def crepRuntimeSharedMemExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) : CrepRuntimeStep α σ ε :=
  match evalCrepFullExp state.locals state.memory state.baseAddress
      state.topAddress address with
  | some address => crepRuntimeSharedMem handler state operator name address
  | none => (.error, state)

def crepRuntimeExtCallExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : CrepExp α) :
    CrepRuntimeStep α σ ε :=
  match evalCrepFullExp state.locals state.memory state.baseAddress
      state.topAddress configuration,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress configurationLength,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress array,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      match handler (.extCall function configuration configurationLength array arrayLength) state with
      | .returned state => (.normal, state)
      | .final event => (.finalFfi event, state)
  | _, _, _, _ => (.error, state)

def evalCrepRuntimeExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad state address
  | .loadGlob address => state.globals address
  | .op operator [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      evalPanShift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

def evalCrepRuntimeExps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (state : CrepRuntimeState α σ) : List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepRuntimeExp state expression
      let values ← evalCrepRuntimeExps state expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

def restoreCrepRuntimeStep (name : Nat) (oldValue : Option α) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, state) =>
      (result, { state with locals := restoreCrepLocal state.locals name oldValue })

def crepRuntimeCallerState (caller callee : CrepRuntimeState α σ) :
    CrepRuntimeState α σ :=
  { caller with
    globals := callee.globals
    functions := callee.functions
    memory := callee.memory
    memaddrs := callee.memaddrs
    shMemaddrs := callee.shMemaddrs
    byteAlign := callee.byteAlign
    clock := callee.clock
    bigEndian := callee.bigEndian
    ffi := callee.ffi
    baseAddress := callee.baseAddress
    topAddress := callee.topAddress }

mutual
  def evalCrepRuntimeCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ →
        Option (List Nat × Option (α × CrepProg α)) → FunName →
        List (CrepExp α) → Option (CrepRuntimeStep α σ ε)
    | 0, _, _, _, _ => none
    | fuel + 1, caller, info, function, arguments =>
        match evalCrepRuntimeExps caller arguments with
        | none => some (.error, caller)
        | some values =>
            match lookupCompiledFunction function caller.functions with
            | none => some (.error, caller)
            | some (parameters, body) =>
                match assignCrepValues (fun _ => none) parameters values with
                | none => some (.error, caller)
                | some calleeLocals =>
                    if caller.clock = 0 then
                      some (.timeout, caller)
                    else
                      let callee :=
                        { caller with
                          locals := calleeLocals
                          clock := caller.clock - 1 }
                      match evalCrepRuntimeProg handler primitive fuel callee body with
                      | none => some (.error, callee)
                      | some (result, callee) =>
                          let callerState := crepRuntimeCallerState caller callee
                          match result with
                          | .normal => some (.normal, callerState)
                          | .returned values =>
                              match info with
                              | none => some (.returned values, callerState)
                              | some (destinations, _) =>
                                  match assignCrepValues caller.locals destinations values with
                                  | some locals =>
                                      some (.normal, { callerState with locals := locals })
                                  | none => some (.error, callerState)
                          | .raised exception =>
                              match info with
                              | some (_, some (caught, continuation)) =>
                                  if caught == exception then
                                    evalCrepRuntimeProg handler primitive fuel
                                      { callerState with locals := caller.locals } continuation
                                  else
                                    some (.raised exception, callerState)
                              | _ => some (.raised exception, callerState)
                          | .broke _label => some (.error, callerState)
                          | .continued _label => some (.error, callerState)
                          | .error => some (.error, callerState)
                          | .timeout => some (.timeout, callerState)
                          | .finalFfi event => some (.finalFfi event, callerState)
    termination_by fuel _ _ _ _ => fuel

  def evalCrepRuntimeProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ → CrepProg α →
        Option (CrepRuntimeStep α σ ε)
    | 0, _, _ => none
    | _fuel + 1, state, .skip => some (.normal, state)
    | fuel + 1, state, .dec name value body =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            let nextState := { state with locals := updateCrepLocal state.locals name value }
            match evalCrepRuntimeProg handler primitive fuel nextState body with
            | none => some (.error, state)
            | some result => some (restoreCrepRuntimeStep name (state.locals name) result)
    | _fuel + 1, state, .assign name value =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            some (.normal, { state with locals := updateCrepLocal state.locals name value })
    | _fuel + 1, state, .primitive names operator arguments =>
        match arguments.mapM state.locals with
        | none => some (.error, state)
        | some arguments =>
            match primitive operator arguments with
            | none => some (.error, state)
            | some values =>
                match assignCrepValues state.locals names values with
                | some locals => some (.normal, { state with locals := locals })
                | none => some (.error, state)
    | _fuel + 1, state, .store address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .store32 address value
    | _fuel + 1, state, .storeByte address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .storeGlob address value =>
        match evalCrepRuntimeExp state value with
        | some value =>
            some (.normal, { state with globals := updateMemory state.globals address value })
        | none => some (.error, state)
    | fuel + 1, state, .seq first second =>
        match evalCrepRuntimeProg handler primitive fuel state first with
        | none => some (.error, state)
        | some (.normal, state) =>
            match evalCrepRuntimeProg handler primitive fuel state second with
            | some result => some result
            | none => some (.error, state)
        | some result => some result
    | fuel + 1, state, .ite condition thenBranch elseBranch =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            match evalCrepRuntimeProg handler primitive fuel state
              (if conditionValue != 0 then thenBranch else elseBranch) with
            | some result => some result
            | none => some (.error, state)
    | fuel + 1, state, .while condition body =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            if conditionValue == 0 then
              some (.normal, state)
            else
              match evalCrepRuntimeProg handler primitive fuel state body with
              | none => some (.error, state)
              | some (.normal, state) =>
                  match evalCrepRuntimeProg handler primitive fuel state
                    (.while condition body) with
                  | some result => some result
                  | none => some (.error, state)
              | some (.continued 0, state) =>
                  match evalCrepRuntimeProg handler primitive fuel state
                    (.while condition body) with
                  | some result => some result
                  | none => some (.error, state)
              | some (.broke 0, state) => some (.normal, state)
              | some (.continued label, state) => some (.continued (label - 1), state)
              | some (.broke label, state) => some (.broke (label - 1), state)
              | some (result, state) => some (result, state)
    | _fuel + 1, state, .break label => some (.broke label, state)
    | _fuel + 1, state, .continue label => some (.continued label, state)
    | fuel + 1, state, .call info function arguments =>
        evalCrepRuntimeCall handler primitive fuel state info function arguments
    | _fuel + 1, state, .extCall function configuration configurationLength array arrayLength =>
        some (crepRuntimeExtCall handler state function
          configuration configurationLength array arrayLength)
    | _fuel + 1, state, .raise exception => some (.raised exception, state)
    | _fuel + 1, state, .return values =>
        match evalCrepRuntimeExps state values with
        | some values => some (.returned values, state)
        | none => some (.error, state)
    | _fuel + 1, state, .shMem operator name address =>
        some (crepRuntimeSharedMemExp handler state operator name address)
    | _fuel + 1, state, .tick =>
        if state.clock = 0 then some (.timeout, state)
        else some (.normal, { state with clock := state.clock - 1 })
    termination_by fuel _ _ => fuel
end

def evalCrepRuntimeResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) (program : CrepProg α) :
    Option (CrepRuntimeResult α ε × CrepRuntimeState α σ) :=
  evalCrepRuntimeProg handler primitive fuel state program

theorem crepRuntimeLoad_memaddrs
    (state : CrepRuntimeState α σ) (address : α)
    (haddress : state.memaddrs address = true) :
    crepRuntimeLoad state address = state.memory address := by
  simp [crepRuntimeLoad, haddress]

theorem crepRuntimeStore_invalid
    [BEq α] (state : CrepRuntimeState α σ) (address value : α)
    (haddress : state.memaddrs address = false) :
    crepRuntimeStore state address value = none := by
  simp [crepRuntimeStore, haddress]

theorem evalCrepRuntimeResult_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state .skip =
      some (.normal, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]

theorem evalCrepRuntimeResult_extCall_final
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (function : FunName) (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : ε)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength : state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hhandler : handler
      (.extCall function configurationValue configurationLengthValue arrayValue arrayLengthValue)
      state = .final event) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.extCall function configuration configurationLength array arrayLength) =
      some (.finalFfi event, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, crepRuntimeExtCall,
    hconfiguration, hconfigurationLength, harray, harrayLength, hhandler]

end Flapjack
