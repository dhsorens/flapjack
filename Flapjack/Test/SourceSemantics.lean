import Flapjack.Semantics

namespace Flapjack

/-! Regression coverage for scoped local declarations in each scalar source
    evaluator.  These are the source-level bindings used by the front-end
    before the structured-value evaluator takes over. -/

example :
    evalPanProg (fun _ => none)
      (.dec "x" .one (.const 7)
        (.return (.var .local "x"))) = some [7] := by
  decide

example :
    (evalPanStateProg (fun _ => none)
      (.dec "x" .one (.const 7)
        (.return (.var .local "x")))).map (fun result => result.2) =
      some [7] := by
  decide

example :
    (evalPanProgWithCalls [] 4 (fun _ => none)
      (.dec "x" .one (.const 7)
        (.return (.var .local "x")))).map (fun result => result.2) =
      some [7] := by
  decide +kernel

example :
    (evalPanProgWithHandlers [] 4 (fun _ => none)
      (.dec "x" .one (.const 7)
        (.return (.var .local "x")))).map (fun result =>
          match result with
          | .returned _ values => values
          | _ => []) = some [7] := by
  decide +kernel

end Flapjack
