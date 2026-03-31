import Lean

open Lean Elab Term Meta Tactic

/-- `wrapTactic` is borrowed from this Zulip thread:
    https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Run.20tactics.20in.20parallel.20.28asynchronously.29/near/526382362 -/
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken) (stxRef : Syntax) :
  TacticM (α → BaseIO (Except Exception (Option Expr))) := do
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let mvar ← mkFreshExprSyntheticOpaqueMVar (← getMainTarget)
  let s ← ref.get
  let runTac? (x : α) : TermElabM (Option Expr) := withRef stxRef do
    try
      Term.withoutModifyingElabMetaStateWithInfo do
        let ngoals ← Term.withSynthesize (postpone := .no) do
          Tactic.run mvar.mvarId! (tactic x)
        if ngoals.isEmpty then
          let result ← instantiateMVars mvar
          if result.hasExprMVar then return none
          else return some result
        else return none
    catch _ =>
      return none
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let tac (x : α) := MetaM.run' (ctx := metaCtx) (s := metaState) $ Term.TermElabM.run' (runTac? x) ctx s
  let tac ← Lean.Core.wrapAsync tac cancelTk?
  pure (fun x => (tac x).toBaseIO)

/-- `tryAllTacsOnGoal` runs all of the tactics supplied in `tacs` to the main goal. As soon as
    any of the tactics produce a result (of the form `.ok (some res)`), a cancellation token
    is sent to all other tasks. This approach assumes that all of the tactics in `tacs` check
    `Core.checkSystem` with some regularity. -/
def tryAllTacsOnGoal (stxRef : Syntax) (tacs : List (TacticM Unit)) : TacticM Unit := do
  let g ← getMainGoal
  let mut tasks := #[]
  let cancelTk ← IO.CancelToken.new
  -- Create tasks
  for tac in tacs do
    let wrappedTac ← pure ((← wrapTactic (fun () => tac) cancelTk stxRef) ())
    tasks := tasks.push (← (BaseIO.asTask wrappedTac))
  let mut remainingTasks := tasks.toList
  while h : 0 < remainingTasks.length do
    let (firstRes, otherTasks) ← IO.waitAny' remainingTasks h
    remainingTasks := otherTasks
    match firstRes with
    | .ok (some res) =>
      g.assign res
      IO.CancelToken.set cancelTk
      break -- I think it should also work to make this continue?
    | .ok none => continue -- Tactic failed but didn't yield an error
    | .error _ => continue -- Tactic yielded an error

/- Testing
def fail : TacticM Unit := return ()
def sorry' : TacticM Unit := do IO.sleep 400; evalTactic $ ← `(tactic| sorry)
def succeed : TacticM Unit := do IO.sleep 50; evalTactic $ ← `(tactic| rfl)
-- def loop : TacticM Unit := do while true do Core.checkSystem "loop";
def loop : TacticM Unit := do let mut canceled := false; while !canceled do checkSystem "loop";

def tryFailSucceed : TacticM Unit := tryAllTacsOnGoal [fail, succeed, sorry', succeed, loop]

elab "tryFailSucceed" : tactic => do tryFailSucceed

example : 0 = 0 := by
  sorry -- tryFailSucceed
-/
