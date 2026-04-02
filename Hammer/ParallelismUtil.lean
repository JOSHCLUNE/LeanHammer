import Lean

open Lean Elab Term Meta Tactic

namespace Hammer.Util

/-- Returns the new messages appended to `post` after `preCount` in `reportedPlusUnreported`, for logs that only
    grow by extension (as with `logInfo` / `Lean.Meta.Tactic.TryThis.addSuggestion`). -/
def coreMessageLogDelta (preCount : Nat) (post : MessageLog) : MessageLog :=
  let msgs := post.reportedPlusUnreported
  if msgs.size ≤ preCount then {}
  else Id.run do
    let mut u : PersistentArray Message := {}
    let mut i := preCount
    while i < msgs.size do
      u := u.push msgs[i]!
      i := i + 1
    return { reported := {}, unreported := u, loggedKinds := {} }

/-- `wrapTactic` is borrowed from this Zulip thread:
    https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Run.20tactics.20in.20parallel.20.28asynchronously.29/near/526382362 -/
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken) (stxRef : Syntax) :
  TacticM (α → BaseIO (Except Exception (Option Expr × MessageLog))) := do
  let ctx ← readThe Term.Context
  let termState ← getThe Term.State
  let mvar ← mkFreshExprSyntheticOpaqueMVar (← getMainTarget)
  let runTac? (x : α) : TermElabM (Option Expr × MessageLog) := withRef stxRef do
    try
      Term.withoutModifyingElabMetaStateWithInfo do
        let preCount := (← Core.getMessageLog).reportedPlusUnreported.size
        let ngoals ← Term.withSynthesize (postpone := .no) do
          Tactic.run mvar.mvarId! (tactic x)
        if ngoals.isEmpty then
          let result ← instantiateMVars mvar
          if result.hasExprMVar then return (none, {})
          else
            let tryThisDelta := coreMessageLogDelta preCount (← Core.getMessageLog)
            return (some result, tryThisDelta)
        else return (none, {})
    catch _ =>
      return (none, {})
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let tac (x : α) : CoreM (Option Expr × MessageLog) := do
    let (_captured, r) ←
      IO.FS.withIsolatedStreams (isolateStderr := true) <|
        MetaM.run' (ctx := metaCtx) (s := metaState) <|
          Term.TermElabM.run' (runTac? x) ctx termState
    return r
  let tac ← Lean.Core.wrapAsync tac cancelTk?
  pure (fun x => (tac x).toBaseIO)

/-- `tryAllTacsOnGoal` runs all of the tactics supplied in `tacs` to the main goal. As soon as
    any of the tactics produce a result (of the form `.ok (some res)`), a cancellation token
    is sent to all other tasks. This approach assumes that all of the tactics in `tacs` check
    `Core.checkSystem` with some regularity. -/
def tryAllTacsOnGoal (stxRef : Syntax) (outputAllSuggestions : Bool) (tacs : List (TacticM Unit)) : TacticM Unit := do
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
    | .ok (some res, fwdMsgs) =>
      g.assign res
      Core.setMessageLog ((← Core.getMessageLog) ++ fwdMsgs)
      if outputAllSuggestions then continue
      else IO.CancelToken.set cancelTk; break
    | .ok (none, _) => continue -- Tactic failed but didn't yield an error
    | .error _ => continue -- Tactic yielded an error

end Hammer.Util
