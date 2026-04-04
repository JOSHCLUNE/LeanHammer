import Lean

open Lean Elab Term Meta Tactic

namespace Hammer.Util

mutual
  /-- A helper function for `proofExprIncomplete` which checks whether `e` has any unnasigned metavariables or depends on `sorryAx`.
      `visitExprForIncomplete` sets `found` to `true` if it determines that the answer is yes, and does not modify `found` otherwise.
      `checkedConstsRef` is used to keep track of the set of auxiliary constants that have already been checked. -/
  private partial def visitExprForIncomplete (e : Expr) (found : IO.Ref Bool) (checkedConstsRef : IO.Ref NameHashSet) : MetaM Unit := do
    let e ← instantiateExprMVars e
    if (← found.get) then return ()
    if e.hasExprMVar || e.hasSorry then found.set true; return ()
    Meta.forEachExpr e fun sub => do
      if (← found.get) then return ()
      match sub with
      | .const n _ => visitConstForIncomplete n found checkedConstsRef
      | _ => pure ()

  /-- A helper function for `proofExprIncomplete` which checks whether the value corresponding to `.const n` has any unnasigned metavariables
      or depends on `sorryAx`. `visitConstForIncomplete` sets `found` to `true` if it determines that the answer is yes, and does not modify
      `found` otherwise. `checkedConstsRef` is used to keep track of the set of auxiliary constants that have already been checked. -/
  private partial def visitConstForIncomplete (n : Name) (found : IO.Ref Bool) (checkedConstsRef : IO.Ref NameHashSet) : MetaM Unit := do
    if (← found.get) then return ()
    let checkedConsts ← checkedConstsRef.get
    if checkedConsts.contains n then return ()
    checkedConstsRef.set (checkedConsts.insert n)
    let env ← getEnv
    match env.find? n with
    | none => pure ()
    | some ci =>
      match ci.value? with
      | none => pure ()
      | some val => visitExprForIncomplete val found checkedConstsRef
end

/-- Checks whether `e` has any unassigned metavariables or depends on `sorryAx`. Returns `true` if so and `false` if not. -/
def proofExprIncomplete (e : Expr) : MetaM Bool := do
  let e ← instantiateExprMVars e
  if e.hasExprMVar || e.hasSorry then return true
  let found ← IO.mkRef false
  let expanded ← IO.mkRef ({} : NameHashSet)
  visitExprForIncomplete e found expanded
  found.get

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

/-- Inlines bodies of constants that appear in `e` but are absent from `env0` (typically auxiliary
    definitions created by tactics such as `grind` or `omega` during an isolated elaboration run).
    Must be executed while the current environment still contains those constants. -/
partial def inlineFreshProofs (env0 : Environment) (e : Expr) : MetaM Expr := do
  let rec inline (e : Expr) : MetaM Expr := do
    match e with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure e
    | .const declName us =>
      if env0.contains declName then pure e
      else
        let env ← getEnv
        let some ci := env.find? declName
          | pure e
        let some body := ci.value? (allowOpaque := true)
          | throwError "LeanHammer: could not inline auxiliary constant {declName}"
        let levelMap :=
          Std.HashMap.ofList (List.zip (ci.levelParams.map Level.param) us)
        let body := body.replaceLevel (levelMap.get?)
        inline body
    | .app fn arg => return .app (← inline fn) (← inline arg)
    | .lam name ty body bi => return .lam name (← inline ty) (← inline body) bi
    | .forallE name ty body bi => return .forallE name (← inline ty) (← inline body) bi
    | .letE name ty val body nd => return .letE name (← inline ty) (← inline val) (← inline body) nd
    | .mdata d e => return .mdata d (← inline e)
    | .proj s i e => return .proj s i (← inline e)
  inline (← instantiateExprMVars e)

/-- `wrapTactic` is borrowed from this Zulip thread:
    https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Run.20tactics.20in.20parallel.20.28asynchronously.29/near/526382362 -/
def wrapTactic {α : Type} (tactic : α → TacticM Unit) (cancelTk? : Option IO.CancelToken) (stxRef : Syntax) :
  TacticM (α → BaseIO (Except Exception (Option Expr × MessageLog))) := do
  let env0 ← getEnv
  let ctx ← readThe Term.Context
  let termState ← getThe Term.State
  let metaCtx ← readThe Meta.Context
  -- Take `metaState` after `mkFreshExprSyntheticOpaqueMVar`: that extends `mctx` with the goal mvar.
  let mvar ← mkFreshExprSyntheticOpaqueMVar (← getMainTarget)
  let metaState ← getThe Meta.State
  let runTac? (x : α) : TermElabM (Option Expr × MessageLog) := withRef stxRef do
    try
      Term.withoutModifyingElabMetaStateWithInfo do
        let preCount := (← Core.getMessageLog).reportedPlusUnreported.size
        let ngoals ← Term.withSynthesize (postpone := .no) do
          Tactic.run mvar.mvarId! (tactic x)
        let tryThisDelta := coreMessageLogDelta preCount (← Core.getMessageLog)
        if ngoals.isEmpty then
          let result ← instantiateMVars mvar
          let result ← try inlineFreshProofs env0 result catch _ => return (none, tryThisDelta)
          if (← proofExprIncomplete result) then return (none, tryThisDelta)
          else return (some result, tryThisDelta)
        else return (none, tryThisDelta)
    catch _ =>
      return (none, {})
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
  let mut foundCompleteProof := false
  let mut completeSuggestions ← Core.getMessageLog
  let mut incompleteSuggestions ← Core.getMessageLog
  while h : 0 < remainingTasks.length do
    let (firstRes, otherTasks) ← IO.waitAny' remainingTasks h
    remainingTasks := otherTasks
    match firstRes with
    | .ok (some res, fwdMsgs) =>
      g.assign res
      foundCompleteProof := true
      completeSuggestions := completeSuggestions ++ fwdMsgs
      if outputAllSuggestions then continue
      else IO.CancelToken.set cancelTk; break
    | .ok (none, fwdMsgs) => -- Tactic failed but didn't yield an error
      incompleteSuggestions := incompleteSuggestions ++ fwdMsgs
      continue
    | .error _ => continue -- Tactic yielded an error
  -- If any tactics returned with a complete success, only show the complete successes. Partial suggestions
  -- containing `sorry` should only be shown if none of the attempted tactics could find a complete proof.
  if foundCompleteProof then Core.setMessageLog completeSuggestions
  else Core.setMessageLog incompleteSuggestions

end Hammer.Util
