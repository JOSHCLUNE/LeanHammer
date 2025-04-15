import Duper

open Lean Meta Auto Elab Tactic Parser Tactic Duper

initialize Lean.registerTraceClass `hammer.debug

namespace HammerCore

/-- Returns true if `e` contains a name `n` where `p n` is true. Copied from `Mathlib.Lean.Expr.Basic.lean` -/
def containsConst (e : Expr) (p : Name → Bool) : Bool :=
  Option.isSome <| e.find? fun | .const n _ => p n | _ => false

def unsatCoreIncludesFact (unsatCoreDerivLeafStrings : Array String) (fact : Term) : Bool := Id.run do
  unsatCoreDerivLeafStrings.anyM
    (fun factStr => do
      -- **TODO** Modify `Duper.collectAssumptions` to output a leaf containing `s!"❰{factStx}❱"` so that we only need to check if `factStr` contains `s!"❰{fact}❱"`
      if factStr == s!"❰{fact}❱" then pure true
      else
        let [_isFromGoal, _includeInSetOfSupport, factStrStx] := factStr.splitOn ", "
          | pure false
        pure $ factStrStx == s!"{fact}"
    )

/-- **TODO** Write docstring -/
def getDuperCoreLemmas (unsatCoreDerivLeafStrings : Array String) (userFacts : Syntax.TSepArray `term ",") (goalDecls : Array LocalDecl)
  (includeAllLctx : Bool) (duperConfigOptions : Duper.ConfigurationOptions) : TacticM (Array FVarId × Array Term × Expr) := do
  Core.checkSystem s!"{decl_name%}"
  let lctx ← getLCtx
  -- Filter `userFacts` to only include facts that appear in the extnernal prover's unsat core
  let userFacts : Array Term := userFacts
  let mut coreUserFacts := #[]
  for factStx in userFacts do
    if unsatCoreIncludesFact unsatCoreDerivLeafStrings factStx then
      coreUserFacts := coreUserFacts.push factStx
  -- Build `formulas` to pass into `runDuperPortfolioMode`
  trace[hammer.debug] "{decl_name%} :: Collecting assumptions. coreUserFacts: {coreUserFacts}"
  let mut formulas := (← collectAssumptions coreUserFacts includeAllLctx goalDecls).toArray
  -- Try to reconstruct the proof using `runDuperPortfolioMode`
  let prf ←
    try
      Core.checkSystem s!"{decl_name%} :: runDuperPortfolioMode"
      trace[hammer.debug] "{decl_name%} :: Calling runDuperPortfolioMode with formulas: {formulas}"
      runDuperPortfolioMode formulas.toList [] none duperConfigOptions none
    catch e =>
      throwError m!"{decl_name%} :: Unable to use hints from external solver to reconstruct proof. " ++
                  m!"Duper threw the following error:\n\n{e.toMessageData}"
  -- Find `lctxFactsInProof`
  let mut lctxFactsInProof := #[]
  for declOpt in lctx.decls do
    match declOpt with
    | none => continue
    | some decl =>
      -- **TODO** Write a variant of `runDuperPortfolioMode` that returns the list of facts that were used to reconstruct the proof (current approach is brittle)
      if (← inferType decl.type).isProp && prf.containsFVar decl.fvarId then
        lctxFactsInProof := lctxFactsInProof.push decl.fvarId
  -- Determine which of the non-lctx facts that were passed into `hammer` appear in `prf`
  let mut userInputFactsInProof := #[]
  for factStx in userFacts do
    -- **TODO** Write a variant of `runDuperPortfolioMode` that returns the list of facts that were used to reconstruct the proof (current approach is brittle)
    let factName := factStx.raw.getId
    if containsConst prf (fun n => n == factName) then
      userInputFactsInProof := userInputFactsInProof.push factStx
  pure (lctxFactsInProof, userInputFactsInProof, prf)

end HammerCore
