import Duper

open Lean Meta Auto Elab Tactic Parser Tactic Duper

initialize Lean.registerTraceClass `hammer.debug

namespace HammerCore

/-- Returns true if `e` contains a name `n` where `p n` is true. Copied from `Mathlib.Lean.Expr.Basic.lean` -/
def containsConst (e : Expr) (p : Name → Bool) : Bool :=
  Option.isSome <| e.find? fun | .const n _ => p n | _ => false

/-- Checks `unsatCoreDerivLeafStrings` to see if it contains a string that matches `fact`. -/
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

/-- Like `unsatCoreIncludesFact` but takes `fact` as a String instead of a Term. -/
def unsatCoreIncludesFactAsString (unsatCoreDerivLeafStrings : Array String) (fact : String) : Bool := Id.run do
  unsatCoreDerivLeafStrings.anyM
    (fun factStr => do
      -- **TODO** Modify `Duper.collectAssumptions` to output a leaf containing `s!"❰{factStx}❱"` so that we only need to check if `factStr` contains `s!"❰{fact}❱"`
      if factStr == s!"❰{fact}❱" then pure true
      else
        let [_isFromGoal, _includeInSetOfSupport, factStrStx] := factStr.splitOn ", "
          | pure false
        pure $ factStrStx == s!"{fact}"
    )

/- **TODO** If `Duper.formulasToAutoLemmas` were modified to include identifier information for fVarIds from the local context (rather than just include identifier
   information to track facts explicitly passed in as terms), then we could use Zipperposition's unsat core to also minimize the set of lctx facts that are sent to Duper
   (potentially improving `hammer`'s performance on problems with very large local contexts). This behavior should maybe be added as an option (since even if it improves
   `hammer`'s performance on some problems, it will increase the size of the suggested Duper invocations on all problems), but I definitely think this is worth implementing. -/
/-- **TODO** Write docstring -/
def getDuperCoreLemmas (unsatCoreDerivLeafStrings : Array String) (userFacts : Syntax.TSepArray `term ",") (goalDecls : Array LocalDecl)
  (includeAllLctx : Bool) (duperConfigOptions : Duper.ConfigurationOptions) : TacticM (Array Term × Expr) := do
  Core.checkSystem s!"{decl_name%}"
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
  -- Determine which of the user provided facts appear in `prf`
  let mut userInputFactsInProof := #[]
  for factStx in userFacts do
    -- **TODO** Write a variant of `runDuperPortfolioMode` that returns the list of facts that were used to reconstruct the proof (current approach is brittle)
    -- **TODO** Add support for userFacts that aren't just names of premises (e.g. `(by omega : 1 + 1 = 2)`)
    let factName := factStx.raw.getId
    if containsConst prf (fun n => n == factName) then
      userInputFactsInProof := userInputFactsInProof.push factStx
  pure (userInputFactsInProof, prf)

end HammerCore
