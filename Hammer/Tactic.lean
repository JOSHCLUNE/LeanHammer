import Hammer.HammerCore
import Hammer.ParallelismUtil
import PremiseSelection
import Aesop
import Qq

initialize Lean.registerTraceClass `hammer.premises

namespace Hammer

open Lean Meta Elab Tactic HammerCore Syntax LibrarySuggestions Duper Aesop Qq Util

syntax (name := hammer) "hammer" (ppSpace "[" (term),* "]")? (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

set_library_suggestions open Lean.LibrarySuggestions in Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile

/-- This functions produces one Aesop call where Aesop is given:
    - unsafe rules corresponding to individual premise applications (these are determined by `addIdentStxs`).
    - one unsafe rule to call the Lean-auto/Zipperposition/Duper pipeline (if `configOptions.disableAuto` is
      set to `false`). The premises passed into this pipeline is determined by `autoPremises`.
    - one unsafe rule to call `grind?` (if `configOptions.disableGrind` is set to `false`). The premises passed
      to `grind?` are determined by `grindPremiseNames`.

    This function is entirely sequential. Parallel calls to subcomponents are handled elsewhere. -/
def runAesopWithSubprocedures (autoPremises : Array Term) (addIdentStxs : TSyntaxArray `Aesop.tactic_clause)
  (grindPremiseNames : Array Name) (includeLCtx : Bool)
  (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit :=
  withMainContext do withOptions (fun o => o.set `aesop.warn.applyIff false) do
    -- Building `autoRuleTacStx`
    let formulas ← withDuperOptions $ collectAssumptions autoPremises false #[]
    let formulas : List (Expr × Expr × Array Name × Bool × String) :=
      -- **TODO** This approach prohibits handling arguments that aren't disambiguated theorem names
      formulas.filterMap (fun (fact, proof, params, isFromGoal, stxOpt) =>
        stxOpt.map (fun stx => (fact, proof, params, isFromGoal, stx.raw.getId.toString)))
    let ruleTacType := mkConst `Aesop.SingleRuleTac
    let autoRuleTacVal ← mkAppM `HammerCore.hammerCoreSingleRuleTac #[q($formulas), q($includeLCtx), q($configOptions)]
    let autoRuleTacDecl :=
      mkDefinitionValEx `instantiatedHammerCoreRuleTac [] ruleTacType autoRuleTacVal
        ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedHammerCoreRuleTac]
    addAndCompile $ Declaration.defnDecl autoRuleTacDecl
    let autoRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedHammerCoreRuleTac)))
    let addAutoUnsafeRule ←
      `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopAutoPriority):num% tactic $autoRuleTacStx))
    -- Building `grindRuleTacStx`
    let grindRuleTacVal ← mkAppM `HammerCore.grindSingleRuleTac #[q($grindPremiseNames)]
    let grindRuleTacDecl :=
      mkDefinitionValEx `instantiatedGrindRuleTac [] ruleTacType grindRuleTacVal
        ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedGrindRuleTac]
    addAndCompile $ Declaration.defnDecl grindRuleTacDecl
    let grindRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedGrindRuleTac)))
    let addGrindUnsafeRule ←
      `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopGrindPriority):num% tactic $grindRuleTacStx))
    -- Calling Aesop with the set of subprocedures determined by `configOptions`
    match configOptions.disableAuto, configOptions.disableGrind with
    | true, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs*))
    | true, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addGrindUnsafeRule))
    | false, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule))
    | false, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule $addGrindUnsafeRule))

/-- Runs `Meta.isProof` on `e` and every subterm of `e`. If `Meta.isProof` ever returns `true`,
    then `autoPremiseTypeEligibleAux` returns `false`.

    `Meta.isProof`, `withLocalDecl`, and `withLetDecl` can throw errors when interacting with expressions
    with unassigned metavariables. In such cases, `autoPremiseTypeEligibleAux` errs on the side of declaring
    premises eligible, only ruling out premises that are conclusively determined to have proofs in them. -/
partial def autoPremiseEligibleAux (e : Expr) : MetaM Bool := do
  try
    if ← Meta.isProof e then return false
    match e with
    | .forallE n t b bi =>
      let tEligible ← autoPremiseEligibleAux t
      if !tEligible then return false
      withLocalDecl n bi t fun x => autoPremiseEligibleAux (b.instantiate1 x)
    | .lam n t b bi =>
      let tEligible ← autoPremiseEligibleAux t
      if !tEligible then return false
      withLocalDecl n bi t fun x => autoPremiseEligibleAux (b.instantiate1 x)
    | .letE n t v b _ =>
      let tEligible ← autoPremiseEligibleAux t
      if !tEligible then return false
      let vEligible ← autoPremiseEligibleAux v
      if !vEligible then return false
      withLetDecl n t v fun x => autoPremiseEligibleAux (b.instantiate1 x)
    | .app e1 e2 =>
      let e1Eligible ← autoPremiseEligibleAux e1
      let e2Eligible ← autoPremiseEligibleAux e2
      return e1Eligible && e2Eligible
    | .mdata _ b => autoPremiseEligibleAux b
    | .proj _ _ b => autoPremiseEligibleAux b
    | _ => return true
  catch _ =>
    return true

/-- Checks whether `autoPremise` contains any proofs within it, and returns `false` if so. Any premise that
    contains a proof within it cannot be soundly translated to higher-order logic by Lean-auto's procedure.
    There are other ways that premises can fail to be soundly translated to higher-order logic, but this
    filter does not yet catch those.

    `autoPremiseEligible` assumes that `autoPremise` is just a constant name.

    **TODO** Test the efficacy of this filter and improve it if it remains common for premises to get through
    which cause Lean-auto's translation to fail. -/
def autoPremiseEligible (autoPremise : Term) : TacticM Bool := do
  let name ← realizeGlobalConstNoOverload autoPremise
  let type ← instantiateMVars (← getConstInfo name).type
  autoPremiseEligibleAux type

/-- Checks whether `premiseName` corresponds to a constant that `grind` can use. The set of `thmKinds` that is tested was determined
    by reading `Lean.Meta.Grind.mkEMatchTheoremAndSuggest`. -/
def grindPremiseEligible (premiseName : Name) : MetaM Bool := do
  let thmKinds : List Grind.EMatchTheoremKind :=
    [.default false, .bwd false, .fwd, .rightLeft, .leftRight, .eqLhs false, .eqRhs false]
  let prios ← Grind.getGlobalSymbolPriorities
  for thmKind in thmKinds do
    try
      let _ ← Grind.mkEMatchTheoremForDecl premiseName thmKind prios (showInfo := false) (minIndexable := false)
      return true -- `premiseName` is eligible because there was some `thmKind` for which `Grind.mkEMatchTheoremForDecl` succeeded
    catch _ =>
      continue
  return false

def runHammer (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (userInputTerms premises : Array Term) (includeLCtx : Bool) (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit :=
  withMainContext do
    let mut autoPremises := userInputTerms ++ premises.take configOptions.autoPremises
    let aesopPremises := userInputTerms ++ premises.take configOptions.aesopPremises
    let grindPremises := userInputTerms ++ premises.take configOptions.grindPremises
    let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
    let mut grindParamStxs : TSyntaxArray `Lean.Parser.Tactic.grindParam := #[]
    let mut grindPremiseNames : Array Name := #[]
    if !configOptions.disableAuto then
      autoPremises ← autoPremises.filterM autoPremiseEligible
    if !configOptions.disableAesop then
      for p in aesopPremises do
        -- **TODO** Add support for terms that aren't just names of premises
        let pFeature ← `(Aesop.feature| $(mkIdent p.raw.getId):ident)
        let tacticClause ← `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopPremisePriority):num % $pFeature:Aesop.feature))
        addIdentStxs := addIdentStxs.push tacticClause
    if !configOptions.disableGrind then
      for p in grindPremises do
        if ← grindPremiseEligible p.raw.getId then
          grindPremiseNames := grindPremiseNames.push p.raw.getId
          let grindParam ← `(Lean.Parser.Tactic.grindParam| $(mkIdent p.raw.getId):ident)
          grindParamStxs := grindParamStxs.push grindParam
    if configOptions.parallelism then
      match configOptions.disableAesop, configOptions.disableAuto, configOptions.disableGrind with
      | true, true, false => evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
      | true, false, true => runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions
      | false, true, true => runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx configOptions
      | false, false, true =>
        tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions [
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx configOptions,
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx {configOptions with disableAuto := true, disableGrind := true},
          runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions
        ]
      | false, true, false =>
        tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions [
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx configOptions,
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx {configOptions with disableAuto := true, disableGrind := true},
          evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
        ]
      | false, false, false =>
        tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions [
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx configOptions,
          runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx {configOptions with disableAuto := true, disableGrind := true},
          runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions,
          evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
        ]
      | true, false, false =>
        tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions [
          runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions,
          evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
        ]
      | true, true, true => throwError "Erroneous invocation of hammer: At least one of Aesop, Auto, and Grind must be enabled."
    else
      match configOptions.disableAesop, configOptions.disableAuto, configOptions.disableGrind with
      | true, true, false => evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
      | true, false, true => runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions
      | false, _, _ => runAesopWithSubprocedures autoPremises addIdentStxs grindPremiseNames includeLCtx configOptions
      | true, false, false => throwError "Erroneous invocation of hammer: Aesop or parallelism is needed to enable both Auto and Grind."
      | true, true, true => throwError "Erroneous invocation of hammer: At least one of Aesop, Auto, and Grind must be enabled."

def evalHammerWithArgs : Tactic
| `(tactic| hammer%$stxRef [$userInputTerms,*] {$configOptions,*}) => withoutModifyingEnv do
  withMainContext do
  withOptions (fun o => o.set `linter.deprecated false) do
  let goal ← getMainGoal
  let userInputTerms : Array Term := userInputTerms
  let configOptions ← parseConfigOptions configOptions
  let autoPremises := if configOptions.disableAuto then 0 else configOptions.autoPremises
  let aesopPremises := if configOptions.disableAesop then 0 else configOptions.aesopPremises
  let grindPremises := if configOptions.disableGrind then 0 else configOptions.grindPremises
  let maxSuggestions := max autoPremises (max aesopPremises grindPremises)
  let librarySuggestionsConfig : LibrarySuggestions.Config := {
    maxSuggestions := maxSuggestions + userInputTerms.size, -- Add `userInputTerms.size` to ensure there are `maxSuggestions` non-duplicate premises
    caller := "hammer"
  }
  /- Get the registered premise selector for premise selection.

     Currently, the registration mechanism for library suggestions is just global state, so the `set_library_suggestions` command
     on line 14 should override the `set_library_suggestions` command in Lean.LibrarySuggestions.Default, but if a user invokes
     `set_library_suggestions` after importing Hammer, then their command will override the command on line 14.

     For now, this is fine because the current solution yields the desired behavior.
     `Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile` is the effective default that users can override with
     `set_library_suggestions`. However, a comment in Lean.LibrarySuggestions.Basic (line 392 of v4.26.0) indicates that the registration
     mechanism is likely to change in the future, and if this occurs, I may need to adjust accordingly to preserve LeanHammer's intended behavior. -/
  let selector ← getSelector
  let defaultSelector := Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile
  let selector := selector.getD defaultSelector
  let premises ←
    if maxSuggestions == 0 then pure #[] -- If `maxSuggestions` is 0, then we don't need to waste time calling the premise selector
    else selector goal librarySuggestionsConfig
  let premises ← premises.mapM (fun p => unresolveNameGlobal p.name)
  let premises ← premises.mapM (fun p => return (← `(term| $(mkIdent p))))
  trace[hammer.premises] "user input terms: {userInputTerms}"
  trace[hammer.premises] "premises from premise selector: {premises}"
  let premises := premises.filter (fun p => !userInputTerms.contains p) -- Remove duplicates between `userInputTerms` and `premises`
  trace[hammer.premises] "premises from premise selector after removing duplicates in user input terms: {premises}"
  runHammer stxRef ∅ userInputTerms premises true configOptions
| _ => throwUnsupportedSyntax

-- Note, we no longer use `macro_rules` to process the cases where `hammer` is not given all of its arguments because `macro_rules` appears to
-- interfere with the tactic suggestions that `hammer` produces.
@[tactic hammer]
def evalHammer : Tactic
| `(tactic| hammer) => do evalHammerWithArgs $ ← `(tactic| hammer [] {})
| `(tactic| hammer [$userInputTerms,*]) => do evalHammerWithArgs $ ← `(tactic| hammer [$userInputTerms,*] {})
| `(tactic| hammer {$configOptions,*}) => do evalHammerWithArgs $ ← `(tactic| hammer [] {$configOptions,*})
| `(tactic| hammer [$userInputTerms,*] {$configOptions,*}) => do evalHammerWithArgs $ ← `(tactic| hammer [$userInputTerms,*] {$configOptions,*})
| _ => throwUnsupportedSyntax

end Hammer
