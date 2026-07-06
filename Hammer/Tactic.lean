import Hammer.HammerCore
import Hammer.Smt
import Hammer.ParallelismUtil
import PremiseSelection
import Aesop
import Qq

initialize
  Lean.registerTraceClass `hammer.premises
  Lean.registerTraceClass `hammer.profiling

register_option hammer.singleTacticParallel : Bool := {
  defValue := false
  descr := "A temporary option to test the impact of using tryAllTacsOnGoal"
}

namespace Hammer

open Lean Meta Elab Tactic HammerCore Syntax LibrarySuggestions Duper Aesop Qq Util

syntax (name := hammer) "hammer" (ppSpace "[" (term),* "]")? (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

set_library_suggestions open Lean.LibrarySuggestions in Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile

/-- This functions produces one Aesop call where Aesop is given:
    - unsafe rules corresponding to individual premise applications (these are determined by `addIdentStxs`).
    - one unsafe rule to call the Lean-auto/Zipperposition/Duper pipeline (if `configOptions.disableDuper` is
      set to `false`). The premises passed into this pipeline is determined by `duperPremises`.
    - one unsafe rule to call `grind?` (if `configOptions.disableGrind` is set to `false`). The premises passed
      to `grind?` are determined by `grindPremiseNames`.
    - one unsafe rule to call Lean-SMT (if `configOptions.disableSmt` is set to `false`). The premises passed to
      Lean-SMT are determined by `smtPremises`

    This function is entirely sequential. Parallel calls to subcomponents are handled elsewhere. -/
def runAesopWithSubprocedures (duperPremises : Array Term) (addIdentStxs : TSyntaxArray `Aesop.tactic_clause)
  (grindPremiseNames : Array Name) (smtPremises : Array Term) (includeLCtx : Bool)
  (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit :=
  withMainContext do withOptions (fun o => o.set `aesop.warn.applyIff false) do
    -- Building `duperRuleTacStx`
    let formulas ← withDuperOptions $ collectAssumptions duperPremises false #[]
    let formulas : List (Expr × Expr × Array Name × Bool × String) :=
      -- **TODO** This approach prohibits handling arguments that aren't disambiguated theorem names
      formulas.filterMap (fun (fact, proof, params, isFromGoal, stxOpt) =>
        stxOpt.map (fun stx => (fact, proof, params, isFromGoal, stx.raw.getId.toString)))
    let ruleTacType := mkConst `Aesop.SingleRuleTac
    let duperRuleTacVal ← mkAppM `HammerCore.duperSingleRuleTac #[q($formulas), q($includeLCtx), q($configOptions)]
    let duperRuleTacDecl :=
      mkDefinitionValEx `instantiatedDuperRuleTac [] ruleTacType duperRuleTacVal
        ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedDuperRuleTac]
    addAndCompile $ Declaration.defnDecl duperRuleTacDecl
    let duperRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedDuperRuleTac)))
    let addAutoUnsafeRule ←
      `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopDuperPriority):num% tactic $duperRuleTacStx))
    -- Building `grindRuleTacStx`
    let grindRuleTacVal ← mkAppM `HammerCore.grindSingleRuleTac #[q($grindPremiseNames)]
    let grindRuleTacDecl :=
      mkDefinitionValEx `instantiatedGrindRuleTac [] ruleTacType grindRuleTacVal
        ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedGrindRuleTac]
    addAndCompile $ Declaration.defnDecl grindRuleTacDecl
    let grindRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedGrindRuleTac)))
    let addGrindUnsafeRule ←
      `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopGrindPriority):num% tactic $grindRuleTacStx))
    -- Building `smtRuleTacStx`
    let smtHints ← smtPremises.mapM (fun n => `(Smt.Tactic.smtHintElem| $n:term))
    let (_, elabedSmtHints) ←
      try
        -- `Smt.Tactic.elabHints` can yield the error: "failed to elaborate eliminator, expected type is not available". Lean-SMT's internal
        -- filter should handle this, but if it doesn't it is better to silently pass nothing to Lean-SMT than to throw an error.
        Smt.Tactic.elabHints (← `(Smt.Tactic.smtHints| [$(smtHints),*]))
      catch _ =>
        trace[hammer.debug] "{decl_name%} :: Failed to elab smt hints: {smtHints}, passing zero hints to Lean-SMT"
        pure ({}, #[])
    let smtHintTypes ← elabedSmtHints.mapM (fun h => Meta.inferType h)
    let smtHintTypesAndStx : List (Expr × Syntax) := List.zip smtHintTypes.toList $ smtPremises.toList.map (fun t => t.raw)
    let smtRuleTacVal ← mkAppM `HammerCore.Smt.smtSingleRuleTac #[q($smtHintTypesAndStx), q($includeLCtx)]
    let smtRuleTacDecl :=
      mkDefinitionValEx `instantiatedSmtRuleTac [] ruleTacType smtRuleTacVal
        ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedSmtRuleTac]
    addAndCompile $ Declaration.defnDecl smtRuleTacDecl
    let smtRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedSmtRuleTac)))
    let addSmtUnsafeRule ←
      `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit configOptions.aesopSmtPriority):num% tactic $smtRuleTacStx))
    -- Calling Aesop with the set of subprocedures determined by `configOptions`
    match configOptions.disableDuper, configOptions.disableGrind, configOptions.disableSmt with
    | true, true, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs*))
    | true, true, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addSmtUnsafeRule))
    | true, false, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addGrindUnsafeRule))
    | true, false, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addGrindUnsafeRule $addSmtUnsafeRule))
    | false, true, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule))
    | false, true, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule $addSmtUnsafeRule))
    | false, false, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule $addGrindUnsafeRule))
    | false, false, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* $addAutoUnsafeRule $addGrindUnsafeRule $addSmtUnsafeRule))

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
  -- If `premiseName` comes from a module that has been marked as "grind-annotated", then it shouldn't be recommended
  -- to `grind`, because it either has already been given a grind annotation or someone decided that it shouldn't get one.
  let env ← getEnv
  match env.getModuleIdxFor? premiseName with
  | none => pure ()
  | some modIdx => if Lean.Elab.Tactic.Grind.isGrindAnnotatedModule env modIdx then return false
  -- If `premiseName` doesn't come from a grind-annotated module, then check whether there is some theorem kind for which
  -- `Grind.mkEMatchTheoremForDecl` succeeds (meaning `grind` can actually process and use the premise).
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

/-- Wraps a single-tactic dispatch with `hammer.profiling` timing. Used when `tryAllTacsOnGoal`
    is not invoked (parallelism disabled, or only one of Aesop/Auto/Grind is enabled), so the
    `Running parallel tactics took ...` trace is inapplicable. -/
def runSingularTactic (tac : TacticM Unit) : TacticM Unit := do
  let singularTacticStart ← IO.monoMsNow
  tac
  trace[hammer.profiling] "Running singular tactic took {(← IO.monoMsNow) - singularTacticStart}ms"

def runHammer (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (userInputTerms premises : Array Term) (includeLCtx : Bool) (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit :=
  withMainContext do
    let premiseFilteringStart ← IO.monoMsNow
    let mut duperPremises := userInputTerms ++ premises.take configOptions.duperPremises
    let aesopPremises := userInputTerms ++ premises.take configOptions.aesopPremises
    let grindPremises := userInputTerms ++ premises.take configOptions.grindPremises
    let mut smtPremises := userInputTerms ++ premises.take configOptions.smtPremises
    let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
    let mut grindParamStxs : TSyntaxArray `Lean.Parser.Tactic.grindParam := #[]
    let mut grindPremiseNames : Array Name := #[]
    if !configOptions.disableDuper then
      duperPremises ← duperPremises.filterM autoPremiseEligible -- Duper uses Lean-auto for preprocessing
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
    if !configOptions.disableSmt then
      smtPremises ← smtPremises.filterM autoPremiseEligible -- Lean-SMT uses Lean-auto for preprocessing
    trace[hammer.profiling] "Premise filtering took {(← IO.monoMsNow) - premiseFilteringStart}ms"
    if configOptions.parallelism then
      -- Gather the tactics corresponding to the subprocedures enabled by `configOptions`. When Aesop is enabled
      -- alongside at least one other subprocedure, an additional pure Aesop call (with all other subprocedures
      -- disabled) is included.
      let mut parallelTacs : List (TacticM Unit) := []
      if !configOptions.disableAesop then
        parallelTacs := parallelTacs ++ [runAesopWithSubprocedures duperPremises addIdentStxs grindPremiseNames smtPremises includeLCtx configOptions]
        if !configOptions.disableDuper || !configOptions.disableGrind || !configOptions.disableSmt then
          parallelTacs := parallelTacs ++
            [runAesopWithSubprocedures duperPremises addIdentStxs grindPremiseNames smtPremises includeLCtx
              {configOptions with disableDuper := true, disableGrind := true, disableSmt := true}]
      if !configOptions.disableDuper then
        parallelTacs := parallelTacs ++ [runDuper stxRef simpLemmas duperPremises includeLCtx configOptions]
      if !configOptions.disableGrind then
        parallelTacs := parallelTacs ++ [evalTactic (← `(tactic| grind? [$grindParamStxs,*]))]
      if !configOptions.disableSmt then
        parallelTacs := parallelTacs ++ [smtPipeline stxRef simpLemmas smtPremises includeLCtx configOptions]
      match parallelTacs with
      | [] => throwError "Erroneous invocation of hammer: At least one of Aesop, Duper, Grind, and Lean-SMT must be enabled."
      | [singleTac] =>
        if hammer.singleTacticParallel.get (← getOptions) then
          tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout [singleTac]
        else
          runSingularTactic singleTac
      | multipleTacs => tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout multipleTacs
    else
      match configOptions.disableAesop, configOptions.disableDuper, configOptions.disableGrind, configOptions.disableSmt with
      | true, true, false, true =>
        if hammer.singleTacticParallel.get (← getOptions) then
          tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout [
            evalTactic (← `(tactic| grind? [$grindParamStxs,*]))
          ]
        else
          runSingularTactic (evalTactic (← `(tactic| grind? [$grindParamStxs,*])))
      | true, false, true, true =>
        if hammer.singleTacticParallel.get (← getOptions) then
          tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout [
            runDuper stxRef simpLemmas duperPremises includeLCtx configOptions
          ]
        else
          runSingularTactic (runDuper stxRef simpLemmas duperPremises includeLCtx configOptions)
      | true, true, true, false =>
        if hammer.singleTacticParallel.get (← getOptions) then
          tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout [
            smtPipeline stxRef simpLemmas smtPremises includeLCtx configOptions
          ]
        else
          runSingularTactic (smtPipeline stxRef simpLemmas smtPremises includeLCtx configOptions)
      | false, _, _, _ =>
        if hammer.singleTacticParallel.get (← getOptions) then
          tryAllTacsOnGoal stxRef configOptions.outputAllSuggestions configOptions.wallclockTimeout [
            runAesopWithSubprocedures duperPremises addIdentStxs grindPremiseNames smtPremises includeLCtx configOptions
          ]
        else
          runSingularTactic (runAesopWithSubprocedures duperPremises addIdentStxs grindPremiseNames smtPremises includeLCtx configOptions)
      | true, true, true, true => throwError "Erroneous invocation of hammer: At least one of Aesop, Duper, Grind, and Lean-SMT must be enabled."
      | _, _, _, _ => throwError "Erroneous invocation of hammer: Aesop or parallelism is needed to enable more than one of Duper, Grind, and SMT."

def evalHammerWithArgs : Tactic
| `(tactic| hammer%$stxRef [$userInputTerms,*] {$configOptions,*}) => withoutModifyingEnv do
  withMainContext do
  withOptions (fun o => o.set `linter.deprecated false) do
  let hammerStart ← IO.monoMsNow
  let goal ← getMainGoal
  let userInputTerms : Array Term := userInputTerms
  let configOptions ← parseConfigOptions configOptions
  let autoPremises := if configOptions.disableDuper then 0 else configOptions.duperPremises
  let aesopPremises := if configOptions.disableAesop then 0 else configOptions.aesopPremises
  let grindPremises := if configOptions.disableGrind then 0 else configOptions.grindPremises
  let smtPremises := if configOptions.disableSmt then 0 else configOptions.smtPremises
  let maxSuggestions := max autoPremises $ max aesopPremises $ max grindPremises smtPremises
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
  let premiseSelectionStart ← IO.monoMsNow
  let premises ←
    if maxSuggestions == 0 then pure #[] -- If `maxSuggestions` is 0, then we don't need to waste time calling the premise selector
    else selector goal librarySuggestionsConfig
  let premises ← premises.mapM (fun p => unresolveNameGlobal p.name)
  let premises ← premises.mapM (fun p => return (← `(term| $(mkIdent p))))
  trace[hammer.profiling] "Premise selection took {(← IO.monoMsNow) - premiseSelectionStart}ms"
  trace[hammer.premises] "user input terms: {userInputTerms}"
  trace[hammer.premises] "premises from premise selector: {premises}"
  let premises := premises.filter (fun p => !userInputTerms.contains p) -- Remove duplicates between `userInputTerms` and `premises`
  trace[hammer.premises] "premises from premise selector after removing duplicates in user input terms: {premises}"
  runHammer stxRef ∅ userInputTerms premises true configOptions
  trace[hammer.profiling] "Total hammer runtime: {(← IO.monoMsNow) - hammerStart}ms"
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
