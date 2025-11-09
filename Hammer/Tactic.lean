import HammerCore
import PremiseSelection
import Aesop
import Qq

open Lean Meta Elab Tactic HammerCore Syntax PremiseSelection Duper Aesop Qq

initialize Lean.registerTraceClass `hammer.premises

namespace Hammer

syntax (name := hammer) "hammer" (ppSpace "[" (term),* "]")? (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

def runHammer (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (userInputTerms premises : Array Term) (includeLCtx : Bool) (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit := withMainContext do
  let aesopDuperPriority := configOptions.aesopDuperPriority
  let aesopSmtPriority := configOptions.aesopSmtPriority
  let aesopPremisePriority := configOptions.aesopPremisePriority
  let duperPremises := userInputTerms ++ premises.take configOptions.duperPremises
  let smtPremises := userInputTerms ++ premises.take configOptions.smtPremises
  let aesopPremises := userInputTerms ++ premises.take configOptions.aesopPremises
  match configOptions.disableAesop, configOptions.disableDuper, configOptions.disableSmt with
  | true, true, true =>
    throwError "Erroneous invocation of hammer: At least one of the aesop, duper, and smt options must be enabled"
  | true, true, false =>
    HammerCore.smtPipeline stxRef simpLemmas smtPremises includeLCtx configOptions
  | true, false, true =>
    HammerCore.runDuper stxRef simpLemmas duperPremises includeLCtx configOptions
  | true, false, false =>
    throwError "Parallel execution of duper and smt is not yet implemented"
  | false, _, _ =>
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      -- Build `addIdentStxs`
      let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
      for p in aesopPremises do -- **TODO** Add support for terms that aren't just names of premises
        let pFeature ← `(Aesop.feature| $(mkIdent p.raw.getId):ident)
        addIdentStxs := addIdentStxs.push (← `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit aesopPremisePriority):num % $pFeature:Aesop.feature)))

      -- Build `smtRuleTacStx`
      let smtHints ← smtPremises.mapM (fun n => `(Smt.Tactic.smtHintElem| $n:term))
      -- **TODO** `Smt.Tactic.elabHints` can yield the error: "failed to elaborate eliminator, expected type is not available". Lean-smt's internal
      -- filter does not resolve this issue, then I should wrap the next line in a try-catch statement
      let (_, elabedSmtHints) ← Smt.Tactic.elabHints (← `(Smt.Tactic.smtHints| [$(smtHints),*]))
      let smtHintTypes ← elabedSmtHints.mapM (fun h => Meta.inferType h)
      let smtHintTypesAndStx : List (Expr × Syntax) := List.zip smtHintTypes.toList $ smtPremises.toList.map (fun t => t.raw)
      let smtRuleTacVal ← mkAppM ``HammerCore.Smt.smtSingleRuleTac #[q($smtHintTypesAndStx), q(false)]
      let smtRuleTacType := mkConst `Aesop.SingleRuleTac
      let smtRuleTacDecl := mkDefinitionValEx `instantiatedSmtCoreRuleTac [] smtRuleTacType smtRuleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedSmtCoreRuleTac]
      addAndCompile $ Declaration.defnDecl smtRuleTacDecl
      let smtRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedSmtCoreRuleTac)))

      -- Build `duperRuleTacStx`
      let duperFormulas ← withDuperOptions $ collectAssumptions duperPremises false #[]
      let duperFormulas : List (Expr × Expr × Array Name × Bool × String) := -- **TODO** This approach prohibits handling arguments that aren't disambiguated theorem names
        duperFormulas.filterMap (fun (fact, proof, params, isFromGoal, stxOpt) => stxOpt.map (fun stx => (fact, proof, params, isFromGoal, stx.raw.getId.toString)))
      let duperRuleTacType := mkConst ``Aesop.SingleRuleTac
      let duperRuleTacVal ← mkAppM ``HammerCore.duperSingleRuleTac #[q($duperFormulas), q($includeLCtx), q($configOptions)]
      let duperRuleTacDecl := mkDefinitionValEx `instantiatedDuperCoreRuleTac [] duperRuleTacType duperRuleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedDuperCoreRuleTac]
      addAndCompile $ Declaration.defnDecl duperRuleTacDecl
      let duperRuleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedDuperCoreRuleTac)))

      -- Build `aesop?` call depending on `configOptions.disableDuper` and `configOptions.disableSmt`
      match configOptions.disableDuper, configOptions.disableSmt with
      | true, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs*))
      | true, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopSmtPriority):num% tactic $smtRuleTacStx)))
      | false, true => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopDuperPriority):num% tactic $duperRuleTacStx)))
      | false, false => Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopSmtPriority):num% tactic $smtRuleTacStx)
                                                                           (add unsafe $(Syntax.mkNatLit aesopDuperPriority):num% tactic $duperRuleTacStx)))

def evalHammerWithArgs : Tactic
| `(tactic| hammer%$stxRef [$userInputTerms,*] {$configOptions,*}) => withoutModifyingEnv do
  withMainContext do
  withOptions (fun o => o.set `linter.deprecated false) do
  let goal ← getMainGoal
  let userInputTerms : Array Term := userInputTerms
  let configOptions ← parseConfigOptions configOptions
  let aesopPremises :=
    if configOptions.disableAesop then 0
    else configOptions.aesopPremises
  let smtPremises :=
    if configOptions.disableSmt then 0
    else configOptions.smtPremises
  let duperPremises :=
    if configOptions.disableDuper then 0
    else configOptions.duperPremises
  let maxSuggestions := max aesopPremises (max smtPremises duperPremises)
  let premiseSelectionConfig : PremiseSelection.Config := {
    maxSuggestions := maxSuggestions + userInputTerms.size, -- Add `userInputTerms.size` to ensure there are `maxSuggestions` non-duplicate premises
    caller := `hammer
  }
  -- Extend moduleDenyList to include modules from LeanHammer or its dependencies
  let moduleDenyList := moduleDenyListExt.getState (← getEnv)
  setEnv $ moduleDenyListExt.setState (← getEnv) (["Auto", "Duper", "PremiseSelection", "Smt", "cvc5", "Aesop", "HammerCore", "Hammer"] ++ moduleDenyList)
  let unindexedPremises ← PremiseSelection.Cloud.getUnindexedPremises
  trace[hammer.premises] "unindexedPremises: {unindexedPremises.map Premise.name}"
  -- Get the registered premise selector for premise selection.
  -- If none registered, then use the cloud premise selector by default.
  let selector := premiseSelectorExt.getState (← getEnv)
  let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := false) (p := 0.6) (c := 0.9)
  let selector := selector.getD defaultSelector
  let premises ←
    if maxSuggestions == 0 then pure #[] -- If `maxSuggestions` is 0, then we don't need to waste time calling the premise selector
    else selector goal premiseSelectionConfig
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
