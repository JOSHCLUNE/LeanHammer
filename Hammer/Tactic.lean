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
  let aesopAutoPriority := configOptions.aesopAutoPriority
  let aesopPremisePriority := configOptions.aesopPremisePriority
  let autoPremises := userInputTerms ++ premises.take configOptions.autoPremises
  let aesopPremises := userInputTerms ++ premises.take configOptions.aesopPremises
  let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
  for p in aesopPremises do
    -- **TODO** Add support for terms that aren't just names of premises
    let pFeature ← `(Aesop.feature| $(mkIdent p.raw.getId):ident)
    addIdentStxs := addIdentStxs.push (← `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit aesopPremisePriority):num % $pFeature:Aesop.feature)))
  if configOptions.disableAesop && configOptions.disableAuto then
    throwError "Erroneous invocation of hammer: The aesop and auto options cannot both be disabled"
  else if configOptions.disableAesop then
    runHammerCore stxRef simpLemmas autoPremises includeLCtx configOptions
  else if configOptions.disableAuto then
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs*))
  else
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      let formulas ← withDuperOptions $ collectAssumptions autoPremises false #[]
      let formulas : List (Expr × Expr × Array Name × Bool × String) := -- **TODO** This approach prohibits handling arguments that aren't disambiguated theorem names
        formulas.filterMap (fun (fact, proof, params, isFromGoal, stxOpt) => stxOpt.map (fun stx => (fact, proof, params, isFromGoal, stx.raw.getId.toString)))
      let ruleTacType := mkConst `Aesop.SingleRuleTac
      let ruleTacVal ← mkAppM `HammerCore.hammerCoreSingleRuleTac #[q($formulas), q($includeLCtx), q($configOptions)]
      let ruleTacDecl := mkDefinitionValEx `instantiatedHammerCoreRuleTac [] ruleTacType ruleTacVal ReducibilityHints.opaque DefinitionSafety.safe [`instantiatedHammerCoreRuleTac]
      addAndCompile $ Declaration.defnDecl ruleTacDecl
      let ruleTacStx ← `(Aesop.rule_expr| ($(mkIdent `instantiatedHammerCoreRuleTac)))
      Aesop.evalAesop (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopAutoPriority):num% tactic $ruleTacStx)))

def evalHammerWithArgs : Tactic
| `(tactic| hammer%$stxRef [$userInputTerms,*] {$configOptions,*}) => withoutModifyingEnv do
  withMainContext do
  withOptions (fun o => o.set `linter.deprecated false) do
  let goal ← getMainGoal
  let userInputTerms : Array Term := userInputTerms
  let configOptions ← parseConfigOptions configOptions
  let maxSuggestions :=
    if configOptions.disableAesop then configOptions.autoPremises
    else if configOptions.disableAuto then configOptions.aesopPremises
    else max configOptions.autoPremises configOptions.aesopPremises
  let premiseSelectionConfig : PremiseSelection.Config := {
    maxSuggestions := maxSuggestions + userInputTerms.size, -- Add `userInputTerms.size` to ensure there are `maxSuggestions` non-duplicate premises
    caller := `hammer
  }
  -- Get the registered premise selector for premise selection.
  -- If none registered, then use the cloud premise selector by default.
  let selector := premiseSelectorExt.getState (← getEnv)
  let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
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
