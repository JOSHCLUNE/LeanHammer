import HammerCore
import PremiseSelection
import Aesop

open Lean Elab Tactic HammerCore Syntax PremiseSelection Duper Aesop

namespace Hammer

syntax (name := hammer) "hammer" (ppSpace "[" (term),* "]")? (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| hammer) => `(tactic| hammer [] {}) -- Neither lemmas nor config options
| `(tactic| hammer [$lemmas,*]) => `(tactic| hammer [$lemmas,*] {}) -- Lemmas only
| `(tactic| hammer {$configOptions,*}) => `(tactic| hammer [] {$configOptions,*}) -- Config options only

def runHammer (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (userInputTerms premises : Array Term) (includeLCtx : Bool) (configOptions : HammerCore.ConfigurationOptions) : TacticM Unit := withMainContext do
  let aesopAutoPriority := configOptions.aesopAutoPriority
  let aesopPremisePriority := configOptions.aesopPremisePriority
  let autoPremises := userInputTerms ++ premises.take configOptions.k1
  let aesopPremises := userInputTerms ++ premises.take configOptions.k2
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
      evalTactic (← `(tactic| aesop? $addIdentStxs*))
  else
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      if autoPremises.isEmpty then
        evalTactic (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopAutoPriority):num% (by hammerCore [$simpLemmas,*] [*]))))
      else
        evalTactic (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopAutoPriority):num% (by hammerCore [$simpLemmas,*] [*, $(autoPremises),*]))))
      -- **TODO** Trying to find a way to integrate `hammerCoreTacGen`

@[tactic hammer]
def evalHammer : Tactic
| `(tactic| hammer%$stxRef [$userInputTerms,*] {$configOptions,*}) => withMainContext do
  let goal ← getMainGoal
  let userInputTerms : Array Term := userInputTerms
  let configOptions ← parseConfigOptions configOptions
  let maxSuggestions := max configOptions.k1 configOptions.k2
  let premiseSelectionConfig : PremiseSelection.Config := {
    maxSuggestions := maxSuggestions,
    caller := `hammer
  }
  -- Get the registered premise selector for premise selection.
  -- If none registered, then use the cloud premise selector by default.
  let selector := premiseSelectorExt.getState (← getEnv)
  let selector := selector.getD Cloud.premiseSelector
  let premises ←
    if maxSuggestions == 0 then pure #[] -- If `maxSuggestions` is 0, then we don't need to waste time calling the premise selector
    else selector goal premiseSelectionConfig
  let premises := premises.map (fun p => p.name)
  let premises ← premises.mapM (fun p => return (← `(term| $(mkIdent p))))
  trace[hammer.debug] "premises from premise selector: {premises}"
  trace[hammer.debug] "user input terms: {userInputTerms}"
  runHammer stxRef ∅ userInputTerms premises true configOptions
| _ => throwUnsupportedSyntax

end Hammer
