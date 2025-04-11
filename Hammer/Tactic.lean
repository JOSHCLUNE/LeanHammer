import HammerCore
import PremiseSelection
import Aesop

open Lean Elab Tactic HammerCore Syntax PremiseSelection

namespace Hammer

syntax (name := hammer) "hammer" (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules | `(tactic| hammer) => `(tactic| hammer {})

def runHammer (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (premises : TSepArray `term ",") (includeLCtx : Bool) (configOptions : ConfigurationOptions) : TacticM Unit := withMainContext do
  if configOptions.disableAesop && configOptions.disableAuto then
    throwError "Erroneous invocation of hammer: The aesop and auto options cannot both be disabled"
  else if configOptions.disableAesop then
    runHammerCore stxRef simpLemmas premises includeLCtx configOptions
  else if configOptions.disableAuto then
    -- **TODO** Make this priority configurable
    let aesopPremisePriority := 20
    let premises : Array Term := premises
    let aesopPremises := premises.take configOptions.k2
    let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
    for p in aesopPremises do
      let pFeature ← `(Aesop.feature| $(mkIdent p.raw.getId):ident)
      addIdentStxs := addIdentStxs.push (← `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit aesopPremisePriority):num % $pFeature:Aesop.feature)))
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      evalTactic (← `(tactic| aesop? $addIdentStxs*))
  else
    -- **TODO** Make these priorities configurable
    let aesopAutoPriority := 10
    let aesopPremisePriority := 20
    let premises : Array Term := premises
    let autoPremises := premises.take configOptions.k1
    let aesopPremises := premises.take configOptions.k2
    let mut addIdentStxs : TSyntaxArray `Aesop.tactic_clause := #[]
    for p in aesopPremises do
      let pFeature ← `(Aesop.feature| $(mkIdent p.raw.getId):ident)
      addIdentStxs := addIdentStxs.push (← `(Aesop.tactic_clause| (add unsafe $(Syntax.mkNatLit aesopPremisePriority):num % $pFeature:Aesop.feature)))
    withOptions (fun o => o.set `aesop.warn.applyIff false) do
      evalTactic (← `(tactic| aesop? $addIdentStxs* (add unsafe $(Syntax.mkNatLit aesopAutoPriority):num% (by hammerCore [$simpLemmas,*] [*, $(autoPremises),*]))))

@[tactic hammer]
def evalHammer : Tactic
| `(tactic| hammer%$stxRef {$configOptions,*}) => withMainContext do
  let goal ← getMainGoal
  let configOptions ← parseConfigOptions configOptions
  let premiseSelectionConfig : PremiseSelection.Config := {
    maxSuggestions := max configOptions.k1 configOptions.k2,
    caller := `hammer
  }
  -- Get the registered premise selector for premise selection.
  -- If none registered, then use the cloud premise selector by default.
  let selector := premiseSelectorExt.getState (← getEnv)
  let selector := selector.getD Cloud.premiseSelector
  let premises ← selector goal premiseSelectionConfig
  let premises := premises.map (fun p => p.name)
  let premises ← premises.mapM (fun p => return (← `(term| $(mkIdent p))))
  trace[hammer.debug] "premises: {premises}"
  runHammer stxRef ∅ premises true configOptions
| _ => throwUnsupportedSyntax

end Hammer
