import Smt
import HammerCore.Options

open Lean Meta Parser Elab Tactic Auto Syntax

initialize Lean.registerTraceClass `hammer.debug

namespace HammerCore

def smtPipeline (preprocessingSuggestion : Array (TSyntax `tactic)) (stxRef : Syntax)
  (premises : TSepArray `term ",") (includeLCtx : Bool) : TacticM Unit := do
  let premises : Array (TSyntax `Smt.Tactic.smtHintElem) ← premises.getElems.mapM fun (p : TSyntax `term) => do
    let x ← `(Smt.Tactic.smtHintElem| $p:term)
    return x
  let cfg ← `(optConfig| +$(mkIdent `mono))
  let hints ← `(Smt.Tactic.smtHints| [$premises,*])
  trace[hammer.debug] "smt {cfg} {hints}"
  let coreUserInputFacts ← Smt.Tactic.evalSmtCore cfg hints
  let mut tacticsArr := preprocessingSuggestion -- The array of tactics that will be suggested to the user
  if coreUserInputFacts.size > 0 && includeLCtx then
    tacticsArr := tacticsArr.push $ ← `(tactic| smt $cfg [*, $(coreUserInputFacts),*])
  else if coreUserInputFacts.size > 0 && !includeLCtx then
    tacticsArr := tacticsArr.push $ ← `(tactic| smt $cfg [$(coreUserInputFacts),*])
  else if coreUserInputFacts.size == 0 && includeLCtx then
    tacticsArr := tacticsArr.push $ ← `(tactic| smt $cfg [*])
  else -- coreUserInputFacts.size == 0 && !includeLCtx
    tacticsArr := tacticsArr.push $ ← `(tactic| smt $cfg)
  -- Add tactic sequence suggestion
  let tacticSeq ← `(tacticSeq| $tacticsArr*)
  addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)

end HammerCore
