import Smt
import HammerCore.Options
import HammerCore.Errors

open Lean Meta Parser Elab Tactic Auto Syntax

namespace HammerCore

def smtPipeline (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (premises : TSepArray `term ",") (includeLCtx : Bool) (configOptions : ConfigurationOptions) : TacticM Unit := do
  let preprocessingSuggestion ←
    tryCatchRuntimeEx (do
      match configOptions.preprocessing with
      | Preprocessing.no_preprocessing => pure #[] -- No preprocessing
      | Preprocessing.aesop => throwError "{decl_name%} :: Aesop preprocessing is not compatible with {decl_name%}"
      | Preprocessing.simp_target =>
        let goalsBeforeSimpCall ← getGoals
        evalTactic (← `(tactic| simp [$simpLemmas,*]))
        let goalsAfterSimpCall ← getGoals
        if goalsBeforeSimpCall != goalsAfterSimpCall then -- Only add `simp` call to suggestion if it affected the goal state
          pure #[(← `(tactic| simp [$simpLemmas,*]))]
        else
          pure #[]
      | Preprocessing.simp_all =>
        let goalsBeforeSimpCall ← getGoals
        evalTactic (← `(tactic| simp_all [$simpLemmas,*]))
        let goalsAfterSimpCall ← getGoals
        if goalsBeforeSimpCall != goalsAfterSimpCall then -- Only add `simp_all` call to suggestion if it affected the goal state
          pure #[(← `(tactic| simp_all [$simpLemmas,*]))]
        else
          pure #[]
      )
      (fun e => do
        let eStr ← e.toMessageData.toString
        if eStr == "simp made no progress" || eStr == "simp_all made no progress" then pure #[]
        else throwSimpPreprocessingError e
      )

  if (← getUnsolvedGoals).isEmpty then
    let tacticSeq ← `(tacticSeq| $preprocessingSuggestion*)
    addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
    return -- The preprocessing call is sufficient to close all goals, so no more work needs to be done

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
