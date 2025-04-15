import HammerCore.Tactic
import Aesop

open Lean Meta Parser Elab Tactic Auto Duper Syntax

namespace HammerCore
/- **TODO** In progress
def hammerCoreTacGen (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (premises : TSepArray `term ",") (includeLCtx : Bool) (configOptions : ConfigurationOptions) : Aesop.TacGen := fun goalMVarId => do
  goalMVarId.withContext do
    Core.checkSystem s!"{decl_name%}"
    let preprocessingSuggestion ←
      match configOptions.preprocessing with
      | Preprocessing.aesop => pure #[] -- Aesop's integration comes prior to calling `hammerCore`, so no preprocessing within `hammerCore` is needed
      | _ => throwError "{decl_name%} :: hammerCoreTacGen should only be called when preprocessing is set to `Preprocessing.aesop`"
    let lctxBeforeIntros ← getLCtx
    let originalMainGoal := goalMVarId
    let goalType ← originalMainGoal.getType
    let goalType ← instantiateMVars goalType
    -- If `goalType` has the form `∀ x1 : t1, … ∀ xn : tn, b`, first apply `intros` to put `x1 … xn` in the local context
    let numBinders := getIntrosSize goalType
    let mut introNCoreNames : Array Name := #[]
    let mut numGoalHyps := 0
    /- Assuming `goal` has the form `∀ x1 : t1, ∀ x2 : t2, … ∀ xn : tn, b`, `goalPropHyps` is
      an array of size `n` where the mth element in `goalPropHyps` indicates whether the mth forall
      binder has a `Prop` type. This is used to help create `introNCoreNames` which should use existing
      binder names for nonProp arguments and newly created names (based on `goalHypPrefix`) for Prop arguments -/
    let goalPropHyps ← forallTelescope goalType fun xs _ => do xs.mapM (fun x => do pure (← inferType (← inferType x)).isProp)
    for b in goalPropHyps do
      if b then
        introNCoreNames := introNCoreNames.push (.str .anonymous (configOptions.goalHypPrefix ++ numGoalHyps.repr))
        numGoalHyps := numGoalHyps + 1
      else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
        introNCoreNames := introNCoreNames.push `_ -- `introNCore` will overwrite this with the existing binder name
    let (goalBinders, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
    let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
      | throwError "evalHammer :: Unexpected result after applying Classical.byContradiction"
    let (_, absurd) ← MVarId.intro nngoal (.str .anonymous configOptions.negGoalLemmaName)
    absurd.withContext do
      let lctxAfterIntros ← getLCtx
      let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
      -- **TODO** Need a version of collectAssumptions that can live in `MetaM`. Note that we can handle the `premises` prior to calling
      -- `hammerCoreTacGen`, so we should be able to avoid elaborating the `premises` in `MetaM`, and only need to handle the local context and goalDecls

      -- **NOTE** We collect `formulas` using `Duper.collectAssumptions` rather than `Auto.collectAllLemmas` because `Auto.collectAllLemmas`
      -- does not currently support a mode where unusable facts are ignored.
      let formulas ← withDuperOptions $ sorry -- collectAssumptions premises includeLCtx goalDecls
      withSolverOptions configOptions do
        let lemmas ← formulasToAutoLemmas formulas (includeInSetOfSupport := true)
        -- Calling `Auto.unfoldConstAndPreprocessLemma` is an essential step for the monomorphization procedure
        let lemmas ←
          tryCatchRuntimeEx
            (lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[]))
            throwTranslationError
        let inhFacts ←
          tryCatchRuntimeEx
            Auto.Inhabitation.getInhFactsFromLCtx
            throwTranslationError
        let solverHints ←
          tryCatchRuntimeEx (do
            trace[hammer.debug] "Lemmas passed to runAutoGetHints {lemmas}"
            trace[hammer.debug] "inhFacts passed to runAutoGetHints {inhFacts}"
            runAutoGetHints lemmas inhFacts
            )
            (fun e => do
              if (← e.toMessageData.toString) ==  "runAutoGetHints :: External TPTP solver unable to solve the goal" then
                throwExternalSolverError e
              else
                throwTranslationError e
            )
        match configOptions.solver with
        | Solver.zipperposition =>
          let mut tacticsArr := preprocessingSuggestion -- The array of tactics that will be suggested to the user
          let unsatCoreDerivLeafStrings := solverHints.1
          trace[hammer.debug] "unsatCoreDerivLeafStrings: {unsatCoreDerivLeafStrings}"
          /- **TODO** Uncomment this once I can uncomment `getDuperCoreLemmas`
          let duperConfigOptions :=
            { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none, includeExpensiveRules := none,
              preprocessing := some PreprocessingOption.FullPreprocessing, selFunction := none }
          -/
          let ((coreLctxLemmas : Array FVarId), (coreUserInputFacts : Array Term), (duperProof : Expr)) ←
            tryCatchRuntimeEx
              sorry -- (getDuperCoreLemmas unsatCoreDerivLeafStrings premises goalDecls includeLCtx duperConfigOptions)
              throwDuperError
          -- **TODO** `intros ...; apply Classical.byContradiction` is unecessary if everything in the goal will be sent to Duper
          -- Build the `intros ...` tactic with appropriate names
          let mut introsNames := #[] -- Can't just use `introNCoreNames` because `introNCoreNames` uses `_ as a placeholder
          let mut numGoalHyps := 0
          for fvarId in goalBinders do
            let some localDecl := lctxAfterIntros.fvarIdToDecl.find? fvarId
              | throwProofFitError $ ← throwError "Unable to find fvarId {Expr.fvar fvarId} in local context (after intros)"
            let ty := localDecl.type
            if (← inferType ty).isProp then
              introsNames := introsNames.push (.str .anonymous (configOptions.goalHypPrefix ++ numGoalHyps.repr))
              numGoalHyps := numGoalHyps + 1
            else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
              introsNames := introsNames.push $ Name.eraseMacroScopes localDecl.userName
          let ids : TSyntaxArray [`ident, `Lean.Parser.Term.hole] := introsNames.map (fun n => mkIdent n)
          if ids.size > 0 then
            tacticsArr := tacticsArr.push $ ← `(tactic| intros $ids*)
          -- Add `apply Classical.byContradiction` so that the unsat core can determine whether the target needs to be included in the call
          let byContradictionConst : TSyntax `term ← PrettyPrinter.delab $ mkConst ``Classical.byContradiction
          tacticsArr := tacticsArr.push $ ← `(tactic| apply $byContradictionConst)
          -- Introduce the negated hypothesis (again, so that the unsat core can determine whether the target needs to be included in the call)
          tacticsArr := tacticsArr.push $ ← `(tactic| intro $(mkIdent (.str .anonymous configOptions.negGoalLemmaName)):term)
          -- Build a Duper call using each coreLctxLemma and each coreUserInputFact
          let coreLctxLemmaIds ← coreLctxLemmas.mapM
            (fun lemFVarId => withOptions ppOptionsSetting $ PrettyPrinter.delab (.fvar lemFVarId))
          let coreUserInputFacts := coreUserInputFacts.filter (fun x => !coreLctxLemmaIds.contains x)
          tacticsArr := tacticsArr.push $ ← `(tactic| duper [$(coreLctxLemmaIds ++ coreUserInputFacts),*] {preprocessing := full})
          -- Add tactic sequence suggestion
          let tacticSeq ← `(tacticSeq| $tacticsArr*)
          -- **TODO** Add a warning if anything gets inadvertently shadowed (e.g. by `negGoal` or an introduced goal hypothesis)
          sorry -- **TODO** Return the TacGen suggestion
        | Solver.cvc5 => throwError "evalHammer :: cvc5 support not yet implemented"
-/
end HammerCore
