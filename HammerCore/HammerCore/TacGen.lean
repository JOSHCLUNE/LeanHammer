import HammerCore.Tactic
import Aesop

open Lean Meta Parser Elab Tactic Auto Duper Syntax

namespace HammerCore

/-- `hammerCoreTacGen` takes in `formulas` selected by premise selection or directly provided by the user, uses Lean-auto/Zipperposition to attempt to
    solve the input `goalMVarId` with `formulas` (and all facts in the local context if `includeLCtx` is enabled), and either returns an empty array
    (if Lean-auto/Zipperposition fail) or returns a singleton array containing the string of a Duper call including just the terms that appear in the
    subset of `formulas` that appears in Lean-auto/Zipperposition's unsat core.

    **TODO** Currently, Zipperposition's unsat core is not used to minimize the set of formulas from the local context that are sent to Duper, but in
    the future, this behavior should be added as an option (it should theoretically improve the strength of some suggested Duper invocations at the cost
    of increasing the size of all suggested Duper invocations). -/
def hammerCoreTacGen (formulas : List (Expr × Expr × Array Name × Bool × Term))
  (includeLCtx : Bool) (configOptions : ConfigurationOptions) : Aesop.TacGen := fun goalMVarId => do
  goalMVarId.withContext do
    Core.checkSystem s!"{decl_name%}"
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
    let (_, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
    let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
      | throwError "evalHammer :: Unexpected result after applying Classical.byContradiction"
    let (_, absurd) ← MVarId.intro nngoal (.str .anonymous configOptions.negGoalLemmaName)
    absurd.withContext do
      let lctxAfterIntros ← getLCtx
      let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
      -- **NOTE** We collect `lctxFormulas` using `Duper.collectAssumptions` rather than `Auto.collectAllLemmas` because `Auto.collectAllLemmas`
      -- does not currently support a mode where unusable facts are ignored.
      let lctxFormulas ← withDuperOptions $ collectLCtxAssumptions goalDecls
      let lctxFormulas := lctxFormulas.filter (fun (fact, _, _, _, _) => !formulas.any (fun (f, _, _, _, _) => f == fact))
      let formulas := (formulas.map (fun (fact, proof, params, isFromGoal, stxOpt) => (fact, proof, params, isFromGoal, some stxOpt))) ++ lctxFormulas
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
          let unsatCoreDerivLeafStrings := solverHints.1
          trace[hammer.debug] "unsatCoreDerivLeafStrings: {unsatCoreDerivLeafStrings}"
          -- Collect all formulas that appear in the unsat core and have a `stxOpt`
          -- **TODO** Add a setting that allows Duper to use Zipperposition's unsat core for lctx facts as well (not just user provided facts)
          let coreFormulas := formulas.filterMap
            (fun (_, _, _, _, stxOpt) => stxOpt.filter (fun stx => unsatCoreIncludesFact unsatCoreDerivLeafStrings stx))
          -- Build a Duper call using includeLCtx and each coreUserInputFact
          if !coreFormulas.isEmpty && includeLCtx then
            return #[(s!"{← `(tactic| duper [*, $(coreFormulas.toArray),*] {preprocessing := full})}", 1.0)]
          else if !coreFormulas.isEmpty && !includeLCtx then
            return #[(s!"{← `(tactic| duper [$(coreFormulas.toArray),*] {preprocessing := full})}", 1.0)]
          else if coreFormulas.isEmpty && includeLCtx then
            return #[(s!"{← `(tactic| duper [*] {preprocessing := full})}", 1.0)]
          else -- coreFormulas.isEmpty && !includeLCtx
            return #[(s!"{← `(tactic| duper {preprocessing := full})}", 1.0)]
        | Solver.cvc5 => throwError "evalHammer :: cvc5 support not yet implemented"

end HammerCore
