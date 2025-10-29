import HammerCore.Duper
import Aesop

open Lean Meta Parser Elab Tactic Auto Duper Syntax Aesop

namespace HammerCore

/-- Constructs a `SingleRuleTac` that uses Lean-auto/Zipperposition to attempt to solve the input goal with `formulas` (and all facts in the local context
    if `includeLCtx` is enabled), and either throws an error (if Lean-auto/Zipperposition fail) or suggests a Duper invocation using the subset of `formulas`
    that Zipperposition used to find a proof.

    **TODO** Currently, Zipperposition's unsat core is not used to minimize the set of formulas from the local context that are sent to Duper, but in
    the future, this behavior should be added as an option (it should theoretically improve the strength of some suggested Duper invocations at the cost
    of increasing the size of all suggested Duper invocations). -/
def duperSingleRuleTac (formulas : List (Expr × Expr × Array Name × Bool × String))
  (includeLCtx : Bool) (configOptions : ConfigurationOptions) : SingleRuleTac := λ input => do
  let preState ← saveState
  input.goal.withContext do
    Core.checkSystem s!"{decl_name%}"
    let lctxBeforeIntros ← getLCtx
    let originalMainGoal := input.goal
    let goalType ← originalMainGoal.getType
    let goalType ← instantiateMVars goalType
    -- If `goalType` has the form `∀ x1 : t1, … ∀ xn : tn, b`, first apply `intros` to put `x1 … xn` in the local context
    let numBinders := getIntrosSize goalType
    let mut introNCoreNames : Array Name := #[]
    let mut numGoalHyps := 0
    /- Assuming `goal` has the form `∀ x1 : t1, ∀ x2 : t2, … ∀ xn : tn, b`, `goalPropHyps` is
       an array of size `n` where the mth element in `goalPropHyps` indicates whether the mth forall
       binder has a `Prop` type. This is used to help create `introNCoreNames` which should use existing
       binder names for nonProp arguments and newly created names for Prop arguments -/
    let goalPropHyps ← forallTelescope goalType fun xs _ => do xs.mapM (fun x => do pure (← inferType (← inferType x)).isProp)
    for b in goalPropHyps do
      if b then
        introNCoreNames := introNCoreNames.push (.str .anonymous ("h" ++ numGoalHyps.repr))
        numGoalHyps := numGoalHyps + 1
      else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
        introNCoreNames := introNCoreNames.push `_ -- `introNCore` will overwrite this with the existing binder name
    let (_, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
    let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
      | throwError "evalHammer :: Unexpected result after applying Classical.byContradiction"
    let (_, absurd) ← MVarId.intro nngoal (.str .anonymous "negGoal")
    absurd.withContext do
      let lctxAfterIntros ← getLCtx
      let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
      -- **NOTE** We collect `lctxFormulas` using `Duper.collectAssumptions` rather than `Auto.collectAllLemmas` because `Auto.collectAllLemmas`
      -- does not currently support a mode where unusable facts are ignored.
      let lctxFormulas ← withDuperOptions $ collectLCtxAssumptions goalDecls
      let lctxFormulas := lctxFormulas.filterMap
        (fun (fact, proof, params, isFromGoal, stxOpt) =>
          if formulas.any (fun (f, _, _, _, _) => f == fact) then none
          else
            match stxOpt with
            | none => some (fact, proof, params, isFromGoal, none)
            | some stx => some (fact, proof, params, isFromGoal, some s!"{stx}")
        )
      let formulas := (formulas.map (fun (fact, proof, params, isFromGoal, stxOpt) => (fact, proof, params, isFromGoal, some stxOpt))) ++ lctxFormulas
      withSolverOptions configOptions do
        let lemmas ← formulasWithStringsToAutoLemmas formulas (includeInSetOfSupport := true)
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
        | Solver.zipperposition_exe | Solver.zipperposition =>
          let unsatCoreDerivLeafStrings := solverHints.1
          trace[hammer.debug] "unsatCoreDerivLeafStrings: {unsatCoreDerivLeafStrings}"
          -- Collect all formulas that appear in the unsat core and have a `stxOpt`
          -- **TODO** Add a setting that allows Duper to use Zipperposition's unsat core for lctx facts as well (not just user provided facts)
          let coreFormulas := formulas.filterMap
            (fun (_, _, _, _, stxOpt) => stxOpt.filter (fun stx => unsatCoreIncludesFactAsString unsatCoreDerivLeafStrings stx))
          let coreFormulas := coreFormulas.map (fun s => Lean.mkIdent s.toName) -- **TODO** This approach prohibits handling arguments that aren't disambiguated theorem names
          -- Build a Duper call using includeLCtx and each coreUserInputFact
          let stx ←
            if !coreFormulas.isEmpty && includeLCtx then
              `(tactic| duper [*, $(coreFormulas.toArray),*] {preprocessing := full})
            else if !coreFormulas.isEmpty && !includeLCtx then
              `(tactic| duper [$(coreFormulas.toArray),*] {preprocessing := full})
            else if coreFormulas.isEmpty && includeLCtx then
              `(tactic| duper [*] {preprocessing := full})
            else -- coreFormulas.isEmpty && !includeLCtx
              `(tactic| duper {preprocessing := full})
          let tac := withoutRecover $ evalTactic stx
          let postGoals := (← Elab.Tactic.run absurd tac |>.run').toArray
          let postState ← saveState
          let tacticBuilder := pure $ .unstructured ⟨stx⟩
          let step := {
            preGoal := input.goal
            tacticBuilders := #[tacticBuilder]
            preState, postState, postGoals
          }
          let postGoals ← postGoals.mapM (mvarIdToSubgoal input.goal ·)
          return (postGoals, some #[step], some ⟨1.0⟩)

end HammerCore
