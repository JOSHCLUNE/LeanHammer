import Aesop
import Auto

/- **TODO** This file is currently a mishmash of code that was adapted from functions that appear in Lean-auto.
   This code should be rearranged into a more coherent structure. -/

open Lean Meta Auto Elab Tactic Parser Tactic

register_option auto.getHints.failOnParseError : Bool := {
  defValue := false
  descr := "Whether to throw an error or ignore smt lemmas that can not be parsed"
}

def auto.getHints.getFailOnParseError (opts : Options) : Bool :=
  auto.getHints.failOnParseError.get opts

def auto.getHints.getFailOnParseErrorM : CoreM Bool := do
  let opts ← getOptions
  return getHints.getFailOnParseError opts

namespace Auto

namespace Solver.SMT

/-- `solverHints` includes:
    - `preprocessFacts` : List (Parser.SMTTerm.Term)
    - `theoryLemmas` : List (Parser.SMTTerm.Term)
    - `instantiations` : List (Parser.SMTTerm.Term)
    - `computationLemmas` : List (Parser.SMTTerm.Term)
    - `polynomialLemmas` : List (Parser.SMTTerm.Term)
    - `rewriteFacts` : List (List (Parser.SMTTerm.Term)) -/
abbrev solverHints :=
  List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) ×
  List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) × List (List (Parser.SMTTerm.Term))

/-- Behaves like `Auto.Solver.SMT.querySolver` but assumes that the output came from `cvc5` with `--dump-hints` enabled. The
    additional output is used to return not just the unsatCore and proof, but also a list of theory lemmas. -/
def querySolverWithHints (query : Array IR.SMT.Command)
  : MetaM (Option (Parser.SMTTerm.Term × solverHints × String)) := do
  if !(auto.smt.get (← getOptions)) then
    throwError "querySolver :: Unexpected error"
  if (auto.smt.solver.name.get (← getOptions) == .none) then
    logInfo "querySolver :: Skipped"
    return .none
  let name := auto.smt.solver.name.get (← getOptions)
  let solver ← Auto.Solver.SMT.createSolver name
  Auto.Solver.SMT.emitCommand solver (.setOption (.produceProofs true))
  Auto.Solver.SMT.emitCommand solver (.setOption (.produceUnsatCores true))
  Auto.Solver.SMT.emitCommands solver query
  Auto.Solver.SMT.emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  trace[auto.smt.result] "checkSatResponse: {stdout}"
  -- **NOTE** When checkSatResponse is sat, the below getTerm call can throw an error
  let (checkSatResponse, _) ← Auto.Solver.SMT.getTerm stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    Auto.Solver.SMT.emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    solver.kill
    try
      let (model, _) ← Auto.Solver.SMT.getTerm stdout
      trace[auto.smt.result] "{name} says Sat"
      trace[auto.smt.model] "Model:\n{model}"
      trace[auto.smt.stderr] "stderr:\n{stderr}"
      return .none
    catch _ => -- Don't let a failure to parse the model prevent `querySolverWithHints` from returning `none`
      return .none
  | .atom (.symb "unsat") =>
    Auto.Solver.SMT.emitCommand solver (.echo "Unsat core:")
    Auto.Solver.SMT.emitCommand solver .getUnsatCore
    Auto.Solver.SMT.emitCommand solver .getProof
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[auto.smt.result] "Original unfiltered {name} output: {stdout}"
    let [_, stdout] := stdout.splitOn "Preprocess:"
      | throwError "Error finding preprocess facts in output"
    let [preprocessFacts, stdout] := stdout.splitOn "Theory lemmas:"
      | throwError "Error finding theory lemmas in output"
    let [theoryLemmas, stdout] := stdout.splitOn "Instantiations:"
      | throwError "Error finding instantiations in output"
    let [instantiations, stdout] := stdout.splitOn "Evaluation/computation:"
      | throwError "Error finding evaluation/computation section in output"
    let [computationLemmas, stdout] := stdout.splitOn "Polynomial normalization:"
      | throwError "Error finding polymolial normalization section in output"
    let firstRewritesLabel :=
      "Rewrites (rule defs (if any) and their usages in quantifier-free terms):"
    let (polynomialLemmas, stdout) :=
      match stdout.splitOn firstRewritesLabel with
      | [polynomialLemmas, stdout] => (polynomialLemmas, stdout)
      | _ => ("", stdout)
    let rewriteFacts := stdout.splitOn "Rewrites:"
    let some stdout := rewriteFacts.getLast?
      | throwError "Error finding rewrites"
    let rewriteFacts := rewriteFacts.take (rewriteFacts.length - 1)
    let [lastRewriteFact, stdout] := stdout.splitOn "\"Unsat core:\""
      | throwError "Error finding unsat core in output"
    let rewriteFacts := rewriteFacts.append [lastRewriteFact]
    let (unsatCore, stdout) ← Auto.Solver.SMT.getTerm stdout
    let preprocessFacts ← Auto.Parser.SMTTerm.lexAllTerms preprocessFacts 0 []
    let theoryLemmas ← Auto.Parser.SMTTerm.lexAllTerms theoryLemmas 0 []
    let instantiations ← Auto.Parser.SMTTerm.lexAllTerms instantiations 0 []
    let computationLemmas ← Auto.Parser.SMTTerm.lexAllTerms computationLemmas 0 []
    let polynomialLemmas ← Auto.Parser.SMTTerm.lexAllTerms polynomialLemmas 0 []
    let rewriteFacts ← rewriteFacts.mapM (fun rwFact => Auto.Parser.SMTTerm.lexAllTerms rwFact 0 [])
    trace[auto.smt.result] "{name} says Unsat, unsat core:\n{unsatCore}"
    trace[auto.smt.result] "{name} preprocess facts:\n{preprocessFacts}"
    trace[auto.smt.result] "{name} theory lemmas:\n{theoryLemmas}"
    trace[auto.smt.result] "{name} computation/evaluation lemmas:\n{computationLemmas}"
    trace[auto.smt.result] "{name} polynomial normalization lemmas:\n{polynomialLemmas}"
    trace[auto.smt.result] "{name} instantiations:\n{instantiations}"
    trace[auto.smt.result] "{name} rewriteFacts:\n{rewriteFacts}"
    trace[auto.smt.stderr] "stderr:\n{stderr}"
    solver.kill
    let solverHints := (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)
    return .some (unsatCore, solverHints, stdout)
  | _ =>
    trace[auto.smt.result] "{name} produces unexpected check-sat response\n {checkSatResponse}"
    return .none

end Solver.SMT

/-- `solverHints` includes:
    - `unsatCoreDerivLeafStrings` an array of Strings that appear as leaves in any derivation for any fact in the unsat core
    - `selectorInfos` which is an array of
      - The SMT selector name (String)
      - The constructor that the selector is for (Expr)
      - The index of the argument it is a selector for (Nat)
      - The type of the selector function (Expr)
    - `preprocessFacts` : List Expr
    - `theoryLemmas` : List Expr
    - `instantiations` : List Expr
    - `computationLemmas` : List Expr
    - `polynomialLemmas` : List Expr
    - `rewriteFacts` : List (List Expr)

    Note 1: In all fields except `selectorInfos`, there may be loose bound variables. The loose bound variable `#i` corresponds to
    the selector indicated by `selectorInfos[i]`

    Note 2: When the external solver is cvc5, all fields can be populated, but when the external solver is Zipperposition, only the
    first field (`unsatCoreDerivLeafStrings`) will be populated -/
abbrev solverHints := Array String × Array (String × Expr × Nat × Expr) × List Expr × List Expr × List Expr × List Expr × List Expr × List (List Expr)

open Embedding.Lam in
def querySMTForHints (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option solverHints) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => pure t
    | _ => throwError "runAuto :: Unexpected error")
  let sni : SMT.SMTNamingInfo :=
    {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
  let ((commands, validFacts, l2hMap, wfPredicatesInvMap, selInfos), state) ←
    (lamFOL2SMTWithExtraInfo sni lamVarTy lamEVarTy exportLamTerms exportInds).run
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let some (unsatCore, solverHints, _proof) ← Solver.SMT.querySolverWithHints commands
    | return none
  let unsatCoreIds ← Solver.SMT.validFactOfUnsatCore unsatCore
  -- **Print valuation of SMT atoms**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for (atomic, name) in state.h2lMap.toArray do
      let e ← SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap atomic
      trace[auto.smt.printValuation] "|{name}| : {e}"
    )
  -- **Print STerms corresponding to `validFacts` in unsatCore**
  for id in unsatCoreIds do
    let some sterm := validFacts[id]?
      | throwError "runAuto :: Index {id} of `validFacts` out of range"
    trace[auto.smt.unsatCore.smtTerms] "|valid_fact_{id}| : {sterm}"
  -- **Print Lean expressions correesponding to `validFacts` in unsatCore**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for id in unsatCoreIds do
      let some t := exportLamTerms[id]?
        | throwError "runAuto :: Index {id} of `exportLamTerms` out of range"
      let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
      trace[auto.smt.unsatCore.leanExprs] "|valid_fact_{id}| : {← Core.betaReduce e}"
    )
  -- **Print derivation of unsatCore and collect unsatCore derivation leaves**
  -- `unsatCoreDerivLeafStrings` contains all of the strings that appear as leaves in any derivation for any fact in the unsat core
  let mut unsatCoreDerivLeafStrings := #[]
  for id in unsatCoreIds do
    let some t := exportLamTerms[id]?
      | throwError "runAuto :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    unsatCoreDerivLeafStrings := unsatCoreDerivLeafStrings ++ vderiv.collectLeafStrings
    trace[auto.smt.unsatCore.deriv] "|valid_fact_{id}| : {vderiv}"
  -- **Build symbolPrecMap using l2hMap, wfPredicatesInvMap, and selInfos**
  let (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts) := solverHints
  let mut symbolMap : Std.HashMap String Expr := Std.HashMap.emptyWithCapacity
  for (varName, varAtom) in l2hMap.toArray do
    let varLeanExp ←
      SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
        SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap varAtom)
    symbolMap := symbolMap.insert varName varLeanExp
  for (wfPredicateName, wfPredicateSort) in wfPredicatesInvMap.toArray do
    let ty ← SMT.withExprValuation sni state.h2lMap (fun tyValMap _ _ => Lam2D.interpLamSortAsUnlifted tyValMap wfPredicateSort)
    let tyPred := .lam .anonymous ty (mkConst ``True) .default -- Interpret `_wf_α` as `fun _ : α => True`
    symbolMap := symbolMap.insert wfPredicateName tyPred
  /- `selectorArr` has entries containing:
     - The name of an SMT selector function
     - The constructor it is a selector for
     - The index of the argument it is a selector for
     - The mvar used to represent the selector function -/
  let mut selectorArr : Array (String × Expr × Nat × Expr) := #[]
  for (selName, selIsProjection, selCtor, argIdx, datatypeName, _selInputType, selOutputType) in selInfos do
    if !selIsProjection then -- Projections already have corresponding values in Lean and therefore don't need to be added to `selectorArr`
      let selCtor ←
        SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
          SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap selCtor)
      let selOutputType ←
        SMT.withExprValuation sni state.h2lMap (fun tyValMap _ _ => Lam2D.interpLamSortAsUnlifted tyValMap selOutputType)
      let selDatatype ←
        match symbolMap.get? datatypeName with
        | some selDatatype => pure selDatatype
        | none => throwError "querySMTForHints :: Could not find the datatype {datatypeName} corresponding to selector {selName}"
      let selType := Expr.forallE `x selDatatype selOutputType .default
      let selMVar ← Meta.mkFreshExprMVar selType
      selectorArr := selectorArr.push (selName, selCtor, argIdx, selMVar)
      symbolMap := symbolMap.insert selName selMVar
  let selectorMVars := selectorArr.map (fun (_, _, _, selMVar) => selMVar)
  -- Change the last argument of selectorArr from the mvar used to represent the selector function to its type
  selectorArr ← selectorArr.mapM
    (fun (selName, selCtor, argIdx, selMVar) => return (selName, selCtor, argIdx, ← Meta.inferType selMVar))
  -- **Extract solverLemmas from solverHints**
  if ← auto.getHints.getFailOnParseErrorM then
    try
      let preprocessFacts ← preprocessFacts.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let theoryLemmas ← theoryLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let instantiations ← instantiations.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let computationLemmas ← computationLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let polynomialLemmas ← polynomialLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let rewriteFacts ← rewriteFacts.mapM
        (fun rwFacts => do
          match rwFacts with
          | [] => return []
          | rwRule :: ruleInstances =>
            /- Try to parse `rwRule`. If succesful, just return that. If unsuccessful (e.g. because the rule contains approximate types),
              then parse each quantifier-free instance of `rwRule` in `ruleInstances` and return all of those. -/
            match ← Parser.SMTTerm.tryParseTermAndAbstractSelectors rwRule symbolMap selectorMVars with
            | some parsedRule => return [parsedRule]
            | none => ruleInstances.mapM (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
        )
      return some (unsatCoreDerivLeafStrings, selectorArr, preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)
    catch e =>
      throwError "querySMTForHints :: Encountered error trying to parse SMT solver's hints. Error: {e.toMessageData}"
  else
    let preprocessFacts ← preprocessFacts.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let theoryLemmas ← theoryLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let instantiations ← instantiations.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let computationLemmas ← computationLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let polynomialLemmas ← polynomialLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let rewriteFacts ← rewriteFacts.mapM
      (fun rwFacts => do
        match rwFacts with
        | [] => return []
        | rwRule :: ruleInstances =>
          /- Try to parse `rwRule`. If succesful, just return that. If unsuccessful (e.g. because the rule contains approximate types),
             then parse each quantifier-free instance of `rwRule` in `ruleInstances` and return all of those. -/
          match ← Parser.SMTTerm.tryParseTermAndAbstractSelectors rwRule symbolMap selectorMVars with
          | some parsedRule => return [some parsedRule]
          | none => ruleInstances.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      )
    -- Filter out `none` results from the above lists (so we can gracefully ignore lemmas that we couldn't parse)
    let preprocessFacts := preprocessFacts.filterMap id
    let theoryLemmas := theoryLemmas.filterMap id
    let instantiations := instantiations.filterMap id
    let computationLemmas := computationLemmas.filterMap id
    let polynomialLemmas := polynomialLemmas.filterMap id
    let rewriteFacts := rewriteFacts.map (fun rwFacts => rwFacts.filterMap id)
    return some (unsatCoreDerivLeafStrings, selectorArr, preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)

/-- Runs `auto`'s monomorphization and preprocessing, then returns `solverHints` determined by the external prover's output -/
def runAutoGetHints (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM solverHints :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (solverHints, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM solverHints) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    return solverHints
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM solverHints := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      if auto.tptp.premiseSelection.get (← getOptions) then
        let (_, some unsatCore) ← queryTPTP exportFacts
          | throwError "runAutoGetHints :: External TPTP solver unable to solve the goal"
        let mut unsatCoreDerivLeafStrings := #[]
        for fact in unsatCore do
          let factDTR ← LamReif.collectDerivFor fact
          unsatCoreDerivLeafStrings := unsatCoreDerivLeafStrings ++ factDTR.collectLeafStrings
          trace[auto.tptp.unsatCore.deriv] "{fact} DTR: {factDTR}"
        -- When the external prover uses the TPTP format, only information about the unsat core can be collected
        return (unsatCoreDerivLeafStrings, #[], [], [], [], [], [], [])
      else
        throwError "runAutoGetHints :: No hints to return if auto.tptp is enabled but auto.tptp.premiseSelection is disabled"
    -- **SMT**
    else if auto.smt.get (← getOptions) then
      if let .some solverHints ← querySMTForHints exportFacts exportInds then
        return solverHints
      else
        throwError "runAutoGetHints :: SMT solver was unable to find a proof"
    -- **Native Prover**
    else
      throwError "runAutoGetHints :: Either auto.smt or auto.tptp must be enabled"

syntax (name := autoGetHints) "autoGetHints" autoinstr hints (uord)* : tactic

/-- Given an expression `∀ x1 : t1, x2 : t2, ... xn : tn, b`, returns `[t1, t2, ..., tn]`. If the given expression is not
    a forall expression, then `getForallArgumentTypes` just returns the empty list -/
partial def getForallArgumentTypes (e : Expr) : List Expr :=
  match e.consumeMData with
  | Expr.forallE _ t b _ => t :: (getForallArgumentTypes b)
  | _ => []

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForInhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`, and if it is passed in a different constructor, it
    returns the default value of the appropriate type. -/
def buildSelectorForInhabitedType (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  let (cval, lvls) ← matchConstCtor selCtor.getAppFn'
    (fun _ => throwError "buildSelectorForInhabitedType :: {selCtor} is not a constructor")
    (fun cval lvls => pure (cval, lvls))
  let selCtorParams := selCtor.getAppArgs
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := (getForallArgumentTypes selCtorType).toArray
  let selectorOutputType ←
    match selCtorFieldTypes[argIdx]? with
    | some outputType => pure outputType
    | none => throwError "buildSelectorForInhabitedType :: argIdx {argIdx} out of bounds for constructor {selCtor}"
  let selectorOutputUniverseLevel ← do
    let selectorOutputTypeSort ← Meta.inferType selectorOutputType
    pure selectorOutputTypeSort.sortLevel!
  let datatypeName := cval.induct
  let datatype ← Meta.mkAppM' (mkConst datatypeName lvls) selCtorParams
  let ival ← matchConstInduct datatype.getAppFn
    (fun _ => throwError "buildSelectorForInhabitedType :: The datatype of {selCtor} ({datatype}) is not a datatype")
    (fun ival _ => pure ival)
  let mutuallyRecursiveDatatypes ← ival.all.mapM
    (fun n => do
      let nConst ← Meta.mkAppM' (mkConst n lvls) selCtorParams
      matchConstInduct nConst.getAppFn
        (fun _ => throwError "buildSelectorForInhabitedType :: Error in gathering InductiveVal for {nConst} which should be mutually recursive with {datatype}")
        (fun ival _ => pure (nConst, ival)))
  let recursor := (mkConst (.str datatypeName "rec") (selectorOutputUniverseLevel :: lvls))
  let mut recursorArgs := selCtorParams
  let motives := mutuallyRecursiveDatatypes.map (fun (t, _) => Expr.lam `_ t selectorOutputType .default)
  recursorArgs := recursorArgs ++ motives.toArray
  let datatypesAndMotives := mutuallyRecursiveDatatypes.zip motives
  for (curDatatype, curDatatypeInfo) in mutuallyRecursiveDatatypes do
    for curCtorIdx in [:curDatatypeInfo.ctors.length] do
      if curDatatype == datatype && curCtorIdx == cval.cidx then
        let decls := selCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) curCtorFields[argIdx]!
        recursorArgs := recursorArgs.push nextRecursorArg
      else
        let curCtor := mkConst curDatatypeInfo.ctors[curCtorIdx]! lvls
        let curCtor ← Meta.mkAppOptM' curCtor (selCtorParams.map some)
        let curCtorType ← Meta.inferType curCtor
        let curCtorFieldTypes := (getForallArgumentTypes curCtorType).toArray
        let decls := curCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) $ ← Meta.mkAppOptM `Inhabited.default #[some selectorOutputType, none]
        recursorArgs := recursorArgs.push nextRecursorArg
  Meta.mkAppOptM' recursor $ recursorArgs.map some

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForUninhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`, and if it is passed in a different constructor, it
    returns `sorry`. -/
def buildSelectorForUninhabitedType (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  let (cval, lvls) ← matchConstCtor selCtor.getAppFn'
    (fun _ => throwError "buildSelectorForUninhabitedType :: {selCtor} is not a constructor")
    (fun cval lvls => pure (cval, lvls))
  let selCtorParams := selCtor.getAppArgs
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := (getForallArgumentTypes selCtorType).toArray
  let selectorOutputType ←
    match selCtorFieldTypes[argIdx]? with
    | some outputType => pure outputType
    | none => throwError "buildSelectorForUninhabitedType :: argIdx {argIdx} out of bounds for constructor {selCtor}"
  let selectorOutputUniverseLevel ← do
    let selectorOutputTypeSort ← Meta.inferType selectorOutputType
    pure selectorOutputTypeSort.sortLevel!
  let datatypeName := cval.induct
  let datatype ← Meta.mkAppM' (mkConst datatypeName lvls) selCtorParams
  let ival ← matchConstInduct datatype.getAppFn
    (fun _ => throwError "buildSelectorForUninhabitedType :: The datatype of {selCtor} ({datatype}) is not a datatype")
    (fun ival _ => pure ival)
  let mutuallyRecursiveDatatypes ← ival.all.mapM
    (fun n => do
      let nConst ← Meta.mkAppM' (mkConst n lvls) selCtorParams
      matchConstInduct nConst.getAppFn
        (fun _ => throwError "buildSelectorForUninhabitedType :: Error in gathering InductiveVal for {nConst} which should be mutually recursive with {datatype}")
        (fun ival _ => pure (nConst, ival)))
  let recursor := (mkConst (.str datatypeName "rec") (selectorOutputUniverseLevel :: lvls))
  let mut recursorArgs := selCtorParams
  let motives := mutuallyRecursiveDatatypes.map (fun (t, _) => Expr.lam `_ t selectorOutputType .default)
  recursorArgs := recursorArgs ++ motives.toArray
  let datatypesAndMotives := mutuallyRecursiveDatatypes.zip motives
  for (curDatatype, curDatatypeInfo) in mutuallyRecursiveDatatypes do
    for curCtorIdx in [:curDatatypeInfo.ctors.length] do
      if curDatatype == datatype && curCtorIdx == cval.cidx then
        let decls := selCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) curCtorFields[argIdx]!
        recursorArgs := recursorArgs.push nextRecursorArg
      else
        let curCtor := mkConst curDatatypeInfo.ctors[curCtorIdx]! lvls
        let curCtor ← Meta.mkAppOptM' curCtor (selCtorParams.map some)
        let curCtorType ← Meta.inferType curCtor
        let curCtorFieldTypes := (getForallArgumentTypes curCtorType).toArray
        let decls := curCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) $ ← Meta.mkSorry selectorOutputType false
        recursorArgs := recursorArgs.push nextRecursorArg
  Meta.mkAppOptM' recursor $ recursorArgs.map some

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForInhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`. -/
def buildSelector (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  try
    buildSelectorForInhabitedType selCtor argIdx
  catch _ =>
    buildSelectorForUninhabitedType selCtor argIdx

/-- Given the information relating to a selector of type `idt → argType`, returns the selector fact entailed by SMT-Lib's semantics
    (`∃ f : idt → argType, ∀ ctor_fields, f (ctor ctor_fields) = ctor_fields[argIdx]`)-/
def buildSelectorFact (selName : String) (selCtor selType : Expr) (argIdx : Nat) : MetaM Expr := do
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := getForallArgumentTypes selCtorType
  let selCtorDeclInfos : Array (Name × (Array Expr → MetaM Expr)) ← do
    let mut declInfos := #[]
    let mut declCounter := 0
    let baseName := "arg"
    for selCtorFieldType in selCtorFieldTypes do
      let argName := Name.str .anonymous (baseName ++ declCounter.repr)
      let argConstructor : Array Expr → MetaM Expr := (fun _ => pure selCtorFieldType)
      declInfos := declInfos.push (argName, argConstructor)
      declCounter := declCounter + 1
    pure declInfos
  Meta.withLocalDeclD (.str .anonymous selName) selType $ fun selectorFVar => do
    Meta.withLocalDeclsD selCtorDeclInfos $ fun selCtorArgFVars => do
      let selCtorWithFields ← Meta.mkAppM' selCtor selCtorArgFVars
      let selectedArg := selCtorArgFVars[argIdx]!
      let existsBody ← Meta.mkForallFVars selCtorArgFVars $ ← Meta.mkAppM ``Eq #[← Meta.mkAppM' selectorFVar #[selCtorWithFields], selectedArg]
      let existsArg ← Meta.mkLambdaFVars #[selectorFVar] existsBody (binderInfoForMVars := .default)
      Meta.mkAppM ``Exists #[existsArg]

/-- `ppOptionsSetting` is used to ensure that the tactics suggested by `autoGetHints` are pretty printed correctly -/
def ppOptionsSetting (o : Options) : Options :=
  let o := o.set `pp.analyze true
  let o := o.set `pp.proofs true
  let o := o.set `pp.funBinderTypes true
  let o := o.set `pp.analyze.trustOfNat false
  o.set `pp.piBinderTypes true

@[tactic autoGetHints]
def evalAutoGetHints : Tactic
| `(autoGetHints | autoGetHints%$stxRef $instr $hints $[$uords]*) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let (_, selectorInfos, lemmas) ← runAutoGetHints lemmas inhFacts
      IO.println s!"Auto found hints. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      let allLemmas :=
        lemmas.1 ++ lemmas.2.1 ++ lemmas.2.2.1 ++ lemmas.2.2.2.1 ++ lemmas.2.2.2.2.1 ++
        (lemmas.2.2.2.2.2.foldl (fun acc l => acc ++ l) [])
      if allLemmas.length = 0 then
        IO.println "SMT solver did not generate any theory lemmas"
      else
        let mut tacticsArr := #[]
        for (selName, selCtor, argIdx, selType) in selectorInfos do
          let selFactName := selName ++ "Fact"
          let selector ← buildSelector selCtor argIdx
          let selectorStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selector
          let selectorFact ← buildSelectorFact selName selCtor selType argIdx
          let selectorFactStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selectorFact
          let existsIntroStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab (mkConst ``Exists.intro)
          tacticsArr := tacticsArr.push $
            ← `(tactic|
                have ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                  apply $existsIntroStx:term $selectorStx:term
                  intros
                  rfl
              )
          evalTactic $ -- Eval to add selector and its corresponding fact to lctx
            ← `(tactic|
                have ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                  apply $existsIntroStx:term $selectorStx:term
                  intros
                  rfl
              )
        let lemmasStx ← withMainContext do -- Use updated main context so that newly added selectors are accessible
          let lctx ← getLCtx
          let mut selectorFVars := #[]
          for (selUserName, _, _, _) in selectorInfos do
            match lctx.findFromUserName? (.str .anonymous selUserName) with
            | some decl => selectorFVars := selectorFVars.push (.fvar decl.fvarId)
            | none => throwError "evalAutoGetHints :: Error in trying to access selector definition for {selUserName}"
          let allLemmas := allLemmas.map (fun lem => lem.instantiateRev selectorFVars)
          trace[auto.tactic] "allLemmas: {allLemmas}"
          allLemmas.mapM (fun lemExp => withOptions ppOptionsSetting $ PrettyPrinter.delab lemExp)
        for lemmaStx in lemmasStx do
          tacticsArr := tacticsArr.push $ ← `(tactic| have : $lemmaStx := sorry)
        tacticsArr := tacticsArr.push $ ← `(tactic| sorry)
        let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tacticsArr*)
        withOptions ppOptionsSetting $ Aesop.addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      let finalGoal ← getMainGoal -- Need to update main goal because running evalTactic to add selectors can change the main goal
      finalGoal.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

end Auto
