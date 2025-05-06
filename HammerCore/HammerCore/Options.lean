import Lean

open Lean Parser Elab Tactic

-- An option to specify the external prover that `hammer` uses
declare_syntax_cat Hammer.solverOption (behavior := symbol)
-- An option to specify the preprocessing that `hammer` uses
declare_syntax_cat Hammer.preprocessing (behavior := symbol)
-- An option to specify other configuration options for `hammer`
declare_syntax_cat Hammer.configOption (behavior := symbol)

namespace HammerCore

syntax "zipperposition_exe" : Hammer.solverOption
syntax "zipperposition" : Hammer.solverOption
syntax "cvc5" : Hammer.solverOption

syntax "simp_target" : Hammer.preprocessing -- Corresponds to `simp`
syntax "simp_all" : Hammer.preprocessing -- Corresponds to `simp_all`
syntax "no_preprocessing" : Hammer.preprocessing -- Corresponds to skipping all preprocessing
syntax "aesop" : Hammer.preprocessing -- Corresponds to integrating with `aesop` (thus using `aesop` for preprocessing)

inductive Solver where
| zipperposition_exe -- The default solver that uses the executable retrieved by `lean-auto`'s post-update hook
| zipperposition -- Calls a local installation of Zipperposition
| cvc5 -- Calls a local installation of cvc5
deriving ToExpr

inductive Preprocessing where
| simp_target
| simp_all
| no_preprocessing
| aesop
deriving BEq, ToExpr

open Solver Preprocessing

def elabSolverOption [Monad m] [MonadError m] (stx : TSyntax `Hammer.solverOption) : m Solver :=
  withRef stx do
    match stx with
    | `(solverOption| zipperposition_exe) => return zipperposition_exe
    | `(solverOption| zipperposition) => return zipperposition
    | `(solverOption| cvc5) => return cvc5
    | _ => Elab.throwUnsupportedSyntax

def elabPreprocessing [Monad m] [MonadError m] (stx : TSyntax `Hammer.preprocessing) : m Preprocessing :=
  withRef stx do
    match stx with
    | `(preprocessing| simp_target) => return simp_target
    | `(preprocessing| simp_all) => return simp_all
    | `(preprocessing| no_preprocessing) => return no_preprocessing
    | `(preprocessing| aesop) => return aesop
    | _ => Elab.throwUnsupportedSyntax

syntax (&"solver" " := " Hammer.solverOption) : Hammer.configOption
syntax (&"goalHypPrefix" " := " strLit) : Hammer.configOption
syntax (&"negGoalLemmaName" " := " strLit) : Hammer.configOption
syntax (&"preprocessing" " := " Hammer.preprocessing) : Hammer.configOption
syntax (&"disableAuto") : Hammer.configOption
syntax (&"disableAesop") : Hammer.configOption
syntax (&"k1" " := " numLit) : Hammer.configOption -- The number of premises sent to `auto` (default: 16)
syntax (&"k2" " := " numLit) : Hammer.configOption -- The number of premises sent to `aesop` (default: 32)
syntax (&"aesopPremisePriority" " := " numLit) : Hammer.configOption -- The priority of premises sent to `aesop` (default: 20)
syntax (&"aesopAutoPriority" " := " numLit) : Hammer.configOption -- The priority of calls to `auto` within `aesop` (default: 10)

structure ConfigurationOptions where
  solver : Solver
  goalHypPrefix : String
  negGoalLemmaName : String
  preprocessing : Preprocessing
  disableAuto : Bool
  disableAesop : Bool
  aesopPremisePriority : Nat
  aesopAutoPriority : Nat
  k1 : Nat -- The number of premises sent to `auto` (default: 16)
  k2 : Nat -- The number of premises sent to `aesop` (default: 32)
deriving ToExpr

syntax hammerStar := "*"
syntax (name := hammerCore) "hammerCore"
  (ppSpace "[" ((simpErase <|> simpLemma),*,?)  "]")
  (ppSpace "[" (hammerStar <|> term),* "]")
  (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules | `(tactic| hammerCore [$simpLemmas,*] [$facts,*]) => `(tactic| hammerCore [$simpLemmas,*] [$facts,*] {})

/-- Checks to ensure that the set of given `configOptions` is usable. -/
def validateConfigOptions (configOptions : ConfigurationOptions) : TacticM Unit := do
  if configOptions.disableAesop && configOptions.disableAuto then
    throwError "Erroneous invocation of hammer: The aesop and auto options cannot both be disabled"
  if configOptions.disableAesop && configOptions.preprocessing == Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing cannot be set to aesop when aesop is disabled"
  if !configOptions.disableAesop && configOptions.preprocessing != Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing must be set to aesop when aesop is enabled"

def parseConfigOptions (configOptionsStx : TSyntaxArray `Hammer.configOption) : TacticM ConfigurationOptions := do
  let mut solverOpt := none
  let mut goalHypPrefix := ""
  let mut negGoalLemmaName := ""
  let mut preprocessingOpt := none
  let mut disableAuto := false
  let mut disableAesop := false
  let mut k1Opt := none
  let mut k2Opt := none
  let mut aesopPremisePriorityOpt := none
  let mut aesopAutoPriorityOpt := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(Hammer.configOption| solver := $solverName:Hammer.solverOption) =>
      if solverOpt.isNone then solverOpt ← elabSolverOption solverName
      else throwError "Erroneous invocation of hammer: The solver option has been specified multiple times"
    | `(Hammer.configOption| goalHypPrefix := $userGoalHypPrefix:str) =>
      if goalHypPrefix.isEmpty then goalHypPrefix := userGoalHypPrefix.getString
      else throwError "Erroneous invocation of hammer: The goalHypPrefix option has been specified multiple times"
    | `(Hammer.configOption| negGoalLemmaName := $userNegGoalLemmaName:str) =>
      if negGoalLemmaName.isEmpty then negGoalLemmaName := userNegGoalLemmaName.getString
      else throwError "Erroneous invocation of hammer: The negGoalLemmaName option has been specified multiple times"
    | `(Hammer.configOption| preprocessing := $preprocessing:Hammer.preprocessing) =>
      if preprocessingOpt.isNone then preprocessingOpt ← elabPreprocessing preprocessing
      else throwError "Erroneous invocation of hammer: The preprocessing option has been specified multiple times"
    | `(Hammer.configOption| disableAuto) => disableAuto := true
    | `(Hammer.configOption| disableAesop) => disableAesop := true
    | `(Hammer.configOption| k1 := $userK1:num) =>
      if k1Opt.isNone then k1Opt := some (TSyntax.getNat userK1)
      else throwError "Erroneous invocation of hammer: The k1 option has been specified multiple times"
    | `(Hammer.configOption| k2 := $userK2:num) =>
      if k2Opt.isNone then k2Opt := some (TSyntax.getNat userK2)
      else throwError "Erroneous invocation of hammer: The k2 option has been specified multiple times"
    | `(Hammer.configOption| aesopPremisePriority := $userAesopPremisePriority:num) =>
      if aesopPremisePriorityOpt.isNone then aesopPremisePriorityOpt := some (TSyntax.getNat userAesopPremisePriority)
      else throwError "Erroneous invocation of hammer: The aesopPremisePriority option has been specified multiple times"
    | `(Hammer.configOption| aesopAutoPriority := $userAesopAutoPriority:num) =>
      if aesopAutoPriorityOpt.isNone then aesopAutoPriorityOpt := some (TSyntax.getNat userAesopAutoPriority)
      else throwError "Erroneous invocation of hammer: The aesopAutoPriority option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  let solver :=
    match solverOpt with
    | none => Solver.zipperposition_exe
    | some solver => solver
  if goalHypPrefix.isEmpty then goalHypPrefix := "h"
  if negGoalLemmaName.isEmpty then negGoalLemmaName := "negGoal"
  let preprocessing :=
    match preprocessingOpt with
    | none =>
      if disableAesop then Preprocessing.simp_all
      else Preprocessing.aesop
    | some preprocessing => preprocessing
  let k1 :=
    match k1Opt with
    | none => 16
    | some k1 => k1
  let k2 :=
    match k2Opt with
    | none => 32
    | some k2 => k2
  let aesopPremisePriority :=
    match aesopPremisePriorityOpt with
    | none => 20
    | some aesopPremisePriority => aesopPremisePriority
  let aesopAutoPriority :=
    match aesopAutoPriorityOpt with
    | none => 10
    | some aesopAutoPriority => aesopAutoPriority
  let configOptions :=
    {solver := solver, goalHypPrefix := goalHypPrefix, negGoalLemmaName := negGoalLemmaName, preprocessing := preprocessing, disableAuto := disableAuto,
     disableAesop := disableAesop, k1 := k1, k2 := k2, aesopPremisePriority := aesopPremisePriority, aesopAutoPriority := aesopAutoPriority}
  validateConfigOptions configOptions
  return configOptions

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
  match configOptions.solver with
  | zipperposition_exe =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition_exe"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x
  | zipperposition =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x
  | cvc5 => throwError "cvc5 hammer support not implemented yet"

def withDuperOptions [Monad m] [MonadError m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `duper.ignoreUnusableFacts true
      o.set `auto.mono.ignoreNonQuasiHigherOrder true
    ) x

end HammerCore
