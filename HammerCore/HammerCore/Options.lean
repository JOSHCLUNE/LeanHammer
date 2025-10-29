import Lean
import Auto

open Lean Parser Elab Tactic

initialize Lean.registerTraceClass `hammer.debug

-- An option to specify the external prover that `hammer` uses
declare_syntax_cat Hammer.solverOption (behavior := symbol)
-- An option to specify the preprocessing that `hammer` uses
declare_syntax_cat Hammer.preprocessing (behavior := symbol)
-- An option to specify other configuration options for `hammer`
declare_syntax_cat Hammer.configOption (behavior := symbol)
-- An option to indicate a boolean value (used for toggling `disableAesop` and `disableAuto`)
declare_syntax_cat Hammer.bool_lit (behavior := symbol)
syntax "true" : Hammer.bool_lit
syntax "false" : Hammer.bool_lit

register_option hammer.solverDefault : String := {
  defValue := "zipperposition_exe"
  descr := "The default value of the solver option"
}

register_option hammer.solverTimeoutDefault : Nat := {
  defValue := 10
  descr := "The default timeout for the solver (in seconds)"
}

register_option hammer.preprocessingDefault : String := {
  defValue := "aesop"
  descr := "The default value of the preprocessing option"
}

register_option hammer.disableAesopDefault : Bool := {
  defValue := false
  descr := "The default value of the disableAesop option"
}

register_option hammer.disableDuperDefault : Bool := {
  defValue := false
  descr := "The default value of the disableDuper option"
}

register_option hammer.disableSmtDefault : Bool := {
  defValue := false
  descr := "The default value of the disableSmt option"
}

register_option hammer.aesopPremisesDefault : Nat := {
  defValue := 32
  descr := "The default number of premises sent to aesop to be used as unsafe rules"
}

register_option hammer.duperPremisesDefault : Nat := {
  defValue := 16
  descr := "The default number of premises sent to the auto/zipperposition/duper pipeline"
}

register_option hammer.smtPremisesDefault : Nat := {
  defValue := 16
  descr := "The default number of premises sent to lean-smt"
}

register_option hammer.aesopPremisePriorityDefault : Nat := {
  defValue := 20
  descr := "The default priority of premises sent to aesop"
}

register_option hammer.aesopDuperPriorityDefault : Nat := {
  defValue := 10
  descr := "The default priority of calls to the auto/zipperposition/duper pipeline within aesop"
}

register_option hammer.smtPriorityDefault : Nat := {
  defValue := 10
  descr := "The default priority of calls to lean-smt"
}

namespace HammerCore

def getHammerSolverDefault (opts : Options) : String := hammer.solverDefault.get opts
def getHammerSolverTimeoutDefault (opts : Options) : Nat := hammer.solverTimeoutDefault.get opts
def getPreprocessingDefault (opts : Options) : String := hammer.preprocessingDefault.get opts
def getDisableAesopDefault (opts : Options) : Bool := hammer.disableAesopDefault.get opts
def getDisableDuperDefault (opts : Options) : Bool := hammer.disableDuperDefault.get opts
def getDisableSmtDefault (opts : Options) : Bool := hammer.disableSmtDefault.get opts
def getDuperPremisesDefault (opts : Options) : Nat := hammer.duperPremisesDefault.get opts
def getAesopPremisesDefault (opts : Options) : Nat := hammer.aesopPremisesDefault.get opts
def getSmtPremisesDefault (opts : Options) : Nat := hammer.smtPremisesDefault.get opts
def getAesopPremisePriorityDefault (opts : Options) : Nat := hammer.aesopPremisePriorityDefault.get opts
def getAesopDuperPriorityDefault (opts : Options) : Nat := hammer.aesopDuperPriorityDefault.get opts
def getSmtPriorityDefault (opts : Options) : Nat := hammer.smtPriorityDefault.get opts

def getHammerSolverDefaultM : CoreM String := do
  let opts ← getOptions
  return getHammerSolverDefault opts

def getHammerSolverTimeoutDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getHammerSolverTimeoutDefault opts

def getPreprocessingDefaultM : CoreM String := do
  let opts ← getOptions
  return getPreprocessingDefault opts

def getDisableAesopDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableAesopDefault opts

def getDisableDuperDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableDuperDefault opts

def getDisableSmtDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableSmtDefault opts

def getDuperPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getDuperPremisesDefault opts

def getAesopPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisesDefault opts

def getSmtPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getSmtPremisesDefault opts

def getAesopPremisePriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisePriorityDefault opts

def getAesopDuperPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopDuperPriorityDefault opts

def getSmtPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getSmtPriorityDefault opts

syntax "zipperposition_exe" : Hammer.solverOption
syntax "zipperposition" : Hammer.solverOption

syntax "simp_target" : Hammer.preprocessing -- Corresponds to `simp`
syntax "simp_all" : Hammer.preprocessing -- Corresponds to `simp_all`
syntax "no_preprocessing" : Hammer.preprocessing -- Corresponds to skipping all preprocessing
syntax "aesop" : Hammer.preprocessing -- Corresponds to integrating with `aesop` (thus using `aesop` for preprocessing)

inductive Solver where
| zipperposition_exe -- The default solver that uses the executable retrieved by `lean-auto`'s post-update hook
| zipperposition -- Calls a local installation of Zipperposition
deriving ToExpr, BEq

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
    | _ => Elab.throwUnsupportedSyntax

def elabSolverOptionDefault : CoreM Solver := do
  let solverName ← getHammerSolverDefaultM
  match solverName with
  | "zipperposition_exe" => return zipperposition_exe
  | "zipperposition" => return zipperposition
  | _ => throwError "Unsupported default solver option: {solverName}"

def elabPreprocessing [Monad m] [MonadError m] (stx : TSyntax `Hammer.preprocessing) : m Preprocessing :=
  withRef stx do
    match stx with
    | `(preprocessing| simp_target) => return simp_target
    | `(preprocessing| simp_all) => return simp_all
    | `(preprocessing| no_preprocessing) => return no_preprocessing
    | `(preprocessing| aesop) => return aesop
    | _ => Elab.throwUnsupportedSyntax

def elabPreprocessingDefault : CoreM Preprocessing := do
  let preprocessingName ← getPreprocessingDefaultM
  match preprocessingName with
  | "simp_target" => return simp_target
  | "simp_all" => return simp_all
  | "no_preprocessing" => return no_preprocessing
  | "aesop" => return aesop
  | _ => throwError "Unsupported default preprocessing option: {preprocessingName}"

def elabBoolLit [Monad m] [MonadError m] (stx : TSyntax `Hammer.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => Elab.throwUnsupportedSyntax

syntax (&"solver" " := " Hammer.solverOption) : Hammer.configOption
syntax (&"solverTimeout" " := " numLit) : Hammer.configOption
syntax (&"preprocessing" " := " Hammer.preprocessing) : Hammer.configOption
syntax (&"disableDuper" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"disableAesop" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"disableSmt" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"duperPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to the auto/zipperposition/duper pipeline (default: 16)
syntax (&"aesopPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to `aesop` (default: 32)
syntax (&"smtPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to lean-smt (default: 16)
syntax (&"aesopPremisePriority" " := " numLit) : Hammer.configOption -- The priority of premises sent to `aesop` (default: 20)
syntax (&"aesopDuperPriority" " := " numLit) : Hammer.configOption -- The priority of calls to the auto/zipperposition/duper pipeline within `aesop` (default: 10)
syntax (&"leanSmtPriority" " := " numLit) : Hammer.configOption -- The priority of calls to lean-smt (default: 10)

structure ConfigurationOptions where
  solver : Solver
  solverTimeout : Nat
  preprocessing : Preprocessing
  disableDuper : Bool
  disableAesop : Bool
  disableSmt : Bool
  aesopPremisePriority : Nat
  aesopDuperPriority : Nat
  smtPriority : Nat
  duperPremises : Nat -- The number of premises sent to the auto/zipperposition/duper pipeline (default: 16)
  aesopPremises : Nat -- The number of premises sent to `aesop` (default: 32)
  smtPremises : Nat -- The number of premises sent to lean-smt (default: 16)
deriving ToExpr

syntax hammerStar := "*"

/-- Checks to ensure that the set of given `configOptions` is usable. -/
def validateConfigOptions (configOptions : ConfigurationOptions) : TacticM ConfigurationOptions := do
  if configOptions.disableAesop && configOptions.disableDuper && configOptions.disableSmt then
    throwError "Erroneous invocation of hammer: The aesop, duper, and lean-smt options cannot all be disabled"
  if configOptions.disableAesop && configOptions.preprocessing == Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing cannot be set to aesop when aesop is disabled"
  if !configOptions.disableAesop && configOptions.preprocessing != Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing must be set to aesop when aesop is enabled"
  if !configOptions.disableDuper && configOptions.solver == Solver.zipperposition_exe then
    try
      let _ ← Auto.Solver.TPTP.getZipperpositionExePath -- This throws an error if the executable can't be found
    catch _ =>
      if configOptions.disableAesop then
        throwError "The bundled zipperposition executable could not be found. To retrieve it, run `lake update`."
      else
        logWarning "The bundled zipperposition executable could not be found. To retrieve it, run `lake update`. Continuing with auto disabled..."
        return {configOptions with disableDuper := true}
  return configOptions

def parseConfigOptions (configOptionsStx : TSyntaxArray `Hammer.configOption) : TacticM ConfigurationOptions := do
  let mut solverOpt := none
  let mut solverTimeoutOpt := none
  let mut preprocessingOpt := none
  let mut disableDuperOpt := none
  let mut disableAesopOpt := none
  let mut disableSmtOpt := none
  let mut duperPremisesOpt := none
  let mut aesopPremisesOpt := none
  let mut smtPremisesOpt := none
  let mut aesopPremisePriorityOpt := none
  let mut aesopDuperPriorityOpt := none
  let mut smtPriorityOpt := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(Hammer.configOption| solver := $solverName:Hammer.solverOption) =>
      if solverOpt.isNone then solverOpt ← elabSolverOption solverName
      else throwError "Erroneous invocation of hammer: The solver option has been specified multiple times"
    | `(Hammer.configOption| solverTimeout := $userSolverTimeout:num) =>
      if solverTimeoutOpt.isNone then solverTimeoutOpt := some (TSyntax.getNat userSolverTimeout)
      else throwError "Erroneous invocation of hammer: The solverTimeout option has been specified multiple times"
    | `(Hammer.configOption| preprocessing := $preprocessing:Hammer.preprocessing) =>
      if preprocessingOpt.isNone then preprocessingOpt ← elabPreprocessing preprocessing
      else throwError "Erroneous invocation of hammer: The preprocessing option has been specified multiple times"
    | `(Hammer.configOption| disableDuper := $disableDuperBoolLit:Hammer.bool_lit) =>
      if disableDuperOpt.isNone then disableDuperOpt := some $ ← elabBoolLit disableDuperBoolLit
      else throwError "Erroneous invocation of hammer: The disableAuto option has been specified multiple times"
    | `(Hammer.configOption| disableAesop := $disableAesopBoolLit:Hammer.bool_lit) =>
      if disableAesopOpt.isNone then disableAesopOpt := some $ ← elabBoolLit disableAesopBoolLit
      else throwError "Erroneous invocation of hammer: The disableAesop option has been specified multiple times"
    | `(Hammer.configOption| disableSmt := $disableSmtBoolLit:Hammer.bool_lit) =>
      if disableSmtOpt.isNone then disableSmtOpt := some $ ← elabBoolLit disableSmtBoolLit
      else throwError "Erroneous invocation of hammer: The disableLeanSmt option has been specified multiple times"
    | `(Hammer.configOption| duperPremises := $userDuperPremises:num) =>
      if duperPremisesOpt.isNone then duperPremisesOpt := some (TSyntax.getNat userDuperPremises)
      else throwError "Erroneous invocation of hammer: The autoPremises option has been specified multiple times"
    | `(Hammer.configOption| aesopPremises := $userAesopPremises:num) =>
      if aesopPremisesOpt.isNone then aesopPremisesOpt := some (TSyntax.getNat userAesopPremises)
      else throwError "Erroneous invocation of hammer: The aesopPremises option has been specified multiple times"
    | `(Hammer.configOption| smtPremises := $userSmtPremises:num) =>
      if smtPremisesOpt.isNone then smtPremisesOpt := some (TSyntax.getNat userSmtPremises)
      else throwError "Erroneous invocation of hammer: The smtPremises option has been specified multiple times"
    | `(Hammer.configOption| aesopPremisePriority := $userAesopPremisePriority:num) =>
      if aesopPremisePriorityOpt.isNone then aesopPremisePriorityOpt := some (TSyntax.getNat userAesopPremisePriority)
      else throwError "Erroneous invocation of hammer: The aesopPremisePriority option has been specified multiple times"
    | `(Hammer.configOption| aesopDuperPriority := $userAesopDuperPriority:num) =>
      if aesopDuperPriorityOpt.isNone then aesopDuperPriorityOpt := some (TSyntax.getNat userAesopDuperPriority)
      else throwError "Erroneous invocation of hammer: The aesopAutoPriority option has been specified multiple times"
    | `(Hammer.configOption| leanSmtPriority := $userSmtPriority:num) =>
      if smtPriorityOpt.isNone then smtPriorityOpt := some (TSyntax.getNat userSmtPriority)
      else throwError "Erroneous invocation of hammer: The leanSmtPriority option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  let solver ← -- **TODO** Come up with a better name for the `solver` option, since it's exclusively used for the Lean-auto/Zipperposition/Duper pipeline
    match solverOpt with
    | none => elabSolverOptionDefault
    | some solver => pure solver
  let solverTimeout ←
    match solverTimeoutOpt with
    | none => getHammerSolverTimeoutDefaultM
    | some solverTimeout => pure solverTimeout
  let disableDuper ←
    match disableDuperOpt with
    | none => getDisableDuperDefaultM
    | some disableDuper => pure disableDuper
  let disableAesop ←
    match disableAesopOpt with
    | none => getDisableAesopDefaultM
    | some disableAesop => pure disableAesop
  let disableSmt ←
    match disableSmtOpt with
    | none => getDisableSmtDefaultM
    | some disableSmt => pure disableSmt
  let preprocessing ←
    match preprocessingOpt with
    | none =>
      if disableAesop && (← getPreprocessingDefaultM) == "aesop" then pure Preprocessing.simp_all
      else elabPreprocessingDefault
    | some preprocessing => pure preprocessing
  let duperPremises ←
    match duperPremisesOpt with
    | none => getDuperPremisesDefaultM
    | some duperPremises => pure duperPremises
  let aesopPremises ←
    match aesopPremisesOpt with
    | none => getAesopPremisesDefaultM
    | some aesopPremises => pure aesopPremises
  let smtPremises ←
    match smtPremisesOpt with
    | none => getSmtPremisesDefaultM
    | some smtPremises => pure smtPremises
  let aesopPremisePriority ←
    match aesopPremisePriorityOpt with
    | none => getAesopPremisePriorityDefaultM
    | some aesopPremisePriority => pure aesopPremisePriority
  let aesopDuperPriority ←
    match aesopDuperPriorityOpt with
    | none => getAesopDuperPriorityDefaultM
    | some aesopDuperPriority => pure aesopDuperPriority
  let smtPriority ←
    match smtPriorityOpt with
    | none => getSmtPriorityDefaultM
    | some smtPriority => pure smtPriority
  let configOptions :=
    {solver := solver, solverTimeout := solverTimeout, preprocessing := preprocessing, disableDuper := disableDuper, disableAesop := disableAesop,
     disableSmt := disableSmt, duperPremises := duperPremises, aesopPremises := aesopPremises, smtPremises := smtPremises, aesopPremisePriority := aesopPremisePriority,
     aesopDuperPriority := aesopDuperPriority, smtPriority := smtPriority}
  let configOptions ← validateConfigOptions configOptions
  return configOptions

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
  match configOptions.solver with
  | zipperposition_exe =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.tptp.timeout configOptions.solverTimeout
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
        let o := o.set `auto.tptp.timeout configOptions.solverTimeout
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x

def withDuperOptions [Monad m] [MonadError m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `duper.ignoreUnusableFacts true
      o.set `auto.mono.ignoreNonQuasiHigherOrder true
    ) x

end HammerCore
