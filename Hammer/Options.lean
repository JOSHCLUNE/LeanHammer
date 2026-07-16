import Lean
import Auto

open Lean Parser Elab Tactic

-- An option to specify the preprocessing that `hammer` uses
declare_syntax_cat Hammer.preprocessing (behavior := symbol)
-- An option to specify other configuration options for `hammer`
declare_syntax_cat Hammer.configOption (behavior := symbol)
-- An option to indicate a boolean value (used for toggling `disableAesop` and `disableDuper`)
declare_syntax_cat Hammer.bool_lit (behavior := symbol)
syntax "true" : Hammer.bool_lit
syntax "false" : Hammer.bool_lit

register_option hammer.solverTimeoutDefault : Nat := {
  defValue := 5
  descr := "The default timeout for the solver (in seconds)"
}

register_option hammer.wallclockTimeoutDefault : Nat := {
  defValue := 10
  descr := "The default wallclock timeout for `hammer` (in seconds). A timeout of 0 means no timeout."
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

register_option hammer.disableGrindDefault : Bool := {
  defValue := false
  descr := "The default value of the disableGrind option"
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
  descr := "The default number of premises sent to duper"
}

register_option hammer.grindPremisesDefault : Nat := {
  defValue := 100
  descr := "The default number of premises sent to grind"
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
  descr := "The default priority of calls to duper within aesop"
}

register_option hammer.aesopGrindPriorityDefault : Nat := {
  defValue := 5
  descr := "The default priority of calls to grind within aesop"
}

register_option hammer.aesopSmtPriorityDefault : Nat := {
  defValue := 10
  descr := "The default priority of calls to lean-smt within aesop"
}

register_option hammer.parallelismDefault : Bool := {
  defValue := true
  descr := "The default value of the parallelism option"
}

register_option hammer.outputAllSuggestionsDefault : Bool := {
  defValue := false
  descr := "The default value of the outputAllSuggestions option"
}

namespace HammerCore

def getHammerSolverTimeoutDefault (opts : Options) : Nat := hammer.solverTimeoutDefault.get opts
def getHammerWallclockTimeoutDefault (opts : Options) : Nat := hammer.wallclockTimeoutDefault.get opts
def getPreprocessingDefault (opts : Options) : String := hammer.preprocessingDefault.get opts
def getDisableAesopDefault (opts : Options) : Bool := hammer.disableAesopDefault.get opts
def getDisableDuperDefault (opts : Options) : Bool := hammer.disableDuperDefault.get opts
def getDisableGrindDefault (opts : Options) : Bool := hammer.disableGrindDefault.get opts
def getDisableSmtDefault (opts : Options) : Bool := hammer.disableSmtDefault.get opts
def getDuperPremisesDefault (opts : Options) : Nat := hammer.duperPremisesDefault.get opts
def getAesopPremisesDefault (opts : Options) : Nat := hammer.aesopPremisesDefault.get opts
def getGrindPremisesDefault (opts : Options) : Nat := hammer.grindPremisesDefault.get opts
def getSmtPremisesDefault (opts : Options) : Nat := hammer.smtPremisesDefault.get opts
def getAesopPremisePriorityDefault (opts : Options) : Nat := hammer.aesopPremisePriorityDefault.get opts
def getAesopDuperPriorityDefault (opts : Options) : Nat := hammer.aesopDuperPriorityDefault.get opts
def getAesopGrindPriorityDefault (opts : Options) : Nat := hammer.aesopGrindPriorityDefault.get opts
def getAesopSmtPriorityDefault (opts : Options) : Nat := hammer.aesopSmtPriorityDefault.get opts
def getParallelismDefault (opts : Options) : Bool := hammer.parallelismDefault.get opts
def getOutputAllSuggestionsDefault (opts : Options) : Bool := hammer.outputAllSuggestionsDefault.get opts

def getHammerSolverTimeoutDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getHammerSolverTimeoutDefault opts

def getHammerWallclockTimeoutDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getHammerWallclockTimeoutDefault opts

def getPreprocessingDefaultM : CoreM String := do
  let opts ← getOptions
  return getPreprocessingDefault opts

def getDisableAesopDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableAesopDefault opts

def getDisableDuperDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableDuperDefault opts

def getDisableGrindDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableGrindDefault opts

def getDisableSmtDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableSmtDefault opts

def getDuperPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getDuperPremisesDefault opts

def getAesopPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisesDefault opts

def getGrindPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getGrindPremisesDefault opts

def getSmtPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getSmtPremisesDefault opts

def getAesopPremisePriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisePriorityDefault opts

def getAesopDuperPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopDuperPriorityDefault opts

def getAesopGrindPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopGrindPriorityDefault opts

def getAesopSmtPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopSmtPriorityDefault opts

def getParallelismDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getParallelismDefault opts

def getOutputAllSuggestionsDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getOutputAllSuggestionsDefault opts

syntax "simp_target" : Hammer.preprocessing -- Corresponds to `simp`
syntax "simp_all" : Hammer.preprocessing -- Corresponds to `simp_all`
syntax "no_preprocessing" : Hammer.preprocessing -- Corresponds to skipping all preprocessing
syntax "aesop" : Hammer.preprocessing -- Corresponds to integrating with `aesop` (thus using `aesop` for preprocessing)

inductive Preprocessing where
| simp_target
| simp_all
| no_preprocessing
| aesop
deriving BEq, ToExpr

open Preprocessing

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

syntax (&"solverTimeout" " := " numLit) : Hammer.configOption
syntax (&"wallclockTimeout" " := " numLit) : Hammer.configOption
syntax (&"preprocessing" " := " Hammer.preprocessing) : Hammer.configOption
syntax (&"disableDuper" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"disableAesop" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"disableGrind" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"disableSmt" " := " Hammer.bool_lit) : Hammer.configOption
syntax (&"duperPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to `duper` (default: 16)
syntax (&"aesopPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to `aesop` (default: 32)
syntax (&"grindPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to `grind` (default: 100)
syntax (&"smtPremises" " := " numLit) : Hammer.configOption -- The number of premises sent to `lean-smt` (default: 16)
syntax (&"aesopPremisePriority" " := " numLit) : Hammer.configOption -- The priority of premises sent to `aesop` (default: 20)
syntax (&"aesopDuperPriority" " := " numLit) : Hammer.configOption -- The priority of calls to `duper` within `aesop` (default: 10)
syntax (&"aesopGrindPriority" " := " numLit) : Hammer.configOption -- The priority of calls to `grind` within `aesop` (default: 5)
syntax (&"aesopSmtPriority" " := " numLit) : Hammer.configOption -- The priority of calls to `lean-smt` within `aesop` (default: 10)
syntax (&"parallelism" " := " Hammer.bool_lit) : Hammer.configOption -- Whether to use parallelism (default: true)
syntax (&"outputAllSuggestions" " := " Hammer.bool_lit) : Hammer.configOption -- Whether to show the user all suggestions or just the first one (default: false)

structure ConfigurationOptions where
  solverTimeout : Nat
  wallclockTimeout : Nat
  preprocessing : Preprocessing
  disableDuper : Bool
  disableAesop : Bool
  disableGrind : Bool
  disableSmt : Bool
  aesopPremisePriority : Nat
  aesopDuperPriority : Nat
  aesopGrindPriority : Nat
  aesopSmtPriority : Nat
  duperPremises : Nat -- The number of premises sent to `duper` (default: 16)
  aesopPremises : Nat -- The number of premises sent to `aesop` (default: 32)
  grindPremises : Nat -- The number of premises sent to `grind` (default: 100)
  smtPremises : Nat -- The number of premises sent to `lean-smt` (default: 16)
  parallelism : Bool -- Whether to use parallelism (default: true)
  outputAllSuggestions : Bool -- Whether to show the user all suggestions or just the first one (default: false)
deriving ToExpr

syntax hammerStar := "*"
syntax (name := hammerCore) "hammerCore"
  (ppSpace "[" ((simpErase <|> simpLemma),*,?)  "]")
  (ppSpace "[" (hammerStar <|> term),* "]")
  (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules | `(tactic| hammerCore [$simpLemmas,*] [$facts,*]) => `(tactic| hammerCore [$simpLemmas,*] [$facts,*] {})

/-- Checks to ensure that the set of given `configOptions` is usable. -/
def validateConfigOptions (configOptions : ConfigurationOptions) : TacticM ConfigurationOptions := do
  if configOptions.wallclockTimeout > 0 && configOptions.wallclockTimeout < configOptions.solverTimeout then
    throwError "Erroneous invocation of hammer: The wallclockTimeout must be greater than or equal to the solverTimeout"
  if !configOptions.parallelism && configOptions.outputAllSuggestions then
    throwError "Erroneous invocation of hammer: The outputAllSuggestions option can only be enabled when parallelism is enabled"
  if configOptions.disableAesop && configOptions.disableDuper && configOptions.disableGrind && configOptions.disableSmt then
    throwError "Erroneous invocation of hammer: The aesop, duper, grind, and smt options cannot all be disabled"
  if configOptions.disableAesop && configOptions.preprocessing == Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing cannot be set to aesop when aesop is disabled"
  if !configOptions.disableAesop && configOptions.preprocessing != Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing must be set to aesop when aesop is enabled"
  if !configOptions.disableDuper then
    let useDefault := auto.tptp.zipperposition.useDefault.get (← getOptions)
    let defaultPath ← Auto.Solver.TPTP.zipperpositionDefaultPath
    let err := (
        s!"Cannot find automatically downloaded Zipperposition executable. " ++
        s!"Try running \"lake build\" at the root directory of this project " ++
        s!"to see if \"zipperposition.exe\" pops up in {defaultPath}. Alternatively, " ++
        s!"you can link LeanHammer to your own installation of Zipperposition by setting " ++
        s!"\"auto.tptp.zipperposition.useDefault\" to false and setting " ++
        s!"\"auto.tptp.zipperposition.customPath\" to your own Zipperposition executable."
      )
    if useDefault && !(← defaultPath.pathExists) then
      -- Log a warning and then continue with duper disabled if possible. Otherwise, just throw an error.
      if !configOptions.disableAesop || !configOptions.disableGrind || !configOptions.disableSmt then
        logWarning $ err ++ " Continuing with the auto → zipperposition → duper pipeline disabled..."
        return {configOptions with disableDuper := true}
      else
        throwError err
  return configOptions

def parseConfigOptions (configOptionsStx : TSyntaxArray `Hammer.configOption) : TacticM ConfigurationOptions := do
  let mut solverTimeoutOpt := none
  let mut wallclockTimeoutOpt := none
  let mut preprocessingOpt := none
  let mut disableDuperOpt := none
  let mut disableAesopOpt := none
  let mut disableGrindOpt := none
  let mut disableSmtOpt := none
  let mut duperPremisesOpt := none
  let mut aesopPremisesOpt := none
  let mut grindPremisesOpt := none
  let mut smtPremisesOpt := none
  let mut aesopPremisePriorityOpt := none
  let mut aesopDuperPriorityOpt := none
  let mut aesopGrindPriorityOpt := none
  let mut aesopSmtPriorityOpt := none
  let mut parallelismOpt := none
  let mut outputAllSuggestionsOpt := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(Hammer.configOption| solverTimeout := $userSolverTimeout:num) =>
      if solverTimeoutOpt.isNone then solverTimeoutOpt := some (TSyntax.getNat userSolverTimeout)
      else throwError "Erroneous invocation of hammer: The solverTimeout option has been specified multiple times"
    | `(Hammer.configOption| wallclockTimeout := $userWallclockTimeout:num) =>
      if wallclockTimeoutOpt.isNone then wallclockTimeoutOpt := some (TSyntax.getNat userWallclockTimeout)
      else throwError "Erroneous invocation of hammer: The wallclockTimeout option has been specified multiple times"
    | `(Hammer.configOption| preprocessing := $preprocessing:Hammer.preprocessing) =>
      if preprocessingOpt.isNone then preprocessingOpt ← elabPreprocessing preprocessing
      else throwError "Erroneous invocation of hammer: The preprocessing option has been specified multiple times"
    | `(Hammer.configOption| disableDuper := $disableDuperBoolLit:Hammer.bool_lit) =>
      if disableDuperOpt.isNone then disableDuperOpt := some $ ← elabBoolLit disableDuperBoolLit
      else throwError "Erroneous invocation of hammer: The disableDuper option has been specified multiple times"
    | `(Hammer.configOption| disableAesop := $disableAesopBoolLit:Hammer.bool_lit) =>
      if disableAesopOpt.isNone then disableAesopOpt := some $ ← elabBoolLit disableAesopBoolLit
      else throwError "Erroneous invocation of hammer: The disableAesop option has been specified multiple times"
    | `(Hammer.configOption| disableGrind := $disableGrindBoolLit:Hammer.bool_lit) =>
      if disableGrindOpt.isNone then disableGrindOpt := some $ ← elabBoolLit disableGrindBoolLit
      else throwError "Erroneous invocation of hammer: The disableGrind option has been specified multiple times"
    | `(Hammer.configOption| disableSmt := $disableSmtBoolLit:Hammer.bool_lit) =>
      if disableSmtOpt.isNone then disableSmtOpt := some $ ← elabBoolLit disableSmtBoolLit
      else throwError "Erroneous invocation of hammer: The disableSmt option has been specified multiple times"
    | `(Hammer.configOption| duperPremises := $userDuperPremises:num) =>
      if duperPremisesOpt.isNone then duperPremisesOpt := some (TSyntax.getNat userDuperPremises)
      else throwError "Erroneous invocation of hammer: The duperPremises option has been specified multiple times"
    | `(Hammer.configOption| aesopPremises := $userAesopPremises:num) =>
      if aesopPremisesOpt.isNone then aesopPremisesOpt := some (TSyntax.getNat userAesopPremises)
      else throwError "Erroneous invocation of hammer: The aesopPremises option has been specified multiple times"
    | `(Hammer.configOption| grindPremises := $userGrindPremises:num) =>
      if grindPremisesOpt.isNone then grindPremisesOpt := some (TSyntax.getNat userGrindPremises)
      else throwError "Erroneous invocation of hammer: The grindPremises option has been specified multiple times"
    | `(Hammer.configOption| smtPremises := $userSmtPremises:num) =>
      if smtPremisesOpt.isNone then smtPremisesOpt := some (TSyntax.getNat userSmtPremises)
      else throwError "Erroneous invocation of hammer: The smtPremises option has been specified multiple times"
    | `(Hammer.configOption| aesopPremisePriority := $userAesopPremisePriority:num) =>
      if aesopPremisePriorityOpt.isNone then aesopPremisePriorityOpt := some (TSyntax.getNat userAesopPremisePriority)
      else throwError "Erroneous invocation of hammer: The aesopPremisePriority option has been specified multiple times"
    | `(Hammer.configOption| aesopDuperPriority := $userAesopDuperPriority:num) =>
      if aesopDuperPriorityOpt.isNone then aesopDuperPriorityOpt := some (TSyntax.getNat userAesopDuperPriority)
      else throwError "Erroneous invocation of hammer: The aesopDuperPriority option has been specified multiple times"
    | `(Hammer.configOption| aesopGrindPriority := $userAesopGrindPriority:num) =>
      if aesopGrindPriorityOpt.isNone then aesopGrindPriorityOpt := some (TSyntax.getNat userAesopGrindPriority)
      else throwError "Erroneous invocation of hammer: The aesopGrindPriority option has been specified multiple times"
    | `(Hammer.configOption| aesopSmtPriority := $userAesopSmtPriority:num) =>
      if aesopSmtPriorityOpt.isNone then aesopSmtPriorityOpt := some (TSyntax.getNat userAesopSmtPriority)
      else throwError "Erroneous invocation of hammer: The aesopSmtPriority option has been specified multiple times"
    | `(Hammer.configOption| parallelism := $parallelismBoolLit:Hammer.bool_lit) =>
      if parallelismOpt.isNone then parallelismOpt := some $ ← elabBoolLit parallelismBoolLit
      else throwError "Erroneous invocation of hammer: The parallelism option has been specified multiple times"
    | `(Hammer.configOption| outputAllSuggestions := $outputAllSuggestionsBoolLit:Hammer.bool_lit) =>
      if outputAllSuggestionsOpt.isNone then outputAllSuggestionsOpt := some $ ← elabBoolLit outputAllSuggestionsBoolLit
      else throwError "Erroneous invocation of hammer: The outputAllSuggestions option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  let solverTimeout ←
    match solverTimeoutOpt with
    | none => getHammerSolverTimeoutDefaultM
    | some solverTimeout => pure solverTimeout
  let wallclockTimeout ←
    match wallclockTimeoutOpt with
    | none => getHammerWallclockTimeoutDefaultM
    | some wallclockTimeout => pure wallclockTimeout
  let disableDuper ←
    match disableDuperOpt with
    | none => getDisableDuperDefaultM
    | some disableDuper => pure disableDuper
  let disableAesop ←
    match disableAesopOpt with
    | none => getDisableAesopDefaultM
    | some disableAesop => pure disableAesop
  let disableGrind ←
    match disableGrindOpt with
    | none => getDisableGrindDefaultM
    | some disableGrind => pure disableGrind
  let disableSmt ←
    match disableSmtOpt with
    | none => getDisableSmtDefaultM
    | some disableSmt => pure disableSmt
  let preprocessing ←
    match preprocessingOpt with
    | none =>
      if disableAesop && (← getPreprocessingDefaultM) == "aesop" then pure Preprocessing.no_preprocessing
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
  let grindPremises ←
    match grindPremisesOpt with
    | none => getGrindPremisesDefaultM
    | some grindPremises => pure grindPremises
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
  let aesopGrindPriority ←
    match aesopGrindPriorityOpt with
    | none => getAesopGrindPriorityDefaultM
    | some aesopGrindPriority => pure aesopGrindPriority
  let aesopSmtPriority ←
    match aesopSmtPriorityOpt with
    | none => getAesopSmtPriorityDefaultM
    | some aesopSmtPriority => pure aesopSmtPriority
  let parallelism ←
    match parallelismOpt with
    | none => getParallelismDefaultM
    | some parallelism => pure parallelism
  let outputAllSuggestions ←
    match outputAllSuggestionsOpt with
    | none => getOutputAllSuggestionsDefaultM
    | some outputAllSuggestions => pure outputAllSuggestions
  let configOptions := {
    solverTimeout := solverTimeout, wallclockTimeout := wallclockTimeout, preprocessing := preprocessing,
    disableDuper := disableDuper, disableGrind := disableGrind, disableAesop := disableAesop, disableSmt := disableSmt,
    duperPremises := duperPremises, aesopPremises := aesopPremises, grindPremises := grindPremises,
    smtPremises := smtPremises, aesopPremisePriority := aesopPremisePriority, aesopDuperPriority := aesopDuperPriority,
    aesopGrindPriority := aesopGrindPriority, aesopSmtPriority := aesopSmtPriority, parallelism := parallelism,
    outputAllSuggestions := outputAllSuggestions
  }
  let configOptions ← validateConfigOptions configOptions
  return configOptions

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
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
