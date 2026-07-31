/-
Tests for downstream users that *have* adopted the module system.

Before LeanHammer adopted the module system this file could not exist at all: a `module` cannot
import a non-`module`, so `public import Hammer` was rejected outright. It runs the same checks as
`HammerTest/Legacy.lean` so that the two consumption paths can be compared directly.
-/
module

public import Hammer

set_option maxHeartbeats 1000000

public theorem hammerTestInvolutive {α : Type} {f : α → α} (h : ∀ x, f (f x) = x) (a : α) :
    f (f a) = a := h a

/-! ## The default configuration (Aesop, with Duper/grind/Lean-SMT as Aesop rules)

These also exercise `runAesopWithSubprocedures`, which reflects `ConfigurationOptions` into an
`Expr` and `addAndCompile`s Aesop rule tactics. That is the part of `hammer` most sensitive to the
meta/non-meta split the module system introduces, so it is worth covering directly. -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by hammer

example (α : Type) (f : α → α) (a : α) (h : ∀ x, f x = x) : f (f a) = a := by hammer

/-! ## The Lean-auto / Zipperposition / Duper pipeline -/

example (α : Type) (f : α → α) (h : ∀ x, f (f x) = x) (a : α) :
    f (f (f (f a))) = a := by
  hammer {disableAesop := true, disableGrind := true, disableSmt := true}

/-- `parallelism := false` takes the sequential `runSingularTactic` path instead of
    `tryAllTacsOnGoal`. -/
example (α : Type) (f : α → α) (h : ∀ x, f (f x) = x) (a : α) :
    f (f (f (f a))) = a := by
  hammer {parallelism := false, disableAesop := true, disableGrind := true, disableSmt := true}

/-! ## The Lean-SMT pipeline -/

example (x y : Int) (h : x < y) : x ≤ y := by
  hammer {disableAesop := true, disableDuper := true, disableGrind := true}

/-! ## User-supplied facts

`hammer`'s user-supplied facts are resolved with `realizeGlobalConstNoOverload`, so they name
global constants rather than local hypotheses. -/

example (a : Nat) (f : Nat → Nat) (h : ∀ x, f (f x) = x) : f (f (f (f a))) = a := by
  hammer [hammerTestInvolutive] {disableAesop := true, disableGrind := true, disableSmt := true}

/-! ## Configuration validation

These messages are part of `hammer`'s observable interface, so they are pinned exactly. -/

/-- error: Erroneous invocation of hammer: The aesop, duper, grind, and smt options cannot all be disabled -/
#guard_msgs in
example : True := by
  hammer {disableAesop := true, disableDuper := true, disableGrind := true, disableSmt := true}

/-- error: Erroneous invocation of hammer: The wallclockTimeout must be greater than or equal to the solverTimeout -/
#guard_msgs in
example : True := by hammer {solverTimeout := 10, wallclockTimeout := 5}

/-- error: Erroneous invocation of hammer: The outputAllSuggestions option can only be enabled when parallelism is enabled -/
#guard_msgs in
example : True := by hammer {parallelism := false, outputAllSuggestions := true}

/-- error: Erroneous invocation of hammer: Preprocessing cannot be set to aesop when aesop is disabled -/
#guard_msgs in
example : True := by hammer {disableAesop := true, preprocessing := aesop}

/-- error: Erroneous invocation of hammer: Preprocessing must be set to aesop when aesop is enabled -/
#guard_msgs in
example : True := by hammer {preprocessing := simp_all}

/-- error: Erroneous invocation of hammer: The solverTimeout option has been specified multiple times -/
#guard_msgs in
example : True := by hammer {solverTimeout := 1, solverTimeout := 2}

/-! ## Registered options and trace classes

`register_option` and `initialize registerTraceClass` are `meta` under the module system, so these
`set_option`s confirm the options and trace classes are still registered for downstream users. -/

section
set_option hammer.solverTimeoutDefault 5
set_option hammer.wallclockTimeoutDefault 30
set_option hammer.preprocessingDefault "aesop"
set_option hammer.disableAesopDefault false
set_option hammer.disableDuperDefault false
set_option hammer.disableGrindDefault false
set_option hammer.disableSmtDefault false
set_option hammer.aesopPremisesDefault 4
set_option hammer.duperPremisesDefault 4
set_option hammer.grindPremisesDefault 4
set_option hammer.smtPremisesDefault 4
set_option hammer.aesopPremisePriorityDefault 20
set_option hammer.aesopDuperPriorityDefault 10
set_option hammer.aesopGrindPriorityDefault 5
set_option hammer.aesopSmtPriorityDefault 10
set_option hammer.parallelismDefault true
set_option hammer.outputAllSuggestionsDefault false
set_option hammer.singleTacticParallel false
set_option auto.getHints.failOnParseError false
set_option trace.hammer.debug false
set_option trace.hammer.premises false
set_option trace.hammer.profiling false

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by hammer
end

/-! ## The public API surface

Every LeanHammer module is `public meta section`, so these names must remain reachable (and
identically typed) through a `public import Hammer` from another `module`. -/

#check @HammerCore.ConfigurationOptions.mk
#check @HammerCore.Preprocessing.aesop
#check @HammerCore.runDuper
#check @HammerCore.smtPipeline
#check @HammerCore.duperSingleRuleTac
#check @HammerCore.grindSingleRuleTac
#check @HammerCore.Smt.smtSingleRuleTac
#check @HammerCore.parseConfigOptions
#check @HammerCore.validateConfigOptions
#check @HammerCore.removeHammerStar
#check @HammerCore.getDuperCoreLemmas
#check @HammerCore.duperNativeSolverFunc
#check @HammerCore.withSolverOptions
#check @HammerCore.withDuperOptions
#check @HammerCore.throwSimpPreprocessingError
#check @HammerCore.errorIsTranslationError
#check @Hammer.Util.tryAllTacsOnGoal
#check @Hammer.Util.proofExprIncomplete
#check @Hammer.Util.inlineFreshProofs
#check @Auto.runAutoGetHints
#check @Auto.buildSelector
#check @Auto.buildSelectorFact

/-! ## Transitive availability of the tactics `hammer` suggests

`hammer` reports its results as `Try this:` suggestions that call `aesop`, `duper`, `smt` and
`grind`. Those suggestions are only usable if `public import Hammer` still transitively provides
the tactics, which is what makes the `public import`s in LeanHammer's modules load-bearing. -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by aesop
example (α : Type) (f : α → α) (h : ∀ x, f x = x) (a : α) : f (f a) = a := by duper [*]
example (x y : Int) (h : x < y) : x ≤ y := by smt +mono [*]
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by grind
