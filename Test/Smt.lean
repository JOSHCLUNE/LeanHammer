import Hammer
import Smt.Real

set_option hammer.solverTimeoutDefault 20

namespace HammerTests.Smt

/-! ## Pure SMT pipeline

Tests below use `disableAesop := true, disableDuper := true, preprocessing := no_preprocessing`
to exercise just the `Hammer.smtPipeline` (no Aesop wrapping, no Duper, no premise selection traffic).
-/

example : True := by
  hammer [] {disableAesop := true, disableDuper := true, preprocessing := no_preprocessing, smtPremises := 0}

example (h : 1 + 1 = 2) : 1 + 1 = 2 := by
  hammer [h] {disableAesop := true, disableDuper := true, preprocessing := no_preprocessing, smtPremises := 0}

example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  hammer [hpq, hp] {disableAesop := true, disableDuper := true, preprocessing := no_preprocessing, smtPremises := 0}

example (x y : Int) (h : x = y) : x + 1 = y + 1 := by
  hammer [h] {disableAesop := true, disableDuper := true, preprocessing := no_preprocessing, smtPremises := 0}

/-! ## SMT via Aesop integration

`disableDuper := true` keeps SMT as the only solver-backed rule used by Aesop.
`aesopPremises := 0, smtPremises := 0` avoids contacting the premise-selection server.
-/

example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  hammer [hpq, hp] {disableDuper := true, aesopPremises := 0, smtPremises := 0}

/-! ## Configuration validation -/

/-- Disabling all three backends must error. -/
example : True := by
  fail_if_success
    hammer [] {disableAesop := true, disableDuper := true, disableSmt := true, preprocessing := no_preprocessing}
  trivial

end HammerTests.Smt
