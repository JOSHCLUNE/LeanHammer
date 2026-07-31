/-
A `module` that imports LeanHammer *privately*.

`HammerTest/ModuleSystem.lean` uses `public import Hammer`, which re-exports LeanHammer to anything
importing it in turn. A downstream `module` that merely uses `hammer` in its own proofs has no
reason to re-export it and will write a plain `import Hammer` instead, so check that form works too.
-/
module

import Hammer

set_option maxHeartbeats 1000000

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by hammer

example (α : Type) (f : α → α) (h : ∀ x, f (f x) = x) (a : α) :
    f (f (f (f a))) = a := by
  hammer {disableAesop := true, disableGrind := true, disableSmt := true}

example (x y : Int) (h : x < y) : x ≤ y := by
  hammer {disableAesop := true, disableDuper := true, disableGrind := true}

/-- error: Erroneous invocation of hammer: The aesop, duper, grind, and smt options cannot all be disabled -/
#guard_msgs in
example : True := by
  hammer {disableAesop := true, disableDuper := true, disableGrind := true, disableSmt := true}

-- The suggested tactics are usable through a private import as well.
example (α : Type) (f : α → α) (h : ∀ x, f x = x) (a : α) : f (f a) = a := by duper [*]
example (x y : Int) (h : x < y) : x ≤ y := by smt +mono [*]
