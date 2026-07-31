/-
Root of LeanHammer's test library; run it with `lake test`.

This file is deliberately *not* a `module`: it has to import `HammerTest.Legacy` (which is not a
`module` either, because it stands in for a downstream user that has not adopted the module system)
alongside the two `module` test files.
-/
import HammerTest.Legacy
import HammerTest.ModuleSystem
import HammerTest.ModuleSystemPrivateImport
