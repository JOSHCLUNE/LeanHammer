import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "4f71a99b24c1b6dc946f258ff94afec41f24ee2d"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
