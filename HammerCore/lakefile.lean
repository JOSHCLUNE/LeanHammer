import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.24.0"

require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "main"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "main"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
