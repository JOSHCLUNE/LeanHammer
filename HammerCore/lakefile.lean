import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "4bd11f5af780aded58ef038ee05be6b40e6a208f"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
