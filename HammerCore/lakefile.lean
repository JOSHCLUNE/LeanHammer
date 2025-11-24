import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.25.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "v4.25.0"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
