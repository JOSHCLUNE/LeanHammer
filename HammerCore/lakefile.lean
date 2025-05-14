import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "95b69c2315e30ff1c7b459dddde174486d6cc004"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
