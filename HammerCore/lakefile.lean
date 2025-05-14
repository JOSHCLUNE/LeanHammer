import Lake
open Lake DSL

require «aesop» from git "https://github.com/leanprover-community/aesop" @ "v4.20.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "70363959d03d11205efd94d3e1d73e7b2e2c6695"

package HammerCore {
  precompileModules := true
}

@[default_target]
lean_lib HammerCore
